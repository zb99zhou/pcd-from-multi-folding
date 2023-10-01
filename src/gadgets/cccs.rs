//! This module implements various gadgets necessary for folding R1CS types.
use super::nonnative::{
    bignat::BigNat,
    util::{f_to_nat, Num},
};
use crate::{
    gadgets::{
        ecc::AllocatedPoint,
        utils::{
            alloc_bignat_constant, alloc_one, alloc_scalar_as_base, conditionally_select,
        },
    },
    traits::{Group, ROCircuitTrait},
};
use bellpepper::gadgets::{boolean::Boolean, num::AllocatedNum, Assignment};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::AllocatedBit;
use ff::Field;
use crate::gadgets::utils::vec_conditionally_select;
use crate::nimfs::ccs::cccs::CCCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::traits::commitment::CommitmentTrait;

/// An Allocated Committed CCS instance
#[derive(Clone)]
pub struct AllocatedCCCS<G: Group> {
    // Commitment to witness
    pub(crate) C: AllocatedPoint<G>,
    pub(crate) Xs: Vec<AllocatedNum<G::Base>>,
}

impl<G: Group> AllocatedCCCS<G> {
    /// Takes the CCCS instance and creates a new allocated CCCS instance
    pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
        mut cs: CS,
        cccs: Option<&CCCS<G>>,
        io_num: usize
    ) -> Result<Self, SynthesisError> {
        // Check that the incoming instance has exactly 2 io
        let C = AllocatedPoint::alloc(
            cs.namespace(|| "allocate C"),
            cccs.get().map_or(None, |u| Some(u.C.to_coordinates())),
        )?;

        let Xs = (0..io_num).map(|i|{
            alloc_scalar_as_base::<G, _>(
                cs.namespace(|| format!("allocate X[{}]", i)),
                cccs.get().map_or(None, |u| Some(u.x[i])),
            )
        }).collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(AllocatedCCCS { C, Xs })
    }

    /// Absorb the provided instance in the RO
    pub fn absorb_in_ro(&self, ro: &mut G::ROCircuit) {
        ro.absorb(&self.C.x);
        ro.absorb(&self.C.y);
        ro.absorb(&self.C.is_infinity);
        for x in self.Xs.iter() {
            ro.absorb(&x);
        }
    }
}

/// An Allocated Linearized Committed CCS instance
#[derive(Clone)]
pub struct AllocatedLCCCS<G: Group> {
    pub C: AllocatedPoint<G>,
    pub u: AllocatedNum<G::Base>,
    pub Xs: Vec<BigNat<G::Base>>,
    pub Vs: Vec<BigNat<G::Base>>,
    pub r_x: Vec<BigNat<G::Base>>,
}

impl<G: Group> AllocatedLCCCS<G> {
    /// Allocates the given `LCCCS` as a witness of the circuit
    pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
        mut cs: CS,
        inst: Option<&LCCCS<G>>,
        io_num: usize,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
        let C = AllocatedPoint::alloc(
            cs.namespace(|| "allocate C"),
            inst
                .get()
                .map_or(None, |inst| Some(inst.C.to_coordinates())),
        )?;

        // u << |G::Base| despite the fact that u is a scalar.
        // So we parse all of its bytes as a G::Base element
        let u = alloc_scalar_as_base::<G, _>(
            cs.namespace(|| "allocate u"),
            inst.get().map_or(None, |inst| Some(inst.u)),
        )?;

        // Allocate X0..Xn. If the input instance is None, then allocate default values 0.
        let Xs = (0..io_num).map(|i|{
            BigNat::alloc_from_nat(
                cs.namespace(|| format!("allocate x[{}]", i)),
                || Ok(f_to_nat(&inst.map_or(G::Scalar::ZERO, |inst| inst.x[i]))),
                limb_width,
                n_limbs,
            )
        }).collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(AllocatedLCCCS { C, u, Xs, r_x: vec![], Vs: vec![] })
    }

    /// Allocates the hardcoded default `RelaxedR1CSInstance` in the circuit.
    /// C = 0, u = 0, X0 = X1 = ... = Xn = 0
    pub fn default<CS: ConstraintSystem<<G as Group>::Base>>(
        mut cs: CS,
        io_num: usize,
        s: usize,
        t: usize,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
        let C = AllocatedPoint::default(cs.namespace(|| "allocate W"))?;

        let u = C.x.clone(); // In the default case, W.x = u = 0

        let Xs = (0..io_num).map(|i|{
            BigNat::alloc_from_nat(
                cs.namespace(|| format!("allocate x[{}]", i)),
                || Ok(f_to_nat(&G::Scalar::ZERO)),
                limb_width,
                n_limbs,
            )
        }).collect::<Result<Vec<_>, SynthesisError>>()?;
        let Vs = (0..t).map(|i|{
            BigNat::alloc_from_nat(
                cs.namespace(|| format!("allocate v[{}]", i)),
                || Ok(f_to_nat(&G::Scalar::ZERO)),
                limb_width,
                n_limbs,
            )
        }).collect::<Result<Vec<_>, SynthesisError>>()?;
        let r_x = (0..s).map(|i|{
            BigNat::alloc_from_nat(
                cs.namespace(|| format!("allocate r_x[{}]", i)),
                || Ok(f_to_nat(&G::Scalar::ZERO)),
                limb_width,
                n_limbs,
            )
        }).collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(AllocatedLCCCS { C, u, Xs, r_x, Vs })
    }

    /// Allocates the CCCS Instance as a LCCCS in the circuit.
    pub fn from_cccs<CS: ConstraintSystem<<G as Group>::Base>>(
        mut cs: CS,
        inst: AllocatedCCCS<G>,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
        let u = alloc_one(cs.namespace(|| "one"))?;

        let Xs = inst.Xs
            .into_iter()
            .enumerate()
            .map(|(i, num)|{
                BigNat::from_num(
                    cs.namespace(|| format!("allocate x[{}]", i)),
                    &Num::from(num),
                    limb_width,
                    n_limbs,
                )
            }).collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(AllocatedLCCCS {
            C: inst.C,
            u,
            Xs,
            r_x: vec![],
            Vs: vec![],
        })
    }

    /// Absorb the provided instance in the RO
    pub fn absorb_in_ro<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        ro: &mut G::ROCircuit,
    ) -> Result<(), SynthesisError> {
        ro.absorb(&self.C.x);
        ro.absorb(&self.C.y);
        ro.absorb(&self.C.is_infinity);
        ro.absorb(&self.u);

        for X in self.Xs.iter() {
            let X_bn = X.as_limbs()
                .iter()
                .enumerate()
                .map(|(i, limb)| {
                    limb.as_allocated_num(cs.namespace(|| format!("convert limb {i} of X_r[0] to num")))
                }).collect::<Result<Vec<_>, SynthesisError>>()?;
            // absorb each of the limbs of Xs
            for limb in X_bn {
                ro.absorb(&limb);
            }
        }

        Ok(())
    }

    /// If the condition is true then returns this otherwise it returns the other
    pub fn conditionally_select<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        other: &AllocatedLCCCS<G>,
        condition: &Boolean,
    ) -> Result<AllocatedLCCCS<G>, SynthesisError> {
        let C = AllocatedPoint::conditionally_select(
            cs.namespace(|| "C = cond ? self.C : other.C"),
            &self.C,
            &other.C,
            condition,
        )?;

        let u = conditionally_select(
            cs.namespace(|| "u = cond ? self.u : other.u"),
            &self.u,
            &other.u,
            condition,
        )?;

        let Xs = vec_conditionally_select(
            cs.namespace(|| "Xs"),
            &self.Xs,
            &other.Xs,
            condition
        )?;

        let r_x = vec_conditionally_select(
            cs.namespace(|| "r_x "),
            &self.r_x,
            &other.r_x,
            condition
        )?;

        let Vs = vec_conditionally_select(
            cs.namespace(|| "Vs"),
            &self.Vs,
            &other.Vs,
            condition
        )?;

        Ok(AllocatedLCCCS { C, u, Xs, r_x, Vs })
    }

    #[allow(clippy::too_many_arguments)]
    pub fn folding_with_lcccs<CS: ConstraintSystem<<G as Group>::Base>>(
        &mut self,
        mut cs: CS,
        lcccs: &AllocatedLCCCS<G>,
        rho_i: &AllocatedNum<G::Base>,
        sigmas: &[BigNat<G::Base>],
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<(), SynthesisError> {
        self.folding(
            cs.namespace(|| " folding with lcccs"),
            &lcccs.C,
            rho_i,
            &lcccs.u,
            &lcccs.Xs,
            &sigmas,
            limb_width,
            n_limbs
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn folding_with_cccs<CS: ConstraintSystem<<G as Group>::Base>>(
        &mut self,
        mut cs: CS,
        cccs: &AllocatedCCCS<G>,
        rho_i: &AllocatedNum<G::Base>,
        thetas: &[BigNat<G::Base>],
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<(), SynthesisError> {
        let one = AllocatedNum::alloc(cs.namespace(|| "alloc"), || Ok(G::Base::ZERO))?;
        let Xs_bn = cccs.Xs
            .iter()
            .enumerate()
            .map(|(i, X)|BigNat::from_num(
                cs.namespace(|| format!("allocate x[{}]", i)),
                &Num::from(X.clone()),
                limb_width,
                n_limbs,
            ))
            .collect::<Result<Vec<_>, SynthesisError>>()?;
        self.folding(
            cs.namespace(|| " folding with cccs"),
            &cccs.C,
            rho_i,
            &one,
            &Xs_bn,
            &thetas,
            limb_width,
            n_limbs
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn folding<CS: ConstraintSystem<<G as Group>::Base>>(
        &mut self,
        mut cs: CS,
        C: &AllocatedPoint<G>,
        rho_i: &AllocatedNum<G::Base>,
        u: &AllocatedNum<G::Base>,
        x: &[BigNat<G::Base>],
        v: &[BigNat<G::Base>],
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<(), SynthesisError> {
        let rho_i_bits = rho_i
            .to_bits_le_strict(cs.namespace(|| "poseidon hash to boolean"))?
            .into_iter()
            .map(|boolean| match boolean {
                Boolean::Is(x) => x,
                _ => panic!("Wrong type of input. We should have never reached there"),
            })
            .collect::<Vec<AllocatedBit>>();

        // C_fold = self.C + r * u.C
        let r_C = C.scalar_mul(cs.namespace(|| "r * u.C"), &rho_i_bits)?;
        let C_fold = self.C.add(cs.namespace(|| "self.C + r * u.C"), &r_C)?;

        // u_fold = self.u + rho_i * u
        let u_fold = AllocatedNum::alloc(
            cs.namespace(|| "u_fold"),
            || Ok(*self.u.get_value().get()? + *rho_i.get_value().get()? * *u.get_value().get()?)
        )?;
        cs.enforce(
            || "Check u_fold",
            |lc| lc + rho_i.get_variable(),
            |lc| lc + u.get_variable(),
            |lc| lc + u_fold.get_variable() - self.u.get_variable(),
        );

        // Fold the IO:
        // Analyze r into limbs
        let rho_i_bn = BigNat::from_num(
            cs.namespace(|| "allocate rho_i_bn"),
            &Num::from(rho_i.clone()),
            limb_width,
            n_limbs,
        )?;

        // Allocate the order of the non-native field as a constant
        let m_bn = alloc_bignat_constant(
            cs.namespace(|| "alloc m"),
            &G::get_curve_params().2,
            limb_width,
            n_limbs,
        )?;

        let mut Xs_folded = Vec::new();
        for (i, (X_folded, X_bn)) in self.Xs.iter().zip(x.iter()).enumerate() {
            let mut cs = cs.namespace(|| format!("folding {}th x", i));
            // Fold lcccs.X + r * lccc.X
            let (_, r_0) = X_bn.mult_mod(cs.namespace(|| "r*X"), &rho_i_bn, &m_bn)?;
            let r_new_0 = X_folded.add(&r_0)?;
            Xs_folded.push(r_new_0.red_mod(cs.namespace(|| "reduce folded X"), &m_bn)?);
        }

        let mut vs_folded = Vec::new();
        for (i, (v_folded, V_bn)) in self.Vs.iter().zip(v.iter()).enumerate() {
            let mut cs = cs.namespace(|| format!("folding {}th v", i));
            // Fold lcccs.v + r * lccc.v
            let (_, r_0) = V_bn.mult_mod(cs.namespace(|| "r*v"), &rho_i_bn, &m_bn)?;
            let r_new_0 = v_folded.add(&r_0)?;
            vs_folded.push(r_new_0.red_mod(cs.namespace(|| "reduce folded v"), &m_bn)?);
        }

        self.C = C_fold;
        self.u = u_fold;
        self.Xs = Xs_folded;
        self.Vs = vs_folded;
        self.r_x = vec![];

        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
pub fn multi_folding<CS: ConstraintSystem<<G as Group>::Base>, G: Group>(
    mut cs: CS,
    lcccs: &[AllocatedLCCCS<G>],
    cccs: &[AllocatedCCCS<G>],
    rho: AllocatedNum<G::Base>,
    sigmas: &[Vec<BigNat<G::Base>>],
    thetas: &[Vec<BigNat<G::Base>>],
    limb_width: usize,
    n_limbs: usize,
) -> Result<AllocatedLCCCS<G>, SynthesisError> {
    // init
    let mut lcccs_folded = lcccs[0].clone();
    lcccs_folded.Vs = sigmas[0].to_owned();
    let mut rho_i = rho.clone();

    // folding
    for (i, lcccs) in lcccs.iter().enumerate().skip(1) {
        rho_i = rho_i.square(cs.namespace(|| format!("alloc {}th squared rho_i in folding lcccs", i)))?;
        lcccs_folded.folding_with_lcccs(
            cs.namespace(|| format!("folding {}th lcccs", i)),
            lcccs,
            &rho_i,
            &sigmas[i],
            limb_width,
            n_limbs
        )?;
    }
    for (i, cccs) in cccs.iter().enumerate() {
        rho_i = rho_i.square(cs.namespace(|| format!("alloc {}th squared rho_i in folding cccs", i)))?;
        lcccs_folded.folding_with_cccs(
            cs.namespace(|| format!("folding {}th cccs", i)),
            cccs,
            &rho_i,
            &thetas[i],
            limb_width,
            n_limbs
        )?;
    }
    Ok(lcccs_folded)
}