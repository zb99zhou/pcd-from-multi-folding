//! This module implements various gadgets necessary for folding R1CS types.
use super::nonnative::{
    bignat::BigNat,
    util::{f_to_nat, Num},
};
use crate::{
    gadgets::{
        scalar_ecc::AllocatedPoint,
        utils::{
            alloc_bignat_constant, alloc_one, conditionally_select,
        },
    },
    traits::Group,
};
use bellpepper::gadgets::{boolean::Boolean, num::AllocatedNum, Assignment};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::AllocatedBit;
use ff::Field;
use crate::gadgets::ext_allocated_num::ExtendFunc;
use crate::gadgets::utils::{alloc_num_equals, alloc_vec_num_equals_zero, alloc_vec_number_equals_zero, conditionally_select_vec_allocated_num, multi_and, vec_conditionally_select_big_nat};
use crate::nimfs::ccs::cccs::CCCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::ROCircuitTrait;

/// An Allocated Committed CCS instance
#[derive(Clone)]
pub struct AllocatedCCCSPrimaryPart<G: Group> {
    pub(crate) Xs: Vec<AllocatedNum<G::Scalar>>,
}

impl<G: Group> AllocatedCCCSPrimaryPart<G> {
    pub fn is_null<CS: ConstraintSystem<G::Scalar>>(&self, mut cs: CS, zero: &AllocatedNum<G::Scalar>) -> Result<Boolean, SynthesisError> {
        alloc_vec_number_equals_zero(cs.namespace(|| "is Xs zero"), &self.Xs, &zero).map(Into::into)
    }

    /// Takes the CCCS instance and creates a new allocated CCCS instance
    pub fn alloc<CS: ConstraintSystem<<G as Group>::Scalar>>(
        mut cs: CS,
        cccs: Option<&CCCS<G>>,
        io_num: usize
    ) -> Result<Self, SynthesisError> {
        let Xs = (0..io_num).map(|i|{
            AllocatedNum::alloc(
                cs.namespace(|| format!("allocate X[{}]", i)),
                || Ok(cccs.get().map_or(G::Scalar::ZERO, |u| u.x[i])),
            )
        }).collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(AllocatedCCCSPrimaryPart { Xs })
    }
}

#[derive(Clone)]
pub struct AllocatedCCCSSecondPart<G: Group> {
    // Commitment to witness
    pub(crate) C: AllocatedPoint<G>,
}

impl<G: Group> AllocatedCCCSSecondPart<G> {
    /// Takes the CCCS instance and creates a new allocated CCCS instance
    pub fn alloc<CS: ConstraintSystem<<G as Group>::Scalar>>(
        mut cs: CS,
        cccs: Option<&CCCS<G>>,
    ) -> Result<Self, SynthesisError> {
        // Check that the incoming instance has exactly 2 io
        let C = AllocatedPoint::alloc(
            cs.namespace(|| "allocate C"),
            cccs.get().map_or(None, |u| Some(u.C.to_coordinates())),
        )?;

        Ok(AllocatedCCCSSecondPart { C })
    }

    pub fn absorb_in_ro<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &self,
        ro: &mut G::ROCircuit,
    ) -> Result<(), SynthesisError> {
        ro.absorb(&self.C.is_infinity);
        ro.absorb(&self.C.x);
        ro.absorb(&self.C.y);

        Ok(())
    }
}


/// An Allocated Linearized Committed CCS instance
#[derive(Clone)]
pub struct AllocatedLCCCSPrimaryPart<G: Group> {
    pub u: AllocatedNum<G::Scalar>,
    pub Xs: Vec<BigNat<G::Scalar>>,
    pub Vs: Vec<AllocatedNum<G::Scalar>>,
    pub r_x: Vec<AllocatedNum<G::Scalar>>,
}

impl<G: Group> AllocatedLCCCSPrimaryPart<G> {
    pub fn is_null<CS: ConstraintSystem<G::Scalar>>(&self, mut cs: CS, zero: &AllocatedNum<G::Scalar>) -> Result<Boolean, SynthesisError> {
        let mut is_u_zero = alloc_num_equals(cs.namespace(|| "alloc is_null"), &self.u, zero)?.into();

        let Xs_num = self.Xs.iter().flat_map(|x| x.as_limbs()).collect::<Vec<_>>();
        let is_Xs_zero = alloc_vec_num_equals_zero(cs.namespace(|| "is Xs zero"), &Xs_num)?.into();
        let is_Vs_zero = alloc_vec_number_equals_zero(cs.namespace(|| "is Vs zero"), &self.Vs, &zero)?.into();
        let is_r_x_zero = alloc_vec_number_equals_zero(cs.namespace(|| "is r_x zero"), &self.r_x, &zero)?.into();

        multi_and(cs.namespace(|| "final result"), &[is_u_zero, is_Xs_zero, is_Vs_zero, is_r_x_zero]).map(Into::into)
    }

    /// Allocates the given `LCCCS` as a witness of the circuit
    pub fn alloc<CS: ConstraintSystem<<G as Group>::Scalar>>(
        mut cs: CS,
        inst: Option<&LCCCS<G>>,
        io_num: usize,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
        // u << |G::Scalar| despite the fact that u is a scalar.
        // So we parse all of its bytes as a G::Scalar element
        let u = AllocatedNum::alloc(
            cs.namespace(|| "allocate u"),
            || Ok(inst.get().map_or(G::Scalar::ZERO, |inst| inst.u)),
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

        Ok(AllocatedLCCCSPrimaryPart { u, Xs, r_x: vec![], Vs: vec![] })
    }

    /// Allocates the hardcoded default `RelaxedR1CSInstance` in the circuit.
    /// C = 0, u = 0, X0 = X1 = ... = Xn = 0
    pub fn default<CS: ConstraintSystem<<G as Group>::Scalar>>(
        mut cs: CS,
        io_num: usize,
        s: usize,
        t: usize,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
        // let u = C.x.clone(); // In the default case, W.x = u = 0
        let u = AllocatedNum::zero(cs.namespace(|| "alloc zero`"))?;

        let Xs = (0..io_num).map(|i|{
            BigNat::alloc_from_nat(
                cs.namespace(|| format!("allocate x[{}]", i)),
                || Ok(f_to_nat(&G::Scalar::ZERO)),
                limb_width,
                n_limbs,
            )
        }).collect::<Result<Vec<_>, SynthesisError>>()?;
        let Vs = (0..t).map(|i|{
            AllocatedNum::alloc(
                cs.namespace(|| format!("allocate v[{}]", i)),
                || Ok(G::Scalar::ZERO),
            )
        }).collect::<Result<Vec<_>, SynthesisError>>()?;
        let r_x = (0..s).map(|i|{
            AllocatedNum::alloc(
                cs.namespace(|| format!("allocate v[{}]", i)),
                || Ok(G::Scalar::ZERO),
            )
        }).collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(AllocatedLCCCSPrimaryPart { u, Xs, r_x, Vs })
    }

    /// Allocates the CCCS Instance as a LCCCS in the circuit.
    pub fn from_cccs<CS: ConstraintSystem<<G as Group>::Scalar>>(
        mut cs: CS,
        inst: AllocatedCCCSPrimaryPart<G>,
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

        Ok(AllocatedLCCCSPrimaryPart {
            u,
            Xs,
            r_x: vec![],
            Vs: vec![],
        })
    }

    /// Absorb the provided instance in the RO
    pub fn absorb_in_ro<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &self,
        mut cs: CS,
        ro: &mut G::ROCircuit,
    ) -> Result<(), SynthesisError> {
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

        for v in self.Vs.iter() {
            ro.absorb(v);
        }

        for r in self.r_x.iter() {
            ro.absorb(r);
        }

        Ok(())
    }

    /// If the condition is true then returns this otherwise it returns the other
    pub fn conditionally_select<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &self,
        mut cs: CS,
        other: &AllocatedLCCCSPrimaryPart<G>,
        condition: &Boolean,
    ) -> Result<AllocatedLCCCSPrimaryPart<G>, SynthesisError> {
        let u = conditionally_select(
            cs.namespace(|| "u = cond ? self.u : other.u"),
            &self.u,
            &other.u,
            condition,
        )?;

        let Xs = vec_conditionally_select_big_nat(
            cs.namespace(|| "Xs"),
            &self.Xs,
            &other.Xs,
            condition
        )?;

        let r_x = conditionally_select_vec_allocated_num(
            cs.namespace(|| "r_x "),
            &self.r_x,
            &other.r_x,
            condition
        )?;

        let Vs = conditionally_select_vec_allocated_num(
            cs.namespace(|| "Vs"),
            &self.Vs,
            &other.Vs,
            condition
        )?;

        Ok(AllocatedLCCCSPrimaryPart { u, Xs, r_x, Vs })
    }

    #[allow(clippy::too_many_arguments)]
    pub fn folding_with_lcccs_primary_part<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &mut self,
        mut cs: CS,
        lcccs: &AllocatedLCCCSPrimaryPart<G>,
        rho_i: &AllocatedNum<G::Scalar>,
        sigmas: &[AllocatedNum<G::Scalar>],
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<(), SynthesisError> {
        self.folding(
            cs.namespace(|| " folding with lcccs"),
            rho_i,
            &lcccs.u,
            &lcccs.Xs,
            &sigmas,
            limb_width,
            n_limbs
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn folding_with_cccs_primary_part<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &mut self,
        mut cs: CS,
        cccs: &AllocatedCCCSPrimaryPart<G>,
        rho_i: &AllocatedNum<G::Scalar>,
        thetas: &[AllocatedNum<G::Scalar>],
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<(), SynthesisError> {
        let one = AllocatedNum::alloc(cs.namespace(|| "alloc"), || Ok(G::Scalar::ZERO))?;
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
            rho_i,
            &one,
            &Xs_bn,
            &thetas,
            limb_width,
            n_limbs
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn folding<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &mut self,
        mut cs: CS,
        rho_i: &AllocatedNum<G::Scalar>,
        u: &AllocatedNum<G::Scalar>,
        x: &[BigNat<G::Scalar>],
        v: &[AllocatedNum<G::Scalar>],
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<(), SynthesisError> {
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
        for (i, (v_folded, v)) in self.Vs.iter().zip(v.iter()).enumerate() {
            let mut cs = cs.namespace(|| format!("folding {}th v", i));
            // Fold lcccs.v + r * lccc.v
            let r_0 = v.mul(cs.namespace(|| "r * v"), rho_i)?;
            let r_new_0 = v_folded.add(cs.namespace(|| "v_folded + r * v"), &r_0)?;
            vs_folded.push(r_new_0);
        }

        self.u = u_fold;
        self.Xs = Xs_folded;
        self.Vs = vs_folded;
        self.r_x = vec![];

        Ok(())
    }
}

#[derive(Clone)]
pub struct AllocatedLCCCSSecondPart<G: Group> {
    pub C: AllocatedPoint<G>,
}

impl<G: Group> AllocatedLCCCSSecondPart<G> {
    /// Allocates the given `LCCCS` as a witness of the circuit
    pub fn alloc<CS: ConstraintSystem<<G as Group>::Scalar>>(
        mut cs: CS,
        inst: Option<&LCCCS<G>>,
    ) -> Result<Self, SynthesisError> {
        let C = AllocatedPoint::alloc(
            cs.namespace(|| "allocate C"),
            inst
                .get()
                .map_or(None, |inst| Some(inst.C.to_coordinates())),
        )?;
        Ok(AllocatedLCCCSSecondPart { C })
    }

    /// Allocates the hardcoded default `LCCCS` in the circuit.
    /// C = 0, u = 0, X0 = X1 = ... = Xn = 0
    pub fn default<CS: ConstraintSystem<<G as Group>::Scalar>>(
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        let C = AllocatedPoint::default(cs.namespace(|| "allocate W"))?;
        Ok(AllocatedLCCCSSecondPart { C })
    }

    /// Allocates the CCCS Instance as a LCCCS in the circuit.
    pub fn from_cccs<CS: ConstraintSystem<<G as Group>::Scalar>>(inst: AllocatedCCCSSecondPart<G>) -> Result<Self, SynthesisError> {
        Ok(AllocatedLCCCSSecondPart { C: inst.C })
    }

    /// If the condition is true then returns this otherwise it returns the other
    pub fn conditionally_select<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &self,
        mut cs: CS,
        other: &AllocatedLCCCSSecondPart<G>,
        condition: &Boolean,
    ) -> Result<AllocatedLCCCSSecondPart<G>, SynthesisError> {
        let C = AllocatedPoint::conditionally_select(
            cs.namespace(|| "C = cond ? self.C : other.C"),
            &self.C,
            &other.C,
            condition,
        )?;
        Ok(AllocatedLCCCSSecondPart { C })
    }

    #[allow(clippy::too_many_arguments)]
    pub fn folding_with_lcccs_second_part<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &mut self,
        mut cs: CS,
        lcccs: &AllocatedLCCCSSecondPart<G>,
        rho_i: &AllocatedNum<G::Scalar>,
    ) -> Result<(), SynthesisError> {
        self.folding(
            cs.namespace(|| " folding with lcccs"),
            &lcccs.C,
            rho_i,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn folding_with_cccs_second_part<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &mut self,
        mut cs: CS,
        cccs: &AllocatedCCCSSecondPart<G>,
        rho_i: &AllocatedNum<G::Scalar>,
    ) -> Result<(), SynthesisError> {
        self.folding(
            cs.namespace(|| " folding with cccs"),
            &cccs.C,
            rho_i,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn folding<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &mut self,
        mut cs: CS,
        C: &AllocatedPoint<G>,
        rho_i: &AllocatedNum<G::Scalar>,
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

        self.C = C_fold;

        Ok(())
    }

    pub fn absorb_in_ro<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &self,
        ro: &mut G::ROCircuit,
    ) -> Result<(), SynthesisError> {
        ro.absorb(&self.C.is_infinity);
        ro.absorb(&self.C.x);
        ro.absorb(&self.C.y);

        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
pub fn multi_folding_with_primary_part<CS: ConstraintSystem<<G as Group>::Scalar>, G: Group>(
    mut cs: CS,
    lcccs: &[AllocatedLCCCSPrimaryPart<G>],
    cccs: &[AllocatedCCCSPrimaryPart<G>],
    rho: AllocatedNum<G::Scalar>,
    sigmas: &[Vec<AllocatedNum<G::Scalar>>],
    thetas: &[Vec<AllocatedNum<G::Scalar>>],
    limb_width: usize,
    n_limbs: usize,
) -> Result<AllocatedLCCCSPrimaryPart<G>, SynthesisError> {
    // init
    let mut lcccs_folded = lcccs[0].clone();
    lcccs_folded.Vs = sigmas[0].to_owned();
    let mut rho_i = rho.clone();

    // folding
    for (i, lcccs) in lcccs.iter().enumerate().skip(1) {
        rho_i = rho_i.square(cs.namespace(|| format!("alloc {}th squared rho_i in folding lcccs", i)))?;
        lcccs_folded.folding_with_lcccs_primary_part(
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
        lcccs_folded.folding_with_cccs_primary_part(
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

#[allow(clippy::too_many_arguments)]
pub fn multi_folding_with_second_part<CS: ConstraintSystem<<G as Group>::Scalar>, G: Group>(
    mut cs: CS,
    lcccs: &[AllocatedLCCCSSecondPart<G>],
    cccs: &[AllocatedCCCSSecondPart<G>],
    rho: AllocatedNum<G::Scalar>,
) -> Result<AllocatedLCCCSSecondPart<G>, SynthesisError> {
    // init
    let mut lcccs_folded = lcccs[0].clone();
    let mut rho_i = rho.clone();

    // folding
    for (i, lcccs) in lcccs.iter().enumerate().skip(1) {
        rho_i = rho_i.square(cs.namespace(|| format!("alloc {}th squared rho_i in folding lcccs", i)))?;
        lcccs_folded.folding_with_lcccs_second_part(
            cs.namespace(|| format!("folding {}th lcccs", i)),
            lcccs,
            &rho_i,
        )?;
    }
    for (i, cccs) in cccs.iter().enumerate() {
        rho_i = rho_i.square(cs.namespace(|| format!("alloc {}th squared rho_i in folding cccs", i)))?;
        lcccs_folded.folding_with_cccs_second_part(
            cs.namespace(|| format!("folding {}th cccs", i)),
            cccs,
            &rho_i,
        )?;
    }
    Ok(lcccs_folded)
}