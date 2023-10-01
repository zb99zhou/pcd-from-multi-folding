use bellpepper::gadgets::Assignment;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use ff::Field;
use crate::constants::{NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use crate::gadgets::cccs::{AllocatedCCCS, AllocatedLCCCS};
use crate::gadgets::utils::{alloc_num_equals, alloc_scalar_as_base, alloc_zero, conditionally_select_vec, le_bits_to_num};
// use serde::{Deserialize, Serialize};
use crate::nimfs::ccs::cccs::CCCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::traits::{Group, ROCircuitTrait, ROConstantsCircuit};
use crate::traits::circuit::StepCircuit;

pub struct PCDUnitParams{
    pub(crate) mu: usize,
    pub(crate) nu: usize,
    pub(crate) io_num: usize,
    pub(crate) s: usize,
    pub(crate) t: usize,
    pub(crate) limb_width: usize,
    pub(crate) n_limbs: usize,
    pub(crate) is_primary_circuit: bool, // A boolean indicating if this is the primary circuit
}

impl PCDUnitParams {
    pub const fn new(
        limb_width: usize,
        n_limbs: usize,
        is_primary_circuit: bool,
        mu: usize,
        nu: usize,
        io_num: usize,
        s: usize,
        t: usize,
    ) -> Self {
        Self {
            mu,
            nu,
            io_num,
            s,
            t,
            limb_width,
            n_limbs,
            is_primary_circuit,
        }
    }
}

// #[derive(Debug, Serialize, Deserialize)]
// #[serde(bound = "")]
pub struct PCDUnitInputs<G: Group> {
    params: G::Scalar, // Hash(Shape of u2, Gens for u2). Needed for computing the challenge.
    // i: G::Base,
    z0: Vec<G::Base>,
    zi: Option<Vec<G::Base>>,
    lcccs: Option<Vec<LCCCS<G>>>,
    cccs: Option<Vec<CCCS<G>>>,
    // T: Option<Commitment<G>>,
}

impl<G: Group> PCDUnitInputs<G> {
    /// Create new inputs/witness for the verification circuit
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        params: G::Scalar,
        z0: Vec<G::Base>,
        zi: Option<Vec<G::Base>>,
        lcccs: Option<Vec<LCCCS<G>>>,
        cccs: Option<Vec<CCCS<G>>>,
    ) -> Self {
        Self {
            params,
            z0,
            zi,
            lcccs,
            cccs,
        }
    }
}

pub struct PCDUnitCircuit<'a, G: Group, SC: StepCircuit<G::Base>> {
    params: &'a PCDUnitParams,
    ro_consts: ROConstantsCircuit<G>,
    inputs: Option<PCDUnitInputs<G>>,
    step_circuit: &'a SC, // The function that is applied for each step
}

impl<'a, G: Group, SC: StepCircuit<G::Base>> PCDUnitCircuit<'a, G, SC> {
    /// Create a new verification circuit for the input relaxed r1cs instances
    pub const fn new(
        params: &'a PCDUnitParams,
        inputs: Option<PCDUnitInputs<G>>,
        step_circuit: &'a SC,
        ro_consts: ROConstantsCircuit<G>,
    ) -> Self {
        Self {
            params,
            inputs,
            step_circuit,
            ro_consts,
        }
    }

    /// Allocate all witnesses and return
    fn alloc_witness<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        arity: usize,
    ) -> Result<
        (
            AllocatedNum<G::Base>,
            Vec<AllocatedNum<G::Base>>,
            Vec<AllocatedNum<G::Base>>,
            Vec<AllocatedLCCCS<G>>,
            Vec<AllocatedCCCS<G>>,
        ),
        SynthesisError,
    > {
        // Allocate the params
        let params = alloc_scalar_as_base::<G, _>(
            cs.namespace(|| "params"),
            self.inputs.get().map_or(None, |inputs| Some(inputs.params)),
        )?;

        // Allocate i
        // let i = AllocatedNum::alloc(cs.namespace(|| "i"), || Ok(self.inputs.get()?.i))?;

        // Allocate z0
        let z_0 = (0..arity)
            .map(|i| {
                AllocatedNum::alloc(cs.namespace(|| format!("z0_{i}")), || {
                    Ok(self.inputs.get()?.z0[i])
                })
            })
            .collect::<Result<Vec<AllocatedNum<G::Base>>, _>>()?;

        // Allocate zi. If inputs.zi is not provided (base case) allocate default value 0
        let zero = vec![G::Base::ZERO; arity];
        let z_i = (0..arity)
            .map(|i| {
                AllocatedNum::alloc(cs.namespace(|| format!("zi_{i}")), || {
                    Ok(self.inputs.get()?.zi.as_ref().unwrap_or(&zero)[i])
                })
            })
            .collect::<Result<Vec<AllocatedNum<G::Base>>, _>>()?;

        // Allocate the running instance
        let lcccs: AllocatedLCCCS<G> = AllocatedLCCCS::alloc(
            cs.namespace(|| "Allocate lcccs"),
            self.inputs.get().as_ref().map_or(None, |inputs| {
                inputs.lcccs.get().as_ref().map_or(None, |U| Some(&U[0])) // TODO: deal multi lcccs
            }),
            self.params.io_num,
            self.params.limb_width,
            self.params.n_limbs,
        )?;

        // Allocate the instance to be folded in
        let cccs = AllocatedCCCS::alloc(
            cs.namespace(|| "allocate instance cccs to fold"),
            self.inputs.get().as_ref().map_or(None, |inputs| {
                inputs.cccs.get().as_ref().map_or(None, |u| Some(&u[0])) // TODO: deal multi lcccs
            }),
            self.params.io_num,
        )?;


        Ok((params, z_0, z_i, vec![lcccs], vec![cccs]))
    }

    /// Synthesizes base case and returns the new relaxed `R1CSInstance`
    fn synthesize_base_case<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        cccs: Vec<AllocatedCCCS<G>>,
    ) -> Result<AllocatedLCCCS<G>, SynthesisError> {
        let lcccs_default = if self.params.is_primary_circuit {
            // The primary circuit just returns the default R1CS instance
            AllocatedLCCCS::default(
                cs.namespace(|| "Allocate lcccs default"),
                self.params.io_num,
                self.params.s,
                self.params.t,
                self.params.limb_width,
                self.params.n_limbs,
            )?
        } else {
            // The secondary circuit returns the incoming LCCCS instance
            AllocatedLCCCS::from_cccs(
                cs.namespace(|| "Allocate lcccs default"),
                cccs[0].clone(),
                self.params.limb_width,
                self.params.n_limbs,
            )?
        };
        Ok(lcccs_default)
    }

    /// Synthesizes non base case and returns the new relaxed `R1CSInstance`
    /// And a boolean indicating if all checks pass
    #[allow(clippy::too_many_arguments)]
    fn synthesize_non_base_case<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        _cs: CS,
        _params: &AllocatedNum<G::Base>,
        _z_0: &[AllocatedNum<G::Base>],
        _z_i: &[AllocatedNum<G::Base>],
        _lcccs: Vec<AllocatedLCCCS<G>>,
        _cccs: Vec<AllocatedCCCS<G>>,
        _arity: usize,
    ) -> Result<(AllocatedLCCCS<G>, AllocatedBit), SynthesisError> {
        // // Check that u.x[0] = Hash(params, U, i, z0, zi)
        // let mut ro = G::ROCircuit::new(
        //     self.ro_consts.clone(),
        //     NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * arity,
        // );
        // ro.absorb(params);
        // for e in z_0 {
        //     ro.absorb(e);
        // }
        // for e in z_i {
        //     ro.absorb(e);
        // }
        // lcccs.absorb_in_ro(cs.namespace(|| "absorb U"), &mut ro)?;
        //
        // let hash_bits = ro.squeeze(cs.namespace(|| "Input hash"), NUM_HASH_BITS)?;
        // let hash = le_bits_to_num(cs.namespace(|| "bits to hash"), &hash_bits)?;
        // let check_pass = alloc_num_equals(
        //     cs.namespace(|| "check consistency of u.X[0] with H(params, U, i, z0, zi)"),
        //     &cccs.Xs,
        //     &hash,
        // )?;
        //
        // // Run NIMFS Verifier
        // let new_lcccs = multi_folding(
        //     cs.namespace(|| "compute fold of U and u"),
        //     lcccs,
        //     cccs,
        //     self.params.limb_width,
        //     self.params.n_limbs,
        // )?;
        //
        // Ok((new_lcccs, check_pass))
        unimplemented!()
    }
}


impl<'a, G: Group, SC: StepCircuit<G::Base>> PCDUnitCircuit<'a, G, SC> {
    /// synthesize circuit giving constraint system
    pub fn synthesize<CS: ConstraintSystem<<G as Group>::Base>>(
        self,
        cs: &mut CS,
    ) -> Result<Vec<AllocatedNum<G::Base>>, SynthesisError> {
        let arity = self.step_circuit.arity();

        // Allocate all witnesses
        let (
            params, z_0, z_i,
            lcccs, cccs,
        ) = self.alloc_witness(cs.namespace(|| "allocate the circuit witness"), arity)?;
        let Xs = cccs.iter().flat_map(|c|c.Xs.to_vec()).collect::<Vec<_>>();

        // Compute variable indicating if this is the base case
        let zero = alloc_zero(cs.namespace(|| "zero"))?;
        let is_base_case = alloc_num_equals(cs.namespace(|| "Check if base case"), &cccs[0].C.is_infinity, &zero)?;

        // Synthesize the circuit for the base case and get the new running instance
        let Unew_base = self.synthesize_base_case(cs.namespace(|| "base case"), cccs.clone())?;

        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let (Unew_non_base, check_non_base_pass) = self.synthesize_non_base_case(
            cs.namespace(|| "synthesize non base case"),
            &params,
            &z_0,
            &z_i,
            lcccs,
            cccs,
            arity,
        )?;

        // Either check_non_base_pass=true or we are in the base case
        let should_be_false = AllocatedBit::nor(
            cs.namespace(|| "check_non_base_pass nor base_case"),
            &check_non_base_pass,
            &is_base_case,
        )?;
        cs.enforce(
            || "check_non_base_pass nor base_case = false",
            |lc| lc + should_be_false.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        // Compute the U_new
        let Unew = Unew_base.conditionally_select(
            cs.namespace(|| "compute U_new"),
            &Unew_non_base,
            &Boolean::from(is_base_case.clone()),
        )?;

        // Compute z_{i+1}
        let z_input = conditionally_select_vec(
            cs.namespace(|| "select input to F"),
            &z_0,
            &z_i,
            &Boolean::from(is_base_case),
        )?;

        let z_next = self
            .step_circuit
            .synthesize(&mut cs.namespace(|| "F"), &z_input)?;

        if z_next.len() != arity {
            return Err(SynthesisError::IncompatibleLengthVector(
                "z_next".to_string(),
            ));
        }

        // Compute the new hash H(params, Unew, i+1, z0, z_{i+1})
        let mut ro = G::ROCircuit::new(self.ro_consts, NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * arity);
        ro.absorb(&params);
        for e in &z_0 {
            ro.absorb(e);
        }
        for e in &z_next {
            ro.absorb(e);
        }
        Unew.absorb_in_ro(cs.namespace(|| "absorb U_new"), &mut ro)?;
        let hash_bits = ro.squeeze(cs.namespace(|| "output hash bits"), NUM_HASH_BITS)?;
        let hash = le_bits_to_num(cs.namespace(|| "convert hash to num"), &hash_bits)?;

        // Outputs the computed hash and u.X[1] that corresponds to the hash of the other circuit
        for X in Xs.into_iter() {
            X.inputize(cs.namespace(|| "Output unmodified hash of the other circuit"))?; // this circuit's Xs
        }
        hash.inputize(cs.namespace(|| "output new hash of this circuit"))?; // this circuit's x1

        Ok(z_next)
    }
}