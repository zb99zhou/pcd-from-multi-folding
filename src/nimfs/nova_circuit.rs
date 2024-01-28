use bellpepper::gadgets::Assignment;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use crate::gadgets::cccs::{AllocatedCCCSSecondPart, AllocatedLCCCSSecondPart};
use crate::nimfs::ccs::cccs::CCCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::traits::{Group, ROConstantsCircuit, TEConstantsCircuit, TranscriptCircuitEngineTrait};

pub struct NovaAuxiliaryInputs<G: Group> {
    params: G::Scalar, // Hash(Shape of u2, Gens for u2). Needed for computing the challenge.
    // i: G::Scalar,
    z0: Vec<G::Scalar>,
    zi: Option<Vec<G::Scalar>>,
    lcccs: Option<Vec<LCCCS<G>>>,
    cccs: Option<Vec<CCCS<G>>>,
    r: usize
}

struct NovaAuxiliarySecondCircuit<G: Group> {
    ro_consts: ROConstantsCircuit<G>,
    te_consts: TEConstantsCircuit<G>,
    inputs: NovaAuxiliaryInputs<G>,
}

impl<G: Group> NovaAuxiliarySecondCircuit<G> {
    /// Allocate all witnesses and return
    fn alloc_witness<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &self,
        mut cs: CS,
    ) -> Result<
        (
            Vec<AllocatedLCCCSSecondPart<G>>,
            Vec<AllocatedCCCSSecondPart<G>>,
        ),
        SynthesisError,
    > {
        // Allocate the running instance
        let lcccs = (0..self.inputs.r)
            .map(|i |AllocatedLCCCSSecondPart::alloc(
                cs.namespace(|| format!("Allocate {i}th lcccs")),
                self.inputs.lcccs.get().as_ref().map_or(None, |U| Some(&U[i]))
            )?)
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        // Allocate the instance to be folded in
        let cccs = (0..self.inputs.r)
            .map(|i |AllocatedCCCSSecondPart::alloc(
                cs.namespace(|| format!("Allocate {i}th lcccs")),
                self.inputs.cccs.get().as_ref().map_or(None, |U| Some(&U[i]))
            )?)
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok((lcccs, cccs))
    }
}

impl<G: Group> NovaAuxiliarySecondCircuit<G> {
    /// synthesize circuit giving constraint system
    pub fn synthesize<CS: ConstraintSystem<<G as Group>::Scalar>>(
        self,
        cs: &mut CS,
    ) -> Result<Vec<AllocatedNum<G::Scalar>>, SynthesisError> {
        // Allocate all witnesses
        let (lcccs, cccs)
            = self.alloc_witness(cs.namespace(|| "allocate the circuit witness"))?;

        let new_lcccs = crate::gadgets::cccs::multi_folding_with_second_part(
            cs.namespace(|| "calc new lcccs"),
            &lcccs,
            &cccs,
            rho
        )?;

        // Compute the new hash H(params, Unew, i+1, z0, z_{i+1})
        let mut ro = G::TECircuit::new(
            self.te_consts,
            cs.namespace(|| "init transcript engine"),
            b"init transcript engine"
        );
        // ro.absorb(&params);
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