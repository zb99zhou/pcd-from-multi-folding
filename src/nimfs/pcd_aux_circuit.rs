use bellpepper::gadgets::Assignment;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::num::AllocatedNum;
use crate::constants::NUM_HASH_BITS;
use crate::gadgets::cccs::{AllocatedCCCSSecondPart, AllocatedLCCCSSecondPart};
use crate::gadgets::utils::le_bits_to_num;
use crate::nimfs::ccs::cccs::CCCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::traits::{Group, ROCircuitTrait, ROConstantsCircuit, TEConstantsCircuit};

pub struct NovaAuxiliaryInputs<G: Group> {
    params: G::Base, // Hash(Shape of u2, Gens for u2). Needed for computing the challenge.
    // i: G::Base,
    z0: Vec<G::Base>,
    zi: Option<Vec<G::Base>>,
    lcccs: Option<Vec<LCCCS<G>>>,
    cccs: Option<Vec<CCCS<G>>>,
    rho: Option<G::Base>,
    r: usize
}

struct NovaAuxiliarySecondCircuit<G: Group> {
    ro_consts: ROConstantsCircuit<G>,
    te_consts: TEConstantsCircuit<G>,
    inputs: NovaAuxiliaryInputs<G>,
}

impl<G: Group> NovaAuxiliarySecondCircuit<G> {
    /// Allocate all witnesses and return
    fn alloc_witness<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
    ) -> Result<
        (
            Vec<AllocatedLCCCSSecondPart<G>>,
            Vec<AllocatedCCCSSecondPart<G>>,
            AllocatedNum<G::Base>
        ),
        SynthesisError,
    > {
        // Allocate the running instance
        let lcccs = (0..self.inputs.r)
            .map(|i |AllocatedLCCCSSecondPart::alloc(
                cs.namespace(|| format!("Allocate {i}th lcccs")),
                self.inputs.lcccs.get().as_ref().map_or(None, |U| Some(&U[i]))
            ))
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        // Allocate the instance to be folded in
        let cccs = (0..self.inputs.r)
            .map(|i |AllocatedCCCSSecondPart::alloc(
                cs.namespace(|| format!("Allocate {i}th lcccs")),
                self.inputs.cccs.get().as_ref().map_or(None, |U| Some(&U[i]))
            ))
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        let rho = AllocatedNum::alloc(
            cs.namespace(|| "alloc rho"),
            || self.inputs.rho.get().copied()
        )?;

        Ok((lcccs, cccs, rho))
    }
}

impl<G: Group> NovaAuxiliarySecondCircuit<G> {
    /// synthesize circuit giving constraint system
    pub fn synthesize<CS: ConstraintSystem<<G as Group>::Base>>(
        self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<G::Base>, SynthesisError> {
        // Allocate all witnesses
        let (lcccs, cccs, rho)
            = self.alloc_witness(cs.namespace(|| "allocate the circuit witness"))?;

        let new_lcccs = crate::gadgets::cccs::multi_folding_with_second_part(
            cs.namespace(|| "calc new lcccs"),
            &lcccs,
            &cccs,
            rho
        )?;

        let mut ro = G::ROCircuit::new(self.ro_consts, (lcccs.len() + cccs.len() + 1) * 3);
        for c in lcccs {
            c.absorb_in_ro(&mut ro)?;
        }
        for c in cccs {
            c.absorb_in_ro(&mut ro)?;
        }
        new_lcccs.absorb_in_ro(&mut ro)?;
        let hash_bits = ro.squeeze(cs.namespace(|| "output hash bits"), NUM_HASH_BITS)?;
        let hash = le_bits_to_num(cs.namespace(|| "convert hash to num"), &hash_bits)?;

        hash.inputize(cs.namespace(|| "output new hash of this circuit"))?; // this circuit's x1

        Ok(hash)
    }
}