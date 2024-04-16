use bellpepper::gadgets::Assignment;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::num::AllocatedNum;
use ff::Field;
use serde::Serialize;
use crate::compute_digest;
use crate::gadgets::cccs::{AllocatedCCCSSecondPart, AllocatedLCCCSSecondPart};
use crate::nimfs::ccs::cccs::CCCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::r1cs::R1CSShape;
use crate::traits::Group;

#[derive(Clone)]
pub struct NovaAuxiliaryInputs<G: Group> {
    params: Option<G::Base>, // Hash(Shape of u2, Gens for u2). Needed for computing the challenge.
    lcccs: Option<Vec<LCCCS<G>>>,
    cccs: Option<Vec<CCCS<G>>>,
    rho: Option<G::Base>,
    r: usize // the number of multi-folding PCD node at once
}

#[derive(Clone)]
pub struct NovaAuxiliarySecondCircuit<G: Group> {
    inputs: NovaAuxiliaryInputs<G>,
}

impl<G: Group> NovaAuxiliaryInputs<G>{
    pub fn new(
        params: Option<G::Base>,
        lcccs: Option<Vec<LCCCS<G>>>,
        cccs: Option<Vec<CCCS<G>>>,
        rho: Option<G::Base>,
        r: usize
    ) -> Self{
        Self{
            params,
            lcccs,
            cccs,
            rho,
            r,
        }
    }
}

#[derive(Serialize)]
pub struct NovaAuxiliaryParams<G: Group>{
    pub(crate) r1cs_shape: R1CSShape<G>,
    pub(crate) io_num: usize,
    pub(crate) digest: G::Scalar,
}

impl<G: Group> NovaAuxiliaryParams<G> {
    pub fn new(
        r1cs_shape: R1CSShape<G>,
        io_num: usize,
    ) -> Self {
        let mut pp = Self {
            r1cs_shape,
            io_num,
            digest: G::Scalar::ZERO,
        };
        pp.digest = compute_digest::<G, NovaAuxiliaryParams<G>>(&pp);

        pp
    }

}

impl<G: Group> NovaAuxiliarySecondCircuit<G> {
    pub fn new(
        inputs: NovaAuxiliaryInputs<G>,
    ) -> Self{
        Self{
            inputs,
        }
    }

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
    ) -> Result<(), SynthesisError> {
        // Allocate all witnesses
        let (lcccs, cccs, rho)
            = self.alloc_witness(cs.namespace(|| "allocate the circuit witness"))?;

        let new_lcccs = crate::gadgets::cccs::multi_folding_with_second_part(
            cs.namespace(|| "calc new lcccs"),
            &lcccs,
            &cccs,
            &rho
        )?;

        // TODO: compress ecc point to x0, x1, x2, ... , ys_parity(the bit that expresses the parity of all y encode to element)
        // public input
        rho.inputize(cs.namespace(|| "pub rho"))?;
        for (i, x) in lcccs.into_iter().enumerate() {
            x.C.inputize(cs.namespace(|| format!("{i}th lcccs")))?;
        }
        for (i, x) in cccs.into_iter().enumerate() {
            x.C.inputize(cs.namespace(|| format!("{i}th cccs")))?;
        }
        new_lcccs.C.inputize(cs.namespace(|| "pub new lcccs"))?;

        Ok(())
    }
}