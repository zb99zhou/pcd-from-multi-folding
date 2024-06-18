use crate::compute_digest;
use crate::gadgets::cccs::AllocatedCCCSSecondPart;
use crate::gadgets::lcccs::AllocatedLCCCSSecondPart;
use crate::gadgets::utils::from_le_bits_to_num;
use crate::nifs::r1cs::R1CSShape;
use crate::nimfs::ccs::cccs::CCCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::traits::Group;
use bellpepper::gadgets::Assignment;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;
use serde::Serialize;

#[derive(Clone)]
pub struct NovaAuxiliaryInputs<G: Group> {
  params: Option<G::Base>, // Hash(Shape of u2, Gens for u2). Needed for computing the challenge.
  lcccs: Option<Vec<LCCCS<G>>>,
  cccs: Option<Vec<CCCS<G>>>,
  rho: Option<G::Base>,
  r: usize, // the number of multi-folding PCD node at once
}

#[derive(Clone)]
pub struct NovaAuxiliarySecondCircuit<G: Group> {
  inputs: NovaAuxiliaryInputs<G>,
  limb_width: usize,
  n_limbs: usize,
}

impl<G: Group> NovaAuxiliaryInputs<G> {
  pub fn new(
    params: Option<G::Base>,
    lcccs: Option<Vec<LCCCS<G>>>,
    cccs: Option<Vec<CCCS<G>>>,
    rho: Option<G::Base>,
    r: usize,
  ) -> Self {
    Self {
      params,
      lcccs,
      cccs,
      rho,
      r,
    }
  }
}

#[derive(Serialize)]
pub struct NovaAuxiliaryParams<G: Group> {
  pub(crate) r1cs_shape: R1CSShape<G>,
  pub(crate) io_num: usize,
  pub(crate) digest: G::Scalar,
}

impl<G: Group> NovaAuxiliaryParams<G> {
  pub fn new(r1cs_shape: R1CSShape<G>, io_num: usize) -> Self {
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
  pub fn new(inputs: NovaAuxiliaryInputs<G>, limb_width: usize, n_limbs: usize) -> Self {
    Self {
      inputs,
      limb_width,
      n_limbs,
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
      AllocatedNum<G::Base>,
    ),
    SynthesisError,
  > {
    // Allocate the running instance
    let lcccs = (0..self.inputs.r)
      .map(|i| {
        AllocatedLCCCSSecondPart::alloc(
          cs.namespace(|| format!("allocate {i}th lcccs")),
          self
            .inputs
            .lcccs
            .get()
            .as_ref()
            .map_or(None, |U| Some(&U[i])),
        )
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;

    // Allocate the instance to be folded in
    let cccs = (0..self.inputs.r)
      .map(|i| {
        AllocatedCCCSSecondPart::alloc(
          cs.namespace(|| format!("allocate {i}th cccs")),
          self
            .inputs
            .cccs
            .get()
            .as_ref()
            .map_or(None, |U| Some(&U[i])),
        )
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;

    let rho = AllocatedNum::alloc(cs.namespace(|| "alloc rho"), || {
      self.inputs.rho.get().copied()
    })?;

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
    let (lcccs, cccs, rho) = self.alloc_witness(cs.namespace(|| "allocate the circuit witness"))?;

    let new_lcccs = crate::gadgets::cccs::multi_folding_with_second_part(
      cs.namespace(|| "calc new lcccs"),
      &lcccs,
      &cccs,
      &rho,
      self.limb_width,
      self.n_limbs,
    )?;

    // public input
    let mut ecc_parity_container = Vec::new();
    rho.inputize(cs.namespace(|| "pub rho"))?;
    for (i, x) in lcccs.into_iter().enumerate() {
      let mut cs = cs.namespace(|| format!("{i}th lcccs"));
      x.C.check_on_curve(cs.namespace(|| "check C on curve"))?;
      x.C
        .compressed_inputize(cs.namespace(|| "input C"), &mut ecc_parity_container)?;
    }
    for (i, x) in cccs.into_iter().enumerate() {
      let mut cs = cs.namespace(|| format!("{i}th cccs"));
      x.C.check_on_curve(cs.namespace(|| "check C on curve"))?;
      x.C
        .compressed_inputize(cs.namespace(|| "input C"), &mut ecc_parity_container)?;
    }
    new_lcccs
      .C
      .compressed_inputize(cs.namespace(|| "pub new lcccs"), &mut ecc_parity_container)?;

    let ecc_compression_num = from_le_bits_to_num(
      cs.namespace(|| "alloc ecc_compression_num"),
      &ecc_parity_container,
    )?;
    ecc_compression_num.inputize(cs.namespace(|| "pub ecc_compression_num"))?;

    Ok(())
  }
}
