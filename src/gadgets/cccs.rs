//! This module implements various gadgets necessary for folding R1CS types.
use super::lcccs::{AllocatedLCCCSPrimaryPart, AllocatedLCCCSSecondPart};
use crate::gadgets::ecc::AllocatedSimulatedPoint;
use crate::gadgets::ext_allocated_num::ExtendFunc;
use crate::gadgets::nonnative::bignat::BigNat;
use crate::gadgets::utils::{alloc_bignat_constant, alloc_vec_number_equals_zero, multi_and};
use crate::nimfs::ccs::cccs::{CCCSForBase, CCCS};
use crate::traits::commitment::CommitmentTrait;
use crate::traits::ROCircuitTrait;
use crate::{gadgets::ecc::AllocatedPoint, traits::Group};
use bellpepper::gadgets::{boolean::Boolean, num::AllocatedNum, Assignment};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;
use num_bigint::BigInt;
use num_traits::One;

/// An Allocated Committed CCS instance
#[derive(Clone)]
pub struct AllocatedCCCS<G: Group> {
  pub primary_part: AllocatedCCCSPrimaryPart<G>,
  pub C: AllocatedSimulatedPoint<G>,
}

impl<G: Group> AllocatedCCCS<G> {
  pub fn new(Xs: Vec<AllocatedNum<G::Base>>, C: AllocatedSimulatedPoint<G>) -> Self {
    Self {
      primary_part: AllocatedCCCSPrimaryPart { Xs },
      C,
    }
  }

  /// Takes the CCCS instance and creates a new allocated CCCS instance
  pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
    cccs: Option<&CCCSForBase<G>>,
    limb_width: usize,
    n_limbs: usize,
    io_num: usize,
  ) -> Result<Self, SynthesisError> {
    let Xs = (0..io_num)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("allocate X[{}]", i)), || {
          Ok(cccs.get().map_or(G::Base::ZERO, |u| u.x[i]))
        })
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;
    let C = AllocatedSimulatedPoint::alloc(
      cs.namespace(|| "alloc C"),
      cccs.as_ref().map(|c| c.C),
      limb_width,
      n_limbs,
    )?;

    Ok(AllocatedCCCS::new(Xs, C))
  }

  pub fn is_null<CS: ConstraintSystem<G::Base>>(
    &self,
    mut cs: CS,
    zero: &AllocatedNum<G::Base>,
  ) -> Result<Boolean, SynthesisError> {
    let is_null1 = self
      .primary_part
      .is_null(cs.namespace(|| "self.primary_part"), zero)?;
    let is_null2 = self.C.is_null(cs.namespace(|| "self.C"))?;
    multi_and(cs.namespace(|| "lcccs is null"), &[is_null1, is_null2]).map(Into::into)
  }
}

/// An Allocated Committed CCS instance
#[derive(Clone)]
pub struct AllocatedCCCSPrimaryPart<G: Group> {
  pub(crate) Xs: Vec<AllocatedNum<G::Base>>,
}

impl<G: Group> AllocatedCCCSPrimaryPart<G> {
  pub fn is_null<CS: ConstraintSystem<G::Base>>(
    &self,
    mut cs: CS,
    zero: &AllocatedNum<G::Base>,
  ) -> Result<Boolean, SynthesisError> {
    alloc_vec_number_equals_zero(cs.namespace(|| "is Xs zero"), &self.Xs, zero).map(Into::into)
  }

  /// Takes the CCCS instance and creates a new allocated CCCS instance
  pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
    cccs: Option<&CCCSForBase<G>>,
    io_num: usize,
  ) -> Result<Self, SynthesisError> {
    let Xs = (0..io_num)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("allocate X[{}]", i)), || {
          Ok(cccs.get().map_or(G::Base::ZERO, |u| u.x[i]))
        })
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;

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
  pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
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

  pub fn absorb_in_ro(&self, ro: &mut G::ROCircuit) -> Result<(), SynthesisError> {
    ro.absorb(&self.C.is_infinity);
    ro.absorb(&self.C.x);
    ro.absorb(&self.C.y);

    Ok(())
  }
}

#[allow(clippy::too_many_arguments)]
pub fn multi_folding_with_primary_part<CS: ConstraintSystem<<G as Group>::Base>, G: Group>(
  mut cs: CS,
  lcccs: &[AllocatedLCCCSPrimaryPart<G>],
  cccs: &[AllocatedCCCSPrimaryPart<G>],
  rho: &AllocatedNum<G::Base>,
  sigmas: &[Vec<AllocatedNum<G::Base>>],
  thetas: &[Vec<AllocatedNum<G::Base>>],
) -> Result<AllocatedLCCCSPrimaryPart<G>, SynthesisError> {
  // init
  let mut lcccs_folded = lcccs[0].clone();
  lcccs_folded.Vs.clone_from(&sigmas[0]);
  let mut rho_i = AllocatedNum::one(cs.namespace(|| "alloc one"))?;

  // folding
  for (i, lcccs) in lcccs.iter().enumerate().skip(1) {
    rho_i = rho_i.mul(
      cs.namespace(|| format!("alloc rho_{i} in folding lcccs")),
      rho,
    )?;
    lcccs_folded.folding_with_lcccs_primary_part(
      cs.namespace(|| format!("folding {i}th lcccs")),
      lcccs,
      &rho_i,
      &sigmas[i],
    )?;
  }
  for (i, cccs) in cccs.iter().enumerate() {
    rho_i = rho_i.mul(
      cs.namespace(|| format!("alloc rho_{i} in folding cccs")),
      rho,
    )?;
    lcccs_folded.folding_with_cccs_primary_part(
      cs.namespace(|| format!("folding {i}th cccs")),
      cccs,
      &rho_i,
      &thetas[i],
    )?;
  }
  Ok(lcccs_folded)
}

#[allow(clippy::too_many_arguments)]
pub fn multi_folding_with_second_part<CS: ConstraintSystem<<G as Group>::Base>, G: Group>(
  mut cs: CS,
  lcccs: &[AllocatedLCCCSSecondPart<G>],
  cccs: &[AllocatedCCCSSecondPart<G>],
  rho: &AllocatedNum<G::Base>,
  limb_width: usize,
  n_limbs: usize,
) -> Result<AllocatedLCCCSSecondPart<G>, SynthesisError> {
  // init
  let mut lcccs_folded = lcccs[0].clone();
  let rho = BigNat::from_num(
    cs.namespace(|| "alloc rho"),
    &rho.clone().into(),
    limb_width,
    n_limbs,
  )?;
  let mut rho_i = alloc_bignat_constant(
    cs.namespace(|| "alloc rho_0 = one"),
    &BigInt::one(),
    limb_width,
    n_limbs,
  )?;
  let m_bn = alloc_bignat_constant(
    cs.namespace(|| "alloc m bignat"),
    &G::get_curve_params().2,
    limb_width,
    n_limbs,
  )?;

  // folding
  for (i, lcccs) in lcccs.iter().enumerate().skip(1) {
    rho_i = rho_i
      .mult_mod(
        cs.namespace(|| format!("calc rho_{i} in folding lcccs")),
        &rho,
        &m_bn,
      )?
      .1;
    lcccs_folded.folding_with_lcccs_second_part(
      cs.namespace(|| format!("folding {i}th lcccs")),
      lcccs,
      &rho_i,
    )?;
  }
  for (i, cccs) in cccs.iter().enumerate() {
    rho_i = rho_i
      .mult_mod(
        cs.namespace(|| format!("calc rho_{i} in folding cccs")),
        &rho,
        &m_bn,
      )?
      .1;
    lcccs_folded.folding_with_cccs_second_part(
      cs.namespace(|| format!("folding {i}th cccs")),
      cccs,
      &rho_i,
    )?;
  }
  Ok(lcccs_folded)
}
