//! This module implements various gadgets necessary for folding R1CS types.
use crate::gadgets::ecc::AllocatedSimulatedPoint;
use crate::gadgets::ext_allocated_num::ExtendFunc;
use crate::gadgets::nonnative::bignat::BigNat;
use crate::gadgets::utils::{
  alloc_bignat_constant, alloc_num_equals, alloc_vec_number_equals_zero,
  conditionally_select_vec_allocated_num, multi_and,
};
use crate::nimfs::ccs::cccs::{CCCSForBase, CCCS};
use crate::nimfs::ccs::lcccs::{LCCCSForBase, LCCCS};
use crate::traits::commitment::CommitmentTrait;
use crate::traits::ROCircuitTrait;
use crate::{
  gadgets::{ecc::AllocatedPoint, utils::conditionally_select},
  traits::Group,
};
use bellpepper::gadgets::{boolean::Boolean, num::AllocatedNum, Assignment};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;
use num_bigint::BigInt;
use num_traits::One;
use std::fmt::{Debug, Formatter};

// TODO: split lcccs and cccs to two file
/// An Allocated Linear Committed CCS instance
#[derive(Clone)]
pub struct AllocatedLCCCS<G: Group> {
  pub primary_part: AllocatedLCCCSPrimaryPart<G>,
  pub C: AllocatedSimulatedPoint<G>,
}

impl<G: Group> Debug for AllocatedLCCCS<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("AllocatedLCCCS")
      .field("primary_part", &self.primary_part)
      .field("C", &self.C)
      .finish()
  }
}

impl<G: Group> AllocatedLCCCS<G> {
  pub fn new(primary_part: AllocatedLCCCSPrimaryPart<G>, C: AllocatedSimulatedPoint<G>) -> Self {
    Self { primary_part, C }
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

  /// Allocates the given `LCCCS` as a witness of the circuit
  pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
    inst: Option<&LCCCSForBase<G>>,
    io_num: usize,
    (t, s): (usize, usize),
    (limb_width, n_limbs): (usize, usize),
  ) -> Result<Self, SynthesisError> {
    let primary_part = AllocatedLCCCSPrimaryPart::alloc(
      cs.namespace(|| "alloc lcccs primary part"),
      inst,
      io_num,
      t,
      s,
    )?;
    let C = AllocatedSimulatedPoint::alloc(
      cs.namespace(|| "alloc C"),
      inst.as_ref().map(|c| c.C),
      limb_width,
      n_limbs,
    )?;

    Ok(Self { primary_part, C })
  }

  /// If the condition is true then returns this otherwise it returns the other
  pub fn conditionally_select<CS: ConstraintSystem<<G as Group>::Base>>(
    &self,
    mut cs: CS,
    other: &Self,
    condition: &Boolean,
  ) -> Result<AllocatedLCCCS<G>, SynthesisError> {
    let primary_part = self.primary_part.conditionally_select(
      cs.namespace(|| "select primary_part"),
      &other.primary_part,
      condition,
    )?;
    let C = self
      .C
      .conditionally_select(cs.namespace(|| "select C"), &other.C, condition)?;

    Ok(Self { primary_part, C })
  }

  pub fn absorb_in_ro<CS: ConstraintSystem<<G as Group>::Base>>(
    &self,
    cs: CS,
    ro: &mut G::ROCircuit,
  ) -> Result<(), SynthesisError> {
    self.C.absorb_in_ro(cs, ro)?;
    self.primary_part.absorb_in_ro(ro)?;
    Ok(())
  }

  pub fn element_num(&self) -> usize {
    2 * self.C.x.params.n_limbs
      + 1
      + self.primary_part.r_x.len()
      + self.primary_part.Xs.len()
      + self.primary_part.Vs.len()
  }
}

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

/// An Allocated Linearized Committed CCS instance
#[derive(Clone)]
pub struct AllocatedLCCCSPrimaryPart<G: Group> {
  pub u: AllocatedNum<G::Base>,
  pub Xs: Vec<AllocatedNum<G::Base>>,
  pub Vs: Vec<AllocatedNum<G::Base>>,
  pub r_x: Vec<AllocatedNum<G::Base>>,
}

impl<G: Group> Debug for AllocatedLCCCSPrimaryPart<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("AllocatedLCCCSPrimaryPart")
      .field("u", &self.u.get_value())
      .field(
        "Xs",
        &self.Xs.iter().map(|x| x.get_value()).collect::<Vec<_>>(),
      )
      .field(
        "Vs",
        &self.Vs.iter().map(|v| v.get_value()).collect::<Vec<_>>(),
      )
      .field(
        "r_x",
        &self.r_x.iter().map(|r| r.get_value()).collect::<Vec<_>>(),
      )
      .finish()
  }
}

impl<G: Group> AllocatedLCCCSPrimaryPart<G> {
  pub fn is_null<CS: ConstraintSystem<G::Base>>(
    &self,
    mut cs: CS,
    zero: &AllocatedNum<G::Base>,
  ) -> Result<Boolean, SynthesisError> {
    let is_u_zero = alloc_num_equals(cs.namespace(|| "alloc is_u_zero"), &self.u, zero)?.into();

    let Xs_num = alloc_vec_number_equals_zero(cs.namespace(|| "is Xs zero"), &self.Xs, zero)?;
    let is_Vs_zero = alloc_vec_number_equals_zero(cs.namespace(|| "is Vs zero"), &self.Vs, zero)?;

    multi_and(
      cs.namespace(|| "final result"),
      &[is_u_zero, Xs_num, is_Vs_zero],
    )
    .map(Into::into)
  }

  /// Allocates the given `LCCCS` as a witness of the circuit
  pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
    inst: Option<&LCCCSForBase<G>>,
    io_num: usize,
    t: usize,
    s: usize,
  ) -> Result<Self, SynthesisError> {
    // u << |G::Base| despite the fact that u is a scalar.
    // So we parse all of its bytes as a G::Base element
    let u = AllocatedNum::alloc(cs.namespace(|| "allocate u"), || {
      Ok(inst.map_or(G::Base::ZERO, |inst| inst.u))
    })?;

    let Xs = (0..io_num)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("allocate x[{}]", i)), || {
          Ok(inst.map_or(G::Base::ZERO, |inst| inst.x[i]))
        })
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;
    let Vs = (0..t)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("allocate v[{}]", i)), || {
          Ok(inst.map_or(G::Base::ZERO, |inst| inst.v[i]))
        })
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;
    let r_x = (0..s)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("allocate r[{}]", i)), || {
          Ok(inst.map_or(G::Base::ZERO, |inst| inst.r_x[i]))
        })
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(AllocatedLCCCSPrimaryPart { u, Xs, r_x, Vs })
  }

  /// Allocates the hardcoded default `LCCCS` in the circuit.
  /// C = 0, u = 0, X0 = X1 = ... = Xn = 0
  pub fn default<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
    io_num: usize,
    s: usize,
    t: usize,
  ) -> Result<Self, SynthesisError> {
    // let u = C.x.clone(); // In the default case, W.x = u = 0
    let u = AllocatedNum::zero(cs.namespace(|| "alloc zero`"))?;

    let Xs = (0..io_num)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("allocate x[{}]", i)), || {
          Ok(G::Base::ZERO)
        })
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;
    let Vs = (0..t)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("allocate v[{}]", i)), || {
          Ok(G::Base::ZERO)
        })
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;
    let r_x = (0..s)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("allocate r[{}]", i)), || {
          Ok(G::Base::ZERO)
        })
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(AllocatedLCCCSPrimaryPart { u, Xs, r_x, Vs })
  }

  /// Absorb the provided instance in the RO
  pub fn absorb_in_ro(&self, ro: &mut G::ROCircuit) -> Result<(), SynthesisError> {
    ro.absorb(&self.u);

    for X in self.Xs.iter() {
      ro.absorb(X);
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
  pub fn conditionally_select<CS: ConstraintSystem<<G as Group>::Base>>(
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

    let Xs = conditionally_select_vec_allocated_num(
      cs.namespace(|| "Xs"),
      &self.Xs,
      &other.Xs,
      condition,
    )?;

    let r_x = conditionally_select_vec_allocated_num(
      cs.namespace(|| "r_x "),
      &self.r_x,
      &other.r_x,
      condition,
    )?;

    let Vs = conditionally_select_vec_allocated_num(
      cs.namespace(|| "Vs"),
      &self.Vs,
      &other.Vs,
      condition,
    )?;

    Ok(AllocatedLCCCSPrimaryPart { u, Xs, r_x, Vs })
  }

  #[allow(clippy::too_many_arguments)]
  pub fn folding_with_lcccs_primary_part<CS: ConstraintSystem<<G as Group>::Base>>(
    &mut self,
    mut cs: CS,
    lcccs: &AllocatedLCCCSPrimaryPart<G>,
    rho_i: &AllocatedNum<G::Base>,
    sigmas: &[AllocatedNum<G::Base>],
  ) -> Result<(), SynthesisError> {
    self.folding(
      cs.namespace(|| "folding with lcccs"),
      rho_i,
      &lcccs.u,
      &lcccs.Xs,
      sigmas,
    )
  }

  #[allow(clippy::too_many_arguments)]
  pub fn folding_with_cccs_primary_part<CS: ConstraintSystem<<G as Group>::Base>>(
    &mut self,
    mut cs: CS,
    cccs: &AllocatedCCCSPrimaryPart<G>,
    rho_i: &AllocatedNum<G::Base>,
    thetas: &[AllocatedNum<G::Base>],
  ) -> Result<(), SynthesisError> {
    let one = AllocatedNum::one(cs.namespace(|| "alloc"))?;
    self.folding(
      cs.namespace(|| " folding with cccs"),
      rho_i,
      &one,
      &cccs.Xs,
      thetas,
    )
  }

  #[allow(clippy::too_many_arguments)]
  pub fn folding<CS: ConstraintSystem<<G as Group>::Base>>(
    &mut self,
    mut cs: CS,
    rho_i: &AllocatedNum<G::Base>,
    u: &AllocatedNum<G::Base>,
    x: &[AllocatedNum<G::Base>],
    v: &[AllocatedNum<G::Base>],
  ) -> Result<(), SynthesisError> {
    // u_fold = self.u + rho_i * u
    let u_fold = AllocatedNum::alloc(cs.namespace(|| "u_fold"), || {
      Ok(*self.u.get_value().get()? + *rho_i.get_value().get()? * *u.get_value().get()?)
    })?;
    cs.enforce(
      || "Check u_fold",
      |lc| lc + rho_i.get_variable(),
      |lc| lc + u.get_variable(),
      |lc| lc + u_fold.get_variable() - self.u.get_variable(),
    );

    // Fold the IO:
    let mut Xs_folded = Vec::new();
    for (i, (X_folded, X)) in self.Xs.iter().zip(x.iter()).enumerate() {
      let mut cs = cs.namespace(|| format!("folding {}th x", i));
      // Fold lcccs.X + r * lccc.X
      let r_0 = X.mul(cs.namespace(|| "r * X"), rho_i)?;
      let r_new_0 = X_folded.add(cs.namespace(|| "X_folded + r * X"), &r_0)?;
      Xs_folded.push(r_new_0);
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
  pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
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
  pub fn default<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
  ) -> Result<Self, SynthesisError> {
    let C = AllocatedPoint::default(cs.namespace(|| "allocate W"))?;
    Ok(AllocatedLCCCSSecondPart { C })
  }

  /// Allocates the CCCS Instance as a LCCCS in the circuit.
  pub fn from_cccs(inst: AllocatedCCCSSecondPart<G>) -> Result<Self, SynthesisError> {
    Ok(AllocatedLCCCSSecondPart { C: inst.C })
  }

  /// If the condition is true then returns this otherwise it returns the other
  pub fn conditionally_select<CS: ConstraintSystem<<G as Group>::Base>>(
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
  pub fn folding_with_lcccs_second_part<CS: ConstraintSystem<<G as Group>::Base>>(
    &mut self,
    mut cs: CS,
    lcccs: &AllocatedLCCCSSecondPart<G>,
    rho_i: &BigNat<G::Base>,
  ) -> Result<(), SynthesisError> {
    self.folding(cs.namespace(|| " folding with lcccs"), &lcccs.C, rho_i)
  }

  #[allow(clippy::too_many_arguments)]
  pub fn folding_with_cccs_second_part<CS: ConstraintSystem<<G as Group>::Base>>(
    &mut self,
    mut cs: CS,
    cccs: &AllocatedCCCSSecondPart<G>,
    rho_i: &BigNat<G::Base>,
  ) -> Result<(), SynthesisError> {
    self.folding(cs.namespace(|| " folding with cccs"), &cccs.C, rho_i)
  }

  #[allow(clippy::too_many_arguments)]
  pub fn folding<CS: ConstraintSystem<<G as Group>::Base>>(
    &mut self,
    mut cs: CS,
    C: &AllocatedPoint<G>,
    rho_i: &BigNat<G::Base>,
  ) -> Result<(), SynthesisError> {
    let rho_i_bits = rho_i
      .decompose(cs.namespace(|| "decompose bitnat to bits"))?
      .get_bits();

    // C_fold = self.C + r * u.C
    let r_C = C.scalar_mul(cs.namespace(|| "r * u.C"), &rho_i_bits)?;
    let C_fold = self.C.add(cs.namespace(|| "self.C + r * u.C"), &r_C)?;

    self.C = C_fold;

    Ok(())
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
