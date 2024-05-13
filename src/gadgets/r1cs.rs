//! This module implements various gadgets necessary for folding R1CS types.
use super::nonnative::{
  bignat::BigNat,
  util::{f_to_nat, Num},
};
use crate::{
  constants::{NUM_CHALLENGE_BITS, NUM_FE_FOR_RO},
  gadgets::{
    ecc::AllocatedPoint,
    utils::{
      alloc_bignat_constant, alloc_one, alloc_scalar_as_base, conditionally_select,
      conditionally_select_bignat, le_bits_to_num,
    },
  },
  r1cs::{R1CSInstance, RelaxedR1CSInstance},
  traits::{commitment::CommitmentTrait, Group, ROCircuitTrait, ROConstantsCircuit},
};
use bellpepper::gadgets::{boolean::Boolean, num::AllocatedNum, Assignment};
use bellpepper_core::boolean::AllocatedBit;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;
use itertools::Itertools;
use std::fmt::{Debug, Formatter};
use crate::gadgets::ext_allocated_num::ExtendFunc;

pub const ARITY: usize = 2;

/// An Allocated R1CS Instance
#[derive(Clone)]
pub struct AllocatedR1CSInstance<G: Group> {
  pub(crate) W: AllocatedPoint<G>,
  pub(crate) X: Vec<AllocatedNum<G::Base>>,
}

impl<G: Group> AllocatedR1CSInstance<G> {
  /// Takes the r1cs instance and creates a new allocated r1cs instance
  pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
    u: Option<&R1CSInstance<G>>,
    io_num: usize,
  ) -> Result<Self, SynthesisError> {
    // Check that the incoming instance has exactly 2 io
    let W = AllocatedPoint::alloc(
      cs.namespace(|| "allocate W"),
      u.get().map_or(None, |u| Some(u.comm_W.to_coordinates())),
    )?;

    let X = (0..io_num)
      .map(|i| {
        alloc_scalar_as_base::<G, _>(
          cs.namespace(|| format!("allocate X[{i}]")),
          u.get().map_or(None, |u| Some(u.X[i])),
        )
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(AllocatedR1CSInstance { W, X })
  }

  /// Absorb the provided instance in the RO
  pub fn absorb_in_ro(&self, ro: &mut G::ROCircuit) {
    println!(
      "RO u.w: {:?}, {:?}, {:?}",
      self.W.x.get_value(),
      self.W.y.get_value(),
      self.W.is_infinity.get_value()
    );
    ro.absorb(&self.W.x);
    ro.absorb(&self.W.y);
    ro.absorb(&self.W.is_infinity);
    println!();
    for x in &self.X {
      print!("RO u.x: {:?}", x.get_value());
      ro.absorb(x);
    }
    println!();
    println!();
  }
}

/// An Allocated Relaxed R1CS Instance
#[derive(Clone)]
pub struct AllocatedRelaxedR1CSInstance<G: Group> {
  pub(crate) W: AllocatedPoint<G>,
  pub(crate) E: AllocatedPoint<G>,
  pub(crate) u: AllocatedNum<G::Base>,
  pub(crate) Xs: Vec<BigNat<G::Base>>,
}

impl<G: Group> Debug for AllocatedRelaxedR1CSInstance<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("AllocatedRelaxedR1CSInstance")
      .field("W", &self.W)
      .field("E", &self.E)
      .field("u", &self.u.get_value())
      .field(
        "Xs",
        &self
          .Xs
          .iter()
          .map(|x| x.value.as_ref().map(|v| format!("{:x}", v)))
          .collect::<Vec<_>>(),
      )
      .finish()
  }
}

impl<G: Group> AllocatedRelaxedR1CSInstance<G> {
  /// Allocates the given `RelaxedR1CSInstance` as a witness of the circuit
  pub fn alloc<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
    inst: Option<&RelaxedR1CSInstance<G>>,
    io_num: usize,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<Self, SynthesisError> {
    let W = AllocatedPoint::alloc(
      cs.namespace(|| "allocate W"),
      inst
        .get()
        .map_or(None, |inst| Some(inst.comm_W.to_coordinates())),
    )?;

    let E = AllocatedPoint::alloc(
      cs.namespace(|| "allocate E"),
      inst
        .get()
        .map_or(None, |inst| Some(inst.comm_E.to_coordinates())),
    )?;

    // u << |G::Base| despite the fact that u is a scalar.
    // So we parse all of its bytes as a G::Base element
    let u = alloc_scalar_as_base::<G, _>(
      cs.namespace(|| "allocate u"),
      inst.get().map_or(None, |inst| Some(inst.u)),
    )?;

    // Allocate X0 and X1. If the input instance is None, then allocate default values 0.
    let Xs = (0..io_num)
      .map(|i| {
        BigNat::alloc_from_nat(
          cs.namespace(|| format!("allocate X[{i}]")),
          || Ok(f_to_nat(&inst.map_or(G::Scalar::ZERO, |inst| inst.X[i]))),
          limb_width,
          n_limbs,
        )
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(AllocatedRelaxedR1CSInstance { W, E, u, Xs })
  }

  /// Allocates the hardcoded default `RelaxedR1CSInstance` in the circuit.
  /// W = E = 0, u = 0, X0 = X1 = 0
  pub fn default<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
    limb_width: usize,
    n_limbs: usize,
    io_num: usize,
  ) -> Result<Self, SynthesisError> {
    let W = AllocatedPoint::default(cs.namespace(|| "allocate W"))?;
    let E = W.clone();

    let u = W.x.clone(); // In the default case, W.x = u = 0

    let Xs = (0..io_num)
      .map(|i| {
        BigNat::alloc_from_nat(
          cs.namespace(|| format!("allocate x_default[{i}]")),
          || Ok(f_to_nat(&G::Scalar::ZERO)),
          limb_width,
          n_limbs,
        )
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(AllocatedRelaxedR1CSInstance { W, E, u, Xs })
  }

  /// Allocates the R1CS Instance as a `RelaxedR1CSInstance` in the circuit.
  /// E = 0, u = 1
  pub fn from_r1cs_instance<CS: ConstraintSystem<<G as Group>::Base>>(
    mut cs: CS,
    inst: AllocatedR1CSInstance<G>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<Self, SynthesisError> {
    let E = AllocatedPoint::default(cs.namespace(|| "allocate W"))?;

    let u = alloc_one(cs.namespace(|| "one"))?;

    let X0 = BigNat::from_num(
      cs.namespace(|| "allocate X0 from relaxed r1cs"),
      &Num::from(inst.X[0].clone()),
      limb_width,
      n_limbs,
    )?;

    let X1 = BigNat::from_num(
      cs.namespace(|| "allocate X1 from relaxed r1cs"),
      &Num::from(inst.X[1].clone()),
      limb_width,
      n_limbs,
    )?;

    Ok(AllocatedRelaxedR1CSInstance {
      W: inst.W,
      E,
      u,
      Xs: vec![X0, X1],
    })
  }

  pub fn element_num(&self) -> usize {
    2 * 3 + 1 + self.Xs[0].params.n_limbs * self.Xs.len()
  }

  /// Absorb the provided instance in the RO
  pub fn absorb_in_ro<CS: ConstraintSystem<<G as Group>::Base>>(
    &self,
    mut cs: CS,
    ro: &mut G::ROCircuit,
  ) -> Result<(), SynthesisError> {
    println!(
      "RO self.w: {:?}, {:?}, {:?}",
      self.W.x.get_value(),
      self.W.y.get_value(),
      self.W.is_infinity.get_value()
    );
    println!(
      "RO self.w: {:?}, {:?}, {:?}",
      self.E.x.get_value(),
      self.E.y.get_value(),
      self.E.is_infinity.get_value()
    );
    println!("RO self.u: {:?}", self.u.get_value());
    ro.absorb(&self.W.x);
    ro.absorb(&self.W.y);
    ro.absorb(&self.W.is_infinity);
    ro.absorb(&self.E.x);
    ro.absorb(&self.E.y);
    ro.absorb(&self.E.is_infinity);
    ro.absorb(&self.u);

    // Analyze Xs as limbs
    println!();
    for (i, X) in self.Xs.iter().enumerate() {
      print!("self.X: {:?}, ", X.value);
      let X_bn = X
        .as_limbs()
        .iter()
        .enumerate()
        .map(|(j, limb)| {
          limb.as_allocated_num(cs.namespace(|| format!("convert limb[{j}] of X_r[{i}] to num")))
        })
        .collect::<Result<Vec<AllocatedNum<G::Base>>, _>>()?;

      for limb in X_bn {
        ro.absorb(&limb);
      }
    }
    println!();
    println!();

    Ok(())
  }

  /// Folds self with a r1cs instance and returns the result
  #[allow(clippy::too_many_arguments)]
  pub fn fold_with_r1cs<CS: ConstraintSystem<<G as Group>::Base>>(
    &self,
    mut cs: CS,
    u: &AllocatedR1CSInstance<G>,
    T: &AllocatedPoint<G>,
    r_bits: Vec<AllocatedBit>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<AllocatedRelaxedR1CSInstance<G>, SynthesisError> {
    let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;
    println!("ro r: {:?}", r.get_value());

    // W_fold = self.W + r * u.W
    let rW = u.W.scalar_mul(cs.namespace(|| "r * u.W"), &r_bits)?;
    let W_fold = self.W.add(cs.namespace(|| "self.W + r * u.W"), &rW)?;

    // E_fold = self.E + r * T
    let rT = T.scalar_mul(cs.namespace(|| "r * T"), &r_bits)?;
    let E_fold = self.E.add(cs.namespace(|| "self.E + r * T"), &rT)?;

    // u_fold = u_r + r
    let u_fold = AllocatedNum::alloc(cs.namespace(|| "u_fold"), || {
      Ok(*self.u.get_value().get()? + r.get_value().get()?)
    })?;
    cs.enforce(
      || "Check u_fold",
      |lc| lc,
      |lc| lc,
      |lc| lc + u_fold.get_variable() - self.u.get_variable() - r.get_variable(),
    );

    // Fold the IO:
    // Analyze r into limbs
    let r_bn = BigNat::from_num(
      cs.namespace(|| "allocate r_bn"),
      &Num::from(r),
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

    let mut Xs = Vec::new();
    for (i, (other_X, self_X)) in u.X.iter().zip_eq(self.Xs.iter()).enumerate() {
      let mut cs = cs.namespace(|| format!("{i}th folded X"));
      let X_bn = BigNat::from_num(
        cs.namespace(|| "allocate X_bn"),
        &Num::from(other_X.clone()),
        limb_width,
        n_limbs,
      )?;
      let (_, r) = X_bn.mult_mod(cs.namespace(|| "r*X"), &r_bn, &m_bn)?;
      let r_new = self_X.add(&r)?;
      // Now reduce
      Xs.push(r_new.red_mod(cs.namespace(|| "reduce folded X"), &m_bn)?);
    }

    Ok(Self {
      W: W_fold,
      E: E_fold,
      u: u_fold,
      Xs,
    })
  }

  #[allow(clippy::too_many_arguments)]
  pub fn fold_with_r1cs_contains_r<CS: ConstraintSystem<<G as Group>::Base>>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<G::Base>, // hash of R1CSShape of F'
    u: &AllocatedR1CSInstance<G>,
    T: &AllocatedPoint<G>,
    ro_consts: ROConstantsCircuit<G>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<AllocatedRelaxedR1CSInstance<G>, SynthesisError> {
    // Compute r:
    let mut ro = G::ROCircuit::new(ro_consts, NUM_FE_FOR_RO);
    ro.absorb(params);
    self.absorb_in_ro(cs.namespace(|| "absorb running instance"), &mut ro)?;
    u.absorb_in_ro(&mut ro);
    ro.absorb(&T.x);
    ro.absorb(&T.y);
    ro.absorb(&T.is_infinity);
    let r_bits = ro.squeeze(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
    self.fold_with_r1cs(
      cs.namespace(|| "fold with r1cs instance"),
      u,
      T,
      r_bits,
      limb_width,
      n_limbs,
    )
  }

  /// Folds self with a relaxed r1cs instance and returns the result
  #[allow(clippy::too_many_arguments)]
  pub fn fold_with_relaxed_r1cs<CS: ConstraintSystem<<G as Group>::Base>>(
    &self,
    mut cs: CS,
    U: &Self,
    T: &AllocatedPoint<G>,
    r_bits: Vec<AllocatedBit>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<AllocatedRelaxedR1CSInstance<G>, SynthesisError> {
    let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;
    println!("ro r: {:?}", r.get_value());

    // W_fold = self.W + r * U.W
    let rW = U.W.scalar_mul(cs.namespace(|| "r * u.W"), &r_bits)?;
    let W_fold = self.W.add(cs.namespace(|| "self.W + r * u.W"), &rW)?;

    // E_fold = self.E + r * T + r^2 * E
    let rT = T.scalar_mul(cs.namespace(|| "r * T"), &r_bits)?;
    let r_square_E = U.E.scalar_mul(cs.namespace(|| "r * r * E"), &r_bits)?;
    let E_fold = self
      .E
      .add(cs.namespace(|| "self.E + r * T"), &rT)?
      .add(cs.namespace(|| "self.E + r * T + r^2 * E"), &r_square_E)?;

    // u_fold = self.u + U.u * r
    let u_fold = U.u
        .mul(cs.namespace(|| "U.u * r"), &r)?
        .add(cs.namespace(|| "self.u + U.u * r"), &self.u)?;

    // Fold the IO:
    // Analyze r into limbs
    let r_bn = BigNat::from_num(
      cs.namespace(|| "allocate r_bn"),
      &Num::from(r),
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

    let mut Xs = Vec::new();
    for (i, (other_X, self_X)) in U.Xs.iter().zip_eq(self.Xs.iter()).enumerate() {
      let mut cs = cs.namespace(|| format!("{i}th folded X"));
      let (_, r) = other_X.mult_mod(cs.namespace(|| "r*X"), &r_bn, &m_bn)?;
      let r_new = self_X.add(&r)?;
      // Now reduce
      Xs.push(r_new.red_mod(cs.namespace(|| "reduce folded X"), &m_bn)?);
    }

    Ok(Self {
      W: W_fold,
      E: E_fold,
      u: u_fold,
      Xs,
    })
  }

  /// If the condition is true then returns this otherwise it returns the other
  pub fn conditionally_select<CS: ConstraintSystem<<G as Group>::Base>>(
    &self,
    mut cs: CS,
    other: &AllocatedRelaxedR1CSInstance<G>,
    condition: &Boolean,
  ) -> Result<AllocatedRelaxedR1CSInstance<G>, SynthesisError> {
    let W = AllocatedPoint::conditionally_select(
      cs.namespace(|| "W = cond ? self.W : other.W"),
      &self.W,
      &other.W,
      condition,
    )?;

    let E = AllocatedPoint::conditionally_select(
      cs.namespace(|| "E = cond ? self.E : other.E"),
      &self.E,
      &other.E,
      condition,
    )?;

    let u = conditionally_select(
      cs.namespace(|| "u = cond ? self.u : other.u"),
      &self.u,
      &other.u,
      condition,
    )?;

    let Xs = self
      .Xs
      .iter()
      .zip_eq(other.Xs.iter())
      .enumerate()
      .map(|(i, (x, other_x))| {
        conditionally_select_bignat(
          cs.namespace(|| format!("X[{i}] = cond ? self.X[{i}] : other.X[{i}]")),
          x,
          other_x,
          condition,
        )
      })
      .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(AllocatedRelaxedR1CSInstance { W, E, u, Xs })
  }
}
