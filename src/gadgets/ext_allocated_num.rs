use crate::compress_snark::math::Math;
use bellpepper::gadgets::Assignment;
use bellpepper_core::num::{AllocatedNum, Num};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

pub trait ExtendFunc<Scalar: PrimeField> {
  fn zero<CS: ConstraintSystem<Scalar>>(cs: CS) -> Result<AllocatedNum<Scalar>, SynthesisError>;

  fn one<CS: ConstraintSystem<Scalar>>(cs: CS) -> Result<AllocatedNum<Scalar>, SynthesisError>;

  fn add<CS: ConstraintSystem<Scalar>>(
    &self,
    cs: CS,
    other: &AllocatedNum<Scalar>,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError>;

  fn sub_constant<CS: ConstraintSystem<Scalar>>(
    &self,
    cs: CS,
    constant: Scalar,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError>;

  fn mul_with_scale<CS: ConstraintSystem<Scalar>>(
    &self,
    cs: CS,
    other: &AllocatedNum<Scalar>,
    scale: Scalar,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError>;

  fn mul_lc<CS: ConstraintSystem<Scalar>>(
    &self,
    cs: CS,
    other: Num<Scalar>,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError>;

  fn pow_constant<CS: ConstraintSystem<Scalar>>(
    &self,
    cs: CS,
    constant: usize,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError>;

  fn invert_with_scale<CS: ConstraintSystem<Scalar>>(
    &self,
    cs: CS,
    scale: Scalar,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError>;
}

impl<Scalar: PrimeField> ExtendFunc<Scalar> for AllocatedNum<Scalar> {
  fn zero<CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let tmp = AllocatedNum::alloc(cs.namespace(|| "alloc tmp"), || Ok(Scalar::ZERO))?;
    cs.enforce(
      || "constraints tmp = one",
      |lc| lc + tmp.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc,
    );
    Ok(tmp)
  }

  fn one<CS: ConstraintSystem<Scalar>>(mut cs: CS) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let tmp = AllocatedNum::alloc(cs.namespace(|| "alloc tmp"), || Ok(Scalar::ONE))?;
    cs.enforce(
      || "constraints tmp = one",
      |lc| lc + tmp.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + CS::one(),
    );
    Ok(tmp)
  }

  fn add<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    other: &AllocatedNum<Scalar>,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let tmp = AllocatedNum::alloc(cs.namespace(|| "alloc tmp"), || {
      self
        .get_value()
        .and_then(|v| other.get_value().map(|o| v + o))
        .get()
        .copied()
    })?;
    cs.enforce(
      || "constraints tmp = self + other",
      |lc| lc + self.get_variable() + other.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + tmp.get_variable(),
    );
    Ok(tmp)
  }

  fn sub_constant<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    constant: Scalar,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let tmp = AllocatedNum::alloc(cs.namespace(|| "alloc tmp"), || {
      self.get_value().map(|v| v - constant).get().copied()
    })?;
    cs.enforce(
      || "constraints tmp = self - constant",
      |lc| lc + tmp.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + self.get_variable() - (constant, CS::one()),
    );
    Ok(tmp)
  }

  fn mul_with_scale<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    other: &AllocatedNum<Scalar>,
    scale: Scalar,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let tmp = AllocatedNum::alloc(cs.namespace(|| "alloc tmp"), || {
      self
        .get_value()
        .and_then(|v| other.get_value().map(|o| v * scale * o))
        .get()
        .copied()
    })?;
    cs.enforce(
      || "constraints tmp = self * constant * other",
      |lc| lc + self.get_variable(),
      |lc| lc + (scale, other.get_variable()),
      |lc| lc + tmp.get_variable(),
    );
    Ok(tmp)
  }

  fn mul_lc<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    other: Num<Scalar>,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let tmp = AllocatedNum::alloc(cs.namespace(|| "alloc tmp"), || {
      self
        .get_value()
        .and_then(|v| other.get_value().map(|o| v * o))
        .get()
        .copied()
    })?;
    cs.enforce(
      || "constraints tmp = self  * other",
      |lc| lc + self.get_variable(),
      |_lc| other.lc(Scalar::ONE),
      |lc| lc + tmp.get_variable(),
    );
    Ok(tmp)
  }

  fn pow_constant<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    constant: usize,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let mut res = AllocatedNum::alloc(cs.namespace(|| "one"), || Ok(Scalar::ONE))?;

    if constant == 0 {
      return Ok(res);
    }

    let constant_bits_num = constant.log_2();

    let mut temp = self.clone();
    for i in 0..constant_bits_num + 1 {
      if constant >> i & 1 == 1 {
        res = res.mul(cs.namespace(|| format!("mul step: {}", i)), &temp)?;
      }
      temp = temp.square(cs.namespace(|| format!("square on step: {}", i)))?;
    }

    Ok(res)
  }

  fn invert_with_scale<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    scale: Scalar,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let inv = AllocatedNum::alloc(cs.namespace(|| "alloc tmp"), || {
      self
        .get_value()
        .map(|v| (v * scale).invert().unwrap())
        .get()
        .copied()
    })?;
    cs.enforce(
      || "constraints 1 = self * self.invert",
      |lc| lc + (scale, self.get_variable()),
      |lc| lc + inv.get_variable(),
      |lc| lc + CS::one(),
    );
    Ok(inv)
  }
}
