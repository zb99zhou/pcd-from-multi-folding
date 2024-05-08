use super::{BitAccess, OptionExt};
use bellpepper_core::{
  num::AllocatedNum,
  {ConstraintSystem, LinearCombination, SynthesisError, Variable},
};
use byteorder::WriteBytesExt;
use ff::PrimeField;
use num_bigint::{BigInt, Sign};
use std::convert::From;
use std::io::{self, Write};
use std::ops::Add;
use bellpepper::gadgets::Assignment;
use bellpepper_core::boolean::{AllocatedBit, Boolean};

#[derive(Clone)]
/// A representation of a bit
pub struct Bit<Scalar: PrimeField> {
  /// The linear combination which constrain the value of the bit
  pub bit: LinearCombination<Scalar>,
  /// The value of the bit (filled at witness-time)
  pub value: Option<bool>,
}

#[derive(Clone)]
/// A representation of a bit-vector
pub struct Bitvector<Scalar: PrimeField> {
  /// The linear combination which constrain the values of the bits
  pub bits: Vec<LinearCombination<Scalar>>,
  /// The value of the bits (filled at witness-time)
  pub values: Option<Vec<bool>>,
  /// Allocated bit variables
  pub allocations: Vec<Bit<Scalar>>,
}

impl<Scalar: PrimeField> Bit<Scalar> {
  /// Allocate a variable in the constraint system which can only be a
  /// boolean value.
  pub fn alloc<CS>(mut cs: CS, value: Option<bool>) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<Scalar>,
  {
    let var = cs.alloc(
      || "boolean",
      || {
        if *value.grab()? {
          Ok(Scalar::ONE)
        } else {
          Ok(Scalar::ZERO)
        }
      },
    )?;

    // Constrain: (1 - a) * a = 0
    // This constrains a to be either 0 or 1.
    cs.enforce(
      || "boolean constraint",
      |lc| lc + CS::one() - var,
      |lc| lc + var,
      |lc| lc,
    );

    Ok(Self {
      bit: LinearCombination::zero() + var,
      value,
    })
  }
}

pub struct Num<Scalar: PrimeField> {
  pub num: LinearCombination<Scalar>,
  pub value: Option<Scalar>,
}

impl<Scalar: PrimeField> Add for Num<Scalar> {
  type Output = Num<Scalar>;

  fn add(self, rhs: Self) -> Self::Output {
    let num = self.num + &rhs.num;
    let value = match (self.value, rhs.value) {
      (Some(v1), Some(v2)) => {
        let mut tmp = v1;
        tmp.add_assign(&v2);
        Some(tmp)
      }
      (Some(v), None) | (None, Some(v)) => Some(v),
      (None, None) => None,
    };

    Self { value, num }
  }
}

impl<Scalar: PrimeField> Add<&AllocatedNum<Scalar>> for Num<Scalar> {
  type Output = Num<Scalar>;

  fn add(self, rhs: &AllocatedNum<Scalar>) -> Self::Output {
    let num = self.num + rhs.get_variable();
    let value = match (self.value, rhs.get_value()) {
      (Some(v1), Some(v2)) => {
        let mut tmp = v1;
        tmp.add_assign(&v2);
        Some(tmp)
      }
      (Some(v), None) | (None, Some(v)) => Some(v),
      (None, None) => None,
    };

    Self { value, num }
  }
}

impl<Scalar: PrimeField> Num<Scalar> {
  pub fn zero() -> Self {
    Self { value: Some(Scalar::ZERO), num: LinearCombination::default() }
  }

  pub const fn new(value: Option<Scalar>, num: LinearCombination<Scalar>) -> Self {
    Self { value, num }
  }

  pub fn add_bool_with_coeff(self, one: Variable, bit: &Boolean, coeff: Scalar) -> Self {
    let newval = match (self.value, bit.get_value()) {
      (Some(mut curval), Some(bval)) => {
        if bval {
          curval.add_assign(&coeff);
        }

        Some(curval)
      }
      _ => None,
    };

    Num {
      value: newval,
      num: self.num + &bit.lc(one, coeff),
    }
  }

  pub fn alloc<CS, F>(mut cs: CS, value: F) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<Scalar>,
    F: FnOnce() -> Result<Scalar, SynthesisError>,
  {
    let mut new_value = None;
    let var = cs.alloc(
      || "num",
      || {
        let tmp = value()?;

        new_value = Some(tmp);

        Ok(tmp)
      },
    )?;

    Ok(Num {
      value: new_value,
      num: LinearCombination::zero() + var,
    })
  }

  pub fn fits_in_bits<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    n_bits: usize,
  ) -> Result<(), SynthesisError> {
    let v = self.value;

    // Allocate all but the first bit.
    let bits: Vec<Variable> = (1..n_bits)
      .map(|i| {
        cs.alloc(
          || format!("bit {i}"),
          || {
            let r = if *v.grab()?.get_bit(i).grab()? {
              Scalar::ONE
            } else {
              Scalar::ZERO
            };
            Ok(r)
          },
        )
      })
      .collect::<Result<_, _>>()?;

    for (i, v) in bits.iter().enumerate() {
      cs.enforce(
        || format!("{i} is bit"),
        |lc| lc + *v,
        |lc| lc + CS::one() - *v,
        |lc| lc,
      )
    }

    // Last bit
    cs.enforce(
      || "last bit",
      |mut lc| {
        let mut f = Scalar::ONE;
        lc = lc + &self.num;
        for v in bits.iter() {
          f = f.double();
          lc = lc - (f, *v);
        }
        lc
      },
      |mut lc| {
        lc = lc + CS::one();
        let mut f = Scalar::ONE;
        lc = lc - &self.num;
        for v in bits.iter() {
          f = f.double();
          lc = lc + (f, *v);
        }
        lc
      },
      |lc| lc,
    );
    Ok(())
  }

  /// Computes the natural number represented by an array of bits.
  /// Checks if the natural number equals `self`
  pub fn is_equal<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    other: &Bitvector<Scalar>,
  ) -> Result<(), SynthesisError> {
    let allocations = other.allocations.clone();
    let mut f = Scalar::ONE;
    let sum = allocations
      .iter()
      .fold(LinearCombination::zero(), |lc, bit| {
        let l = lc + (f, &bit.bit);
        f = f.double();
        l
      });
    let sum_lc = LinearCombination::zero() + &self.num - &sum;
    cs.enforce(|| "sum", |lc| lc + &sum_lc, |lc| lc + CS::one(), |lc| lc);
    Ok(())
  }

  pub fn equal<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    other: &Self,
  ) -> Result<AllocatedBit, SynthesisError> {
    let r_value = match (self.value, other.value) {
      (Some(a), Some(b)) => Some(a == b),
      _ => None,
    };

    let r = AllocatedBit::alloc(cs.namespace(|| "r"), r_value)?;

    let t = AllocatedNum::alloc(cs.namespace(|| "t"), || {
      Ok(if *self.value.get()? == *other.value.get()? {
        Scalar::ONE
      } else {
        (*self.value.get()? - *other.value.get()?)
            .invert()
            .unwrap()
      })
    })?;

    cs.enforce(
      || "t*(a - b) = 1 - r",
      |lc| lc + t.get_variable(),
      |lc| lc + &self.num - &other.num,
      |lc| lc + CS::one() - r.get_variable(),
    );

    cs.enforce(
      || "r*(a - b) = 0",
      |lc| lc + r.get_variable(),
      |lc| lc + &self.num - &other.num,
      |lc| lc,
    );

    Ok(r)
  }

  /// Compute the natural number represented by an array of limbs.
  /// The limbs are assumed to be based the `limb_width` power of 2.
  /// Low-index bits are low-order
  pub fn decompose<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
    n_bits: usize,
  ) -> Result<Bitvector<Scalar>, SynthesisError> {
    let values: Option<Vec<bool>> = self.value.as_ref().map(|v| {
      let num = *v;
      (0..n_bits).map(|i| num.get_bit(i).unwrap()).collect()
    });
    let allocations: Vec<Bit<Scalar>> = (0..n_bits)
      .map(|bit_i| {
        Bit::alloc(
          cs.namespace(|| format!("bit{bit_i}")),
          values.as_ref().map(|vs| vs[bit_i]),
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    let mut f = Scalar::ONE;
    let sum = allocations
      .iter()
      .fold(LinearCombination::zero(), |lc, bit| {
        let l = lc + (f, &bit.bit);
        f = f.double();
        l
      });
    let sum_lc = LinearCombination::zero() + &self.num - &sum;
    cs.enforce(|| "sum", |lc| lc + &sum_lc, |lc| lc + CS::one(), |lc| lc);
    let bits: Vec<LinearCombination<Scalar>> = allocations
      .clone()
      .into_iter()
      .map(|a| LinearCombination::zero() + &a.bit)
      .collect();
    Ok(Bitvector {
      allocations,
      values,
      bits,
    })
  }

  pub fn as_allocated_num<CS: ConstraintSystem<Scalar>>(
    &self,
    mut cs: CS,
  ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let new = AllocatedNum::alloc(cs.namespace(|| "alloc"), || Ok(*self.value.grab()?))?;
    cs.enforce(
      || "eq",
      |lc| lc,
      |lc| lc,
      |lc| lc + new.get_variable() - &self.num,
    );
    Ok(new)
  }
}

impl<Scalar: PrimeField> From<AllocatedNum<Scalar>> for Num<Scalar> {
  fn from(a: AllocatedNum<Scalar>) -> Self {
    Self::new(a.get_value(), LinearCombination::zero() + a.get_variable())
  }
}

impl<Scalar: PrimeField> From<&AllocatedNum<Scalar>> for Num<Scalar> {
  fn from(a: &AllocatedNum<Scalar>) -> Self {
    Self::new(a.get_value(), LinearCombination::zero() + a.get_variable())
  }
}

pub fn as_allocated_num<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
  mut cs: CS,
  num: bellpepper_core::num::Num<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError> {
  let new = AllocatedNum::alloc(
    cs.namespace(|| "alloc num"),
    || Ok(*num.get_value().grab()?)
  )?;
  cs.enforce(
    || "constraints new num",
    |_lc| num.lc(Scalar::ONE),
    |lc| lc + CS::one(),
    |lc| lc + new.get_variable(),
  );
  Ok(new)
}

fn write_be<F: PrimeField, W: Write>(f: &F, mut writer: W) -> io::Result<()> {
  for digit in f.to_repr().as_ref().iter().rev() {
    writer.write_u8(*digit)?;
  }

  Ok(())
}

/// Convert a field element to a natural number
pub fn f_to_nat<Scalar: PrimeField>(f: &Scalar) -> BigInt {
  let mut s = Vec::new();
  write_be(f, &mut s).unwrap(); // f.to_repr().write_be(&mut s).unwrap();
  BigInt::from_bytes_le(Sign::Plus, f.to_repr().as_ref())
}

/// Convert a natural number to a field element.
/// Returns `None` if the number is too big for the field.
pub fn nat_to_f<Scalar: PrimeField>(n: &BigInt) -> Option<Scalar> {
  Scalar::from_str_vartime(&format!("{n}"))
}
