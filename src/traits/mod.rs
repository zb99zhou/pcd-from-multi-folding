//! This module defines various traits required by the users of the library to implement.
use crate::errors::NovaError;
use bellpepper_core::{boolean::AllocatedBit, num::AllocatedNum, ConstraintSystem, SynthesisError};
use core::{
  fmt::Debug,
  ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};

pub mod commitment;

use commitment::CommitmentEngineTrait;

/// Represents an element of a group
/// This is currently tailored for an elliptic curve group
pub trait Group:
  Clone
  + Copy
  + Debug
  + Eq
  + GroupOps
  + GroupOpsOwned
  + ScalarMul<<Self as Group>::Scalar>
  + ScalarMulOwned<<Self as Group>::Scalar>
  + Send
  + Sync
  + Serialize
  + for<'de> Deserialize<'de>
{
  /// A type representing an element of the base field of the group
  type Base: PrimeFieldExt + PrimeFieldBits + TranscriptReprTrait<Self> + Serialize + for<'de> Deserialize<'de>;

  /// A type representing an element of the scalar field of the group
  type Scalar: PrimeFieldBits
    + PrimeFieldExt
    + Send
    + Sync
    + TranscriptReprTrait<Self>
    + Serialize
    + for<'de> Deserialize<'de>;

  /// A type representing the compressed version of the group element
  type CompressedGroupElement: CompressedGroup<GroupElement = Self>;

  /// A type representing preprocessed group element
  type PreprocessedGroupElement: Clone + Debug + Send + Sync + Serialize + for<'de> Deserialize<'de>;

  /// A type that represents a circuit-friendly sponge that consumes elements
  /// from the base field and squeezes out elements of the scalar field
  type RO: ROTrait<Self::Base, Self::Scalar>;

  /// An alternate implementation of `Self::RO` in the circuit model
  type ROCircuit: ROCircuitTrait<Self::Base>;

  /// A type that provides a generic Fiat-Shamir transcript to be used when externalizing proofs
  type TE: TranscriptEngineTrait<Self>;

  /// An alternate implementation of `Self::TE` in the circuit model
  type TECircuit: TranscriptCircuitEngineTrait<Self>;

  /// A type that provides a generic Fiat-Shamir transcript to be used when externalizing proofs
  type TE1: TranscriptEngineTrait<Self>;

  /// A type that defines a commitment engine over scalars in the group
  type CE: CommitmentEngineTrait<Self>;

  /// A method to compute a multiexponentation
  fn vartime_multiscalar_mul(
    scalars: &[Self::Scalar],
    bases: &[Self::PreprocessedGroupElement],
  ) -> Self;

  /// Compresses the group element
  fn compress(&self) -> Self::CompressedGroupElement;

  /// Produces a preprocessed element
  fn preprocessed(&self) -> Self::PreprocessedGroupElement;

  /// Produce a vector of group elements using a static label
  fn from_label(label: &'static [u8], n: usize) -> Vec<Self::PreprocessedGroupElement>;

  /// Returns the affine coordinates (x, y, infinty) for the point
  fn to_coordinates(&self) -> (Self::Base, Self::Base, bool);

  /// Returns an element that is the additive identity of the group
  fn zero() -> Self;

  /// Returns the generator of the group
  fn get_generator() -> Self;

  /// Returns A, B, and the order of the group as a big integer
  fn get_curve_params() -> (Self::Base, Self::Base, BigInt);
}

/// Represents a compressed version of a group element
pub trait CompressedGroup:
  Clone
  + Copy
  + Debug
  + Eq
  + Send
  + Sync
  + TranscriptReprTrait<Self::GroupElement>
  + Serialize
  + for<'de> Deserialize<'de>
  + 'static
{
  /// A type that holds the decompressed version of the compressed group element
  type GroupElement: Group;

  /// Decompresses the compressed group element
  fn decompress(&self) -> Option<Self::GroupElement>;
}

/// A helper trait to absorb different objects in RO
pub trait AbsorbInROTrait<G: Group> {
  /// Absorbs the value in the provided RO
  fn absorb_in_ro(&self, ro: &mut G::RO);

  /// Absorbs the value in the provided RO
  fn absorb_in_g2_ro<G2: Group<Base = <G as Group>::Scalar>>(&self, _ro: &mut G2::RO) {
    unimplemented!()
  }
}

/// A helper trait that defines the behavior of a hash function that we use as an RO
pub trait ROTrait<Base: PrimeFieldBits, Scalar> {
  /// The circuit alter ego of this trait impl - this constrains it to use the same constants
  type CircuitRO: ROCircuitTrait<Base, Constants = Self::Constants>;

  /// A type representing constants/parameters associated with the hash function
  type Constants: Default + Clone + Send + Sync + Serialize + for<'de> Deserialize<'de>;

  /// Initializes the hash function
  fn new(constants: Self::Constants, num_absorbs: usize) -> Self;

  /// Adds bytes to the internal state
  fn absorb_bytes<T: AsRef<[u8]>>(&mut self, bytes: T);

  /// Adds a scalar to the internal state
  fn absorb(&mut self, e: Base);

  /// Returns a challenge of `num_bits` by hashing the internal state
  fn squeeze(&mut self, num_bits: usize) -> Scalar;

  /// Returns a challenge of `num_bits` by hashing the bytes
  fn absorb_bytes_and_squeeze<T: AsRef<[u8]>>(&mut self, bytes: T, num_bits: usize) -> Scalar;

  /// Returns a set of challenges of length `len` and element size `num_bits`.
  fn batch_squeeze<T: AsRef<[u8]>>(&mut self, bytes: T, len: usize, num_bits: usize) -> Vec<Scalar>;
}

/// A helper trait that defines the behavior of a hash function that we use as an RO in the circuit model
pub trait ROCircuitTrait<Base: PrimeFieldBits> {
  /// the vanilla alter ego of this trait - this constrains it to use the same constants
  type NativeRO<T: PrimeFieldBits>: ROTrait<Base, T, Constants = Self::Constants>;

  /// A type representing constants/parameters associated with the hash function on this Base field
  type Constants: Default + Clone + Send + Sync + Serialize + for<'de> Deserialize<'de>;

  /// Initializes the hash function
  fn new(constants: Self::Constants, num_absorbs: usize) -> Self;

  /// Adds bytes to the internal state
  fn absorb_bytes<CS: ConstraintSystem<Base>, T: AsRef<[u8]>>(&mut self, cs: CS, bytes: T) -> Result<(), SynthesisError>;

  /// Adds a scalar to the internal state
  fn absorb(&mut self, e: &AllocatedNum<Base>);

  /// Returns a challenge of `num_bits` by hashing the internal state
  fn squeeze<CS>(&mut self, cs: CS, num_bits: usize) -> Result<Vec<AllocatedBit>, SynthesisError>
  where
    CS: ConstraintSystem<Base>;

  /// Returns a challenge of `num_bits` by hashing the bytes
  fn absorb_bytes_and_squeeze<CS, T: AsRef<[u8]>>(&mut self, cs: CS, bytes: T, num_bits: usize) -> Result<Vec<AllocatedBit>, SynthesisError>
    where
      CS: ConstraintSystem<Base>;

  /// Returns a set of challenges of length `len` and element size `num_bits`.
  fn batch_squeeze<CS, T: AsRef<[u8]>>(&mut self, cs: CS, bytes: T, len: usize, num_bits: usize) -> Result<Vec<Vec<AllocatedBit>>, SynthesisError>
    where
        CS: ConstraintSystem<Base>;
}

/// An alias for constants associated with G::RO
pub type ROConstants<G> =
  <<G as Group>::RO as ROTrait<<G as Group>::Base, <G as Group>::Scalar>>::Constants;

/// An alias for constants associated with `G::ROCircuit`
pub type ROConstantsCircuit<G> =
  <<G as Group>::ROCircuit as ROCircuitTrait<<G as Group>::Base>>::Constants;

/// An alias for constants associated with `G::TE`
pub type TEConstants<G> =
  <<G as Group>::TE as TranscriptEngineTrait<G>>::Constants;

/// An alias for constants associated with `G::TECircuit`
pub type TEConstantsCircuit<G> =
  <<G as Group>::TECircuit as TranscriptCircuitEngineTrait<G>>::Constants;

/// A helper trait for types with a group operation.
pub trait GroupOps<Rhs = Self, Output = Self>:
  Add<Rhs, Output = Output> + Sub<Rhs, Output = Output> + AddAssign<Rhs> + SubAssign<Rhs>
{
}

impl<T, Rhs, Output> GroupOps<Rhs, Output> for T where
  T: Add<Rhs, Output = Output> + Sub<Rhs, Output = Output> + AddAssign<Rhs> + SubAssign<Rhs>
{
}

/// A helper trait for references with a group operation.
pub trait GroupOpsOwned<Rhs = Self, Output = Self>: for<'r> GroupOps<&'r Rhs, Output> {}
impl<T, Rhs, Output> GroupOpsOwned<Rhs, Output> for T where T: for<'r> GroupOps<&'r Rhs, Output> {}

/// A helper trait for types implementing group scalar multiplication.
pub trait ScalarMul<Rhs, Output = Self>: Mul<Rhs, Output = Output> + MulAssign<Rhs> {}

impl<T, Rhs, Output> ScalarMul<Rhs, Output> for T where T: Mul<Rhs, Output = Output> + MulAssign<Rhs>
{}

/// A helper trait for references implementing group scalar multiplication.
pub trait ScalarMulOwned<Rhs, Output = Self>: for<'r> ScalarMul<&'r Rhs, Output> {}
impl<T, Rhs, Output> ScalarMulOwned<Rhs, Output> for T where T: for<'r> ScalarMul<&'r Rhs, Output> {}

/// This trait allows types to implement how they want to be added to `TranscriptEngine`
pub trait TranscriptReprTrait<G: Group>: Send + Sync {
  /// returns a byte representation of self to be added to the transcript
  fn to_transcript_bytes(&self) -> Vec<u8>{
    unimplemented!()
  }

  /// returns a scalar representation of self to be added to the transcript
  fn to_transcript_scalars(&self) -> Vec<G::Scalar> {
    unimplemented!()
  }

  /// returns a circuit allocated number representation of self to be added to the transcript
  fn to_transcript_nums<CS: ConstraintSystem<G::Base>>(&self, _cs: CS) -> Result<Vec<AllocatedNum<G::Base>>, SynthesisError> {
    unimplemented!()
  }
}

/// This trait defines the behavior of a transcript engine compatible with Spartan
pub trait TranscriptEngineTrait<G: Group>: Send + Sync {
  /// A type representing constants/parameters associated with the hash function
  type Constants: Default + Clone + Send + Sync + Serialize + for<'de> Deserialize<'de>;

  /// initializes the transcript
  fn new(constants: Self::Constants, label: &'static [u8]) -> Self;

  /// returns a scalar element of the group as a challenge
  fn squeeze(&mut self, label: &'static [u8]) -> Result<G::Scalar, NovaError>;

  /// returns a scalar element of the group as a challenge
  fn batch_squeeze(&mut self, label: &'static [u8], len: usize) -> Result<Vec<G::Scalar>, NovaError>;

  /// absorbs any type that implements `TranscriptReprTrait` under a label
  fn absorb<T: TranscriptReprTrait<G>>(&mut self, label: &'static [u8], o: &T);

  /// adds a domain separator
  fn dom_sep(&mut self, bytes: &'static [u8]);

  /// get last state
  fn get_last_state(&self) -> G::Scalar;
}

/// This trait defines the behavior of a transcript circuit engine compatible with Spartan
pub trait TranscriptCircuitEngineTrait<G: Group>: Send + Sync {
  /// A type representing constants/parameters associated with the hash function
  type Constants: Default + Clone + Send + Sync + Serialize + for<'de> Deserialize<'de>;

  /// initializes the transcript
  fn new<CS: ConstraintSystem<G::Base>>(constants: Self::Constants, cs: CS, label: &'static [u8]) -> Self;

  /// returns a AllocatedNumber as a challenge
  fn squeeze<CS: ConstraintSystem<G::Base>>(&mut self, cs: CS, label: &'static [u8]) -> Result<AllocatedNum<G::Base>, SynthesisError>;

  /// returns a AllocatedNumber as a challenge
  fn batch_squeeze<CS: ConstraintSystem<G::Base>>(&mut self, cs: CS, label: &'static [u8], len: usize) -> Result<Vec<AllocatedNum<G::Base>>, SynthesisError>;

  /// absorbs any type that implements `TranscriptReprTrait` under a label
  fn absorb<T: TranscriptReprTrait<G>, CS: ConstraintSystem<G::Base>>(&mut self, cs:CS, label: &'static [u8], o: &T) -> Result<(), SynthesisError>;

  /// adds a domain separator
  fn dom_sep<CS: ConstraintSystem<G::Base>>(&mut self, cs:CS, bytes: &'static [u8]) -> Result<(), SynthesisError>;
}

/// Defines additional methods on `PrimeField` objects
pub trait PrimeFieldExt: PrimeField {
  /// Returns a scalar representing the bytes
  fn from_uniform(bytes: &[u8]) -> Self;
}

impl<G: Group, T: TranscriptReprTrait<G>> TranscriptReprTrait<G> for &[T] {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    self
      .iter()
      .flat_map(|t| t.to_transcript_bytes())
      .collect::<Vec<u8>>()
  }

  fn to_transcript_scalars(&self) -> Vec<G::Scalar> {
    self
      .iter()
      .flat_map(|t| t.to_transcript_scalars())
      .collect()
  }
}

impl<G: Group> TranscriptReprTrait<G> for G {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    let (x, y, is_infinity) = self.to_coordinates();
    let is_infinity_byte = (!is_infinity).into();
    [
      x.to_transcript_bytes(),
      y.to_transcript_bytes(),
      [is_infinity_byte].to_vec(),
    ]
        .concat()
  }

  fn to_transcript_scalars(&self) -> Vec<G::Scalar> {
    let (x, y, is_infinity) = self.to_coordinates();
    let is_infinity_byte = (!is_infinity).into();
    vec![
      x.to_transcript_scalars(),
      y.to_transcript_scalars(),
      vec![G::Scalar::from_uniform(&[is_infinity_byte])],
    ]
        .concat()
  }
}

pub mod circuit;
pub mod evaluation;
pub mod snark;
