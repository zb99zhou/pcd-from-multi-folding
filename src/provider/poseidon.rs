//! Poseidon Constants and Poseidon-based RO used in Nova
use crate::traits::{Group, PrimeFieldExt, ROCircuitTrait, ROTrait, TranscriptCircuitEngineTrait, TranscriptEngineTrait, TranscriptReprTrait};
use bellpepper_core::{
  boolean::{AllocatedBit, Boolean},
  num::AllocatedNum,
  ConstraintSystem, SynthesisError,
};
use core::marker::PhantomData;
use ff::{PrimeField, PrimeFieldBits};
use generic_array::typenum::U24;
use neptune::{
  circuit2::Elt,
  poseidon::PoseidonConstants,
  sponge::{
    api::{IOPattern, SpongeAPI, SpongeOp},
    circuit::SpongeCircuit,
    vanilla::{Mode::Simplex, Sponge, SpongeTrait},
  },
  Strength,
};
use serde::{Deserialize, Serialize};
use crate::constants::NUM_HASH_BITS;
use crate::errors::NovaError;
use crate::gadgets::utils::{le_bits_to_num, base_as_scalar};
use crate::utils::truncate_field_bits;

const LENGTH: usize = 32;

/// All Poseidon Constants that are used in Nova
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PoseidonConstantsCircuit<Base: PrimeField>(PoseidonConstants<Base, U24>);

impl<Base: PrimeField> Default for PoseidonConstantsCircuit<Base> {
  /// Generate Poseidon constants
  fn default() -> Self {
    Self(Sponge::<Base, U24>::api_constants(Strength::Standard))
  }
}

/// A Poseidon-based RO to use outside circuits
#[derive(Serialize, Deserialize)]
pub struct PoseidonRO<Base, Scalar>
where
  Base: PrimeFieldBits,
  Scalar: PrimeFieldBits,
{
  // Internal State
  state: Vec<Base>,
  constants: PoseidonConstantsCircuit<Base>,
  num_absorbs: usize,
  squeezed: bool,
  _p: PhantomData<Scalar>,
}

impl<Base, Scalar> ROTrait<Base, Scalar> for PoseidonRO<Base, Scalar>
where
  Base: PrimeFieldExt + PrimeFieldBits + Serialize + for<'de> Deserialize<'de>,
  Scalar: PrimeFieldBits,
{
  type CircuitRO = PoseidonROCircuit<Base>;
  type Constants = PoseidonConstantsCircuit<Base>;

  fn new(constants: PoseidonConstantsCircuit<Base>, _num_absorbs: usize) -> Self {
    Self {
      state: Vec::new(),
      constants,
      num_absorbs: 0,
      squeezed: false,
      _p: PhantomData,
    }
  }

  /// Absorb a new number into the state of the oracle
  fn absorb_bytes<T: AsRef<[u8]>>(&mut self, bytes: T) {
    let e = Base::from_uniform(bytes.as_ref());
    self.state.push(e);
    self.num_absorbs += 1;
  }

  /// Absorb a new number into the state of the oracle
  fn absorb(&mut self, e: Base) {
    self.state.push(e);
    self.num_absorbs += 1;
  }

  /// Compute a challenge by hashing the current state
  fn squeeze(&mut self, num_bits: usize) -> Scalar {
    self.squeezed = true;

    let mut sponge = Sponge::new_with_constants(&self.constants.0, Simplex);
    let acc = &mut ();
    let parameter = IOPattern(vec![
      SpongeOp::Absorb(self.num_absorbs as u32),
      SpongeOp::Squeeze(1u32),
    ]);

    sponge.start(parameter, None, acc);
    assert_eq!(self.num_absorbs, self.state.len());
    SpongeAPI::absorb(&mut sponge, self.num_absorbs as u32, &self.state, acc);
    let hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
    sponge.finish(acc).unwrap();

    base_as_scalar(truncate_field_bits(hash[0], num_bits))
  }

  fn absorb_bytes_and_squeeze<T: AsRef<[u8]>>(&mut self, bytes: T, num_bits: usize) -> Scalar {
    let e = Base::from_uniform(bytes.as_ref());
    self.absorb(e);
    self.squeeze(num_bits)
  }

  fn batch_squeeze<T: AsRef<[u8]>>(&mut self, bytes: T, len: usize, num_bits: usize) -> Vec<Scalar> {
    (0..len).map(|_| self.absorb_bytes_and_squeeze(bytes.as_ref(), num_bits)).collect()
  }
}

/// A Poseidon-based RO gadget to use inside the verifier circuit.
#[derive(Serialize, Deserialize)]
pub struct PoseidonROCircuit<Base>
where
  Base: PrimeField,
{
  // Internal state
  state: Vec<AllocatedNum<Base>>,
  constants: PoseidonConstantsCircuit<Base>,
  num_absorbs: usize,
  squeezed: bool,
}

impl<Base> ROCircuitTrait<Base> for PoseidonROCircuit<Base>
where
  Base: PrimeFieldExt + PrimeFieldBits + Serialize + for<'de> Deserialize<'de>,
{
  type NativeRO<T: PrimeFieldBits> = PoseidonRO<Base, T>;
  type Constants = PoseidonConstantsCircuit<Base>;

  /// Initialize the internal state and set the poseidon constants
  fn new(constants: PoseidonConstantsCircuit<Base>, num_absorbs: usize) -> Self {
    Self {
      state: Vec::new(),
      constants,
      num_absorbs,
      squeezed: false,
    }
  }

  /// Absorb a new number into the state of the oracle
  fn absorb_bytes<CS: ConstraintSystem<Base>, T: AsRef<[u8]>>(&mut self, mut cs: CS, bytes: T) -> Result<(), SynthesisError>{
    let bytes_scalar = Base::from_uniform(bytes.as_ref());
    let num = AllocatedNum::alloc(
      cs.namespace(|| "absorb bytes"),
      || Ok(bytes_scalar)
    )?;
    cs.enforce(
      || "enforce bytes",
      |lc| lc + num.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + (bytes_scalar, CS::one()),
    );
    self.state.push(num);
    self.num_absorbs += 1;
    Ok(())
  }

  /// Absorb a new number into the state of the oracle
  fn absorb(&mut self, e: &AllocatedNum<Base>) {
    self.state.push(e.clone());
    self.num_absorbs += 1;
  }

  /// Compute a challenge by hashing the current state
  fn squeeze<CS>(
    &mut self,
    mut cs: CS,
    num_bits: usize,
  ) -> Result<Vec<AllocatedBit>, SynthesisError>
  where
    CS: ConstraintSystem<Base>,
  {
    self.squeezed = true;
    let parameter = IOPattern(vec![
      SpongeOp::Absorb(self.num_absorbs as u32),
      SpongeOp::Squeeze(1u32),
    ]);
    let mut ns = cs.namespace(|| "ns");

    let hash = {
      let mut sponge = SpongeCircuit::new_with_constants(&self.constants.0, Simplex);
      let acc = &mut ns;
      assert_eq!(self.num_absorbs, self.state.len());

      sponge.start(parameter, None, acc);
      neptune::sponge::api::SpongeAPI::absorb(
        &mut sponge,
        self.num_absorbs as u32,
        &(0..self.state.len())
          .map(|i| Elt::Allocated(self.state[i].clone()))
          .collect::<Vec<Elt<Base>>>(),
        acc,
      );

      let output = neptune::sponge::api::SpongeAPI::squeeze(&mut sponge, 1, acc);
      sponge.finish(acc).unwrap();
      output
    };

    let hash = Elt::ensure_allocated(&hash[0], &mut ns.namespace(|| "ensure allocated"), true)?;

    // return the hash as a vector of bits, truncated
    Ok(
      hash
        .to_bits_le_strict(ns.namespace(|| "poseidon hash to boolean"))?
        .iter()
        .map(|boolean| match boolean {
          Boolean::Is(ref x) => x.clone(),
          _ => panic!("Wrong type of input. We should have never reached there"),
        })
        .collect::<Vec<AllocatedBit>>()[..num_bits]
        .into(),
    )
  }

  fn absorb_bytes_and_squeeze<CS, T: AsRef<[u8]>>(&mut self, mut cs: CS, bytes: T, num_bits: usize) -> Result<Vec<AllocatedBit>, SynthesisError> where CS: ConstraintSystem<Base> {
    // assert!(bytes.as_ref().len() <= LENGTH);
    // let mut input = [0u8; LENGTH];
    // input[0..bytes.len()].copy_from_slice(bytes.as_ref());
    let bytes = AllocatedNum::alloc(
      cs.namespace(|| "absorb bytes"),
      || Ok(Base::from_uniform(bytes.as_ref()))
    )?;
    self.absorb(&bytes);
    self.squeeze(cs.namespace(|| "absorb bytes and squeeze"), num_bits)
  }

  fn batch_squeeze<CS, T: AsRef<[u8]>>(&mut self, mut cs: CS, bytes: T, len: usize, num_bits: usize) -> Result<Vec<Vec<AllocatedBit>>, SynthesisError> where CS: ConstraintSystem<Base> {
    (0..len).map(|i|
        self.absorb_bytes_and_squeeze(cs.namespace(||format!("{}th squeeze", i)), bytes.as_ref(), num_bits)
    ).collect()
  }
}

const POSEIDON_STATE_SIZE: u32 = 1;
const PERSONA_TAG: &[u8] = b"NoTR";
const DOM_SEP_TAG: &[u8] = b"NoDS";

/// Provides an implementation of `TranscriptEngine`
#[derive(Debug, Clone)]
pub struct PoseidonTranscript<G: Group> {
  round: u16,
  state: Vec<G::Scalar>,
  constants: PoseidonConstantsCircuit<G::Scalar>,
  _p: PhantomData<G>,
}

impl<G: Group> TranscriptEngineTrait<G> for PoseidonTranscript<G> {
  type Constants = PoseidonConstantsCircuit<G::Scalar>;

  fn new(constants: Self::Constants, label: &'static [u8]) -> Self {
    let input = vec![G::Scalar::from_uniform(PERSONA_TAG), G::Scalar::from_uniform(label)];

    Self {
      round: 0u16,
      state: input,
      constants,
      _p: Default::default(),
    }
  }

  fn squeeze(&mut self, label: &'static [u8]) -> Result<G::Scalar, NovaError> {
    // we gather the full input from the round, preceded by the current state of the transcript
    let input = [
      vec![G::Scalar::from_uniform(DOM_SEP_TAG)],
      vec![G::Scalar::from_uniform(self.round.to_le_bytes().as_ref())],
      self.state.clone(),
      vec![G::Scalar::from_uniform(label)],
    ]
        .concat();

    let acc = &mut ();
    let parameter = IOPattern(vec![
      SpongeOp::Absorb(input.len() as u32),
      SpongeOp::Squeeze(1u32),
    ]);

    let mut sponge = Sponge::new_with_constants(&self.constants.0, Simplex);
    sponge.start(parameter, None, acc);
    SpongeAPI::absorb(&mut sponge, input.len() as u32, &input, acc);
    let output = SpongeAPI::squeeze(&mut sponge, POSEIDON_STATE_SIZE, acc);
    sponge.finish(acc).unwrap();
    let hash = truncate_field_bits(output[0], NUM_HASH_BITS);

    // update state
    self.round = self.round.checked_add(1).unwrap();
    self.state = vec![hash];

    // squeeze out a challenge
    Ok(hash)
  }

  fn batch_squeeze(&mut self, label: &'static [u8], len: usize) -> Result<Vec<G::Scalar>, NovaError> {
    (0..len).map(|_| self.squeeze(label)).collect()
  }

  fn absorb<T: TranscriptReprTrait<G>>(&mut self, label: &'static [u8], o: &T) {
    self.state.push(G::Scalar::from_uniform(label));
    for bytes in o.to_transcript_scalars() {
      self.state.push(bytes);
    }
  }

  fn dom_sep(&mut self, bytes: &'static [u8]) {
    self.state.push(G::Scalar::from_uniform(DOM_SEP_TAG));
    self.state.push(G::Scalar::from_uniform(bytes));
  }

  fn get_last_state(&self) -> G::Scalar {
    *self.state.first().unwrap()
  }
}

/// A Poseidon-based Transcript gadget to use inside the verifier circuit.
#[derive(Serialize, Deserialize)]
pub struct PoseidonTranscriptCircuit<G: Group>{
  // Internal state
  round: u16,
  state: Vec<AllocatedNum<G::Base>>,
  constants: PoseidonConstantsCircuit<G::Base>,
  _p: PhantomData<G>,
}

impl<G: Group> TranscriptCircuitEngineTrait<G> for PoseidonTranscriptCircuit<G> {
  type Constants = PoseidonConstantsCircuit<G::Base>;

  fn new<CS: ConstraintSystem<G::Base>>(constants: Self::Constants, mut cs: CS, label: &'static [u8]) -> Self {
    let input = vec![
      AllocatedNum::alloc(cs.namespace(|| "alloc PERSONA_TAG"), || Ok(G::Base::from_uniform(PERSONA_TAG))).unwrap(),
      AllocatedNum::alloc(cs.namespace(|| "alloc labe"), || Ok(G::Base::from_uniform(label))).unwrap()
    ];

    Self {
      round: 0u16,
      state: input,
      constants,
      _p: Default::default(),
    }
  }

  fn squeeze<CS: ConstraintSystem<G::Base>>(&mut self, mut cs: CS, label: &'static [u8]) -> Result<AllocatedNum<G::Base>, SynthesisError> {
    // we gather the full input from the round, preceded by the current state of the transcript
    let input = [
      vec![AllocatedNum::alloc(cs.namespace(|| "alloc dom_sep_tag"), || Ok(G::Base::from_uniform(DOM_SEP_TAG)))?],
      vec![AllocatedNum::alloc(cs.namespace(|| "alloc round"), || Ok(G::Base::from_uniform(self.round.to_le_bytes().as_ref())))?],
      self.state.clone(),
      vec![AllocatedNum::alloc(cs.namespace(|| "alloc label"), || Ok(G::Base::from_uniform(label)))?],
    ]
        .concat();

    let parameter = IOPattern(vec![
      SpongeOp::Absorb(input.len() as u32),
      SpongeOp::Squeeze(1u32),
    ]);
    let mut ns = cs.namespace(|| "ns");

    let hash = {
      let mut sponge = SpongeCircuit::new_with_constants(&self.constants.0, Simplex);
      let acc = &mut ns;

      sponge.start(parameter, None, acc);
      neptune::sponge::api::SpongeAPI::absorb(
        &mut sponge,
        input.len() as u32,
        &(0..input.len())
            .map(|i| Elt::Allocated(input[i].clone()))
            .collect::<Vec<Elt<G::Base>>>(),
        acc,
      );

      let output = neptune::sponge::api::SpongeAPI::squeeze(&mut sponge, POSEIDON_STATE_SIZE, acc);
      sponge.finish(acc).unwrap();
      output
    };

    let output = Elt::ensure_allocated(&hash[0], &mut ns.namespace(|| "ensure allocated"), true)?;
    let output_bits = output
        .to_bits_le_strict(ns.namespace(|| "poseidon transcript hash to boolean"))?
        .iter()
        .map(|boolean| match boolean {
          Boolean::Is(ref x) => x.clone(),
          _ => panic!("Wrong type of input. We should have never reached there"),
        })
        .collect::<Vec<AllocatedBit>>();
    let truncated_output = le_bits_to_num(ns.namespace(|| "bits to hash"), &output_bits[..NUM_HASH_BITS])?;

    // update state
    self.round = self.round.checked_add(1).unwrap();
    self.state = vec![truncated_output.clone()];

    // squeeze out a challenge
    Ok(truncated_output)
  }

  fn batch_squeeze<CS: ConstraintSystem<G::Base>>(
    &mut self,
    mut cs: CS,
    label: &'static [u8],
    len: usize
  ) -> Result<Vec<AllocatedNum<G::Base>>, SynthesisError> {
    (0..len).map(|i| self.squeeze(cs.namespace(|| format!("{}th squeeze", i)), label)).collect()
  }

  fn absorb<T: TranscriptReprTrait<G>, CS: ConstraintSystem<G::Base>>(&mut self, mut cs: CS, label: &'static [u8], o: &T)  -> Result<(), SynthesisError> {
    let label_num = AllocatedNum::alloc(cs.namespace(|| "alloc label"), || Ok(G::Base::from_uniform(label)))?;
    self.state.push(label_num);
    for struct_num in o.to_transcript_nums(cs)? {
      self.state.push(struct_num);
    }
    Ok(())
  }

  fn dom_sep<CS: ConstraintSystem<G::Base>>(&mut self, mut cs: CS, bytes: &'static [u8])  -> Result<(), SynthesisError> {
    let tag_num = AllocatedNum::alloc(cs.namespace(|| "alloc label"), || Ok(G::Base::from_uniform(DOM_SEP_TAG)))?;
    let bytes_num = AllocatedNum::alloc(cs.namespace(|| "alloc bytes"), || Ok(G::Base::from_uniform(bytes)))?;
    self.state.push(tag_num);
    self.state.push(bytes_num);
    Ok(())
  }
}
//
// #[cfg(test)]
// mod tests {
//   use super::*;
//   use crate::provider::{bn256_grumpkin::bn256, secp_secq};
//   use crate::{
//     bellpepper::solver::SatisfyingAssignment, constants::NUM_CHALLENGE_BITS,
//     gadgets::utils::le_bits_to_num, traits::Group,
//   };
//   use ff::Field;
//   use rand::rngs::OsRng;
//
//   fn test_poseidon_ro_with<G: Group>()
//   where
//     // we can print the field elements we get from G's Base & Base fields,
//     // and compare their byte representations
//     <<G as Group>::Base as PrimeField>::Repr: std::fmt::Debug,
//     <<G as Group>::Base as PrimeField>::Repr: std::fmt::Debug,
//     <<G as Group>::Base as PrimeField>::Repr: PartialEq<<<G as Group>::Base as PrimeField>::Repr>,
//   {
//     // Check that the number computed inside the circuit is equal to the number computed outside the circuit
//     let mut csprng: OsRng = OsRng;
//     let constants = PoseidonConstantsCircuit::<G::Base>::default();
//     let num_absorbs = 32;
//     let mut ro: PoseidonRO<G::Base, G::Base> = PoseidonRO::new(constants.clone(), num_absorbs);
//     let mut ro_gadget: PoseidonROCircuit<G::Base> =
//       PoseidonROCircuit::new(constants, num_absorbs);
//     let mut cs: SatisfyingAssignment<G> = SatisfyingAssignment::new();
//     for i in 0..num_absorbs {
//       let num = G::Base::random(&mut csprng);
//       ro.absorb(num);
//       let num_gadget =
//         AllocatedNum::alloc(cs.namespace(|| format!("data {i}")), || Ok(num)).unwrap();
//       num_gadget
//         .inputize(&mut cs.namespace(|| format!("input {i}")))
//         .unwrap();
//       ro_gadget.absorb(&num_gadget);
//     }
//     let num = ro.squeeze(NUM_CHALLENGE_BITS);
//     let num2_bits = ro_gadget.squeeze(&mut cs, NUM_CHALLENGE_BITS).unwrap();
//     let num2 = le_bits_to_num(&mut cs, &num2_bits).unwrap();
//     assert_eq!(num.to_repr(), num2.get_value().unwrap().to_repr());
//   }
//
//   #[test]
//   fn test_poseidon_ro() {
//     test_poseidon_ro_with::<pasta_curves::pallas::Point>();
//     test_poseidon_ro_with::<bn256::Point>();
//     test_poseidon_ro_with::<secp_secq::secp256k1::Point>();
//     test_poseidon_ro_with::<secp_secq::secq256k1::Point>();
//   }
// }
