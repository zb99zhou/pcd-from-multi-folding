use crate::constants::NUM_HASH_BITS;
use crate::traits::commitment::{CommitmentEngineTrait, CommitmentTrait};
use crate::traits::Group;
use digest::Digest;
use ff::{Field, PrimeFieldBits};
use serde::Serialize;
use sha3::Sha3_256;

pub type CommitmentKey<G> = <<G as Group>::CE as CommitmentEngineTrait<G>>::CommitmentKey;
pub type Commitment<G> = <<G as Group>::CE as CommitmentEngineTrait<G>>::Commitment;
pub type CompressedCommitment<G> = <<<G as Group>::CE as CommitmentEngineTrait<G>>::Commitment as CommitmentTrait<G>>::CompressedCommitment;
pub type CE<G> = <G as Group>::CE;

pub fn compute_digest<G: Group, T: Serialize>(o: &T) -> G::Scalar {
  // obtain a vector of bytes representing public parameters
  let bytes = bincode::serialize(o).unwrap();
  // convert pp_bytes into a short digest
  let mut hasher = Sha3_256::new();
  hasher.update(&bytes);
  let digest = hasher.finalize();

  // truncate the digest to NUM_HASH_BITS bits
  let bv = (0..NUM_HASH_BITS).map(|i| {
    let (byte_pos, bit_pos) = (i / 8, i % 8);
    let bit = (digest[byte_pos] >> bit_pos) & 1;
    bit == 1
  });

  // turn the bit vector into a scalar
  let mut digest = G::Scalar::ZERO;
  let mut coeff = G::Scalar::ONE;
  for bit in bv {
    if bit {
      digest += coeff;
    }
    coeff += coeff;
  }
  digest
}

pub fn truncate_field_bits<F: PrimeFieldBits>(elt: F, num_bits: usize) -> F {
  let bits = elt.to_le_bits();
  let mut res = F::ZERO;
  let mut coeff = F::ONE;
  for bit in bits[0..num_bits].into_iter() {
    if *bit {
      res += coeff;
    }
    coeff += coeff;
  }
  res
}
