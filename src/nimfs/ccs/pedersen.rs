use crate::nimfs::util::vec::{vec_add, vec_scalar_mul};

use crate::traits::{Group, TranscriptEngineTrait};
use ff::Field;
use rand_core::RngCore;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct Proof<C: Group> {
  R: C,
  u_: Vec<C::Scalar>,
  ru_: C::Scalar,
}

#[derive(Clone, Debug)]
pub struct Params<C: Group> {
  pub(crate) h: C,
  pub generators: Vec<C::PreprocessedGroupElement>, // Affine for the MSM
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Commitment<C: Group>(pub C);

#[derive(Clone, Debug)]
pub struct Pedersen<C: Group> {
  _c: PhantomData<C>,
}

impl<C: Group> Pedersen<C> {
  pub fn new_params(rng: impl RngCore + Clone, max: usize) -> Params<C> {
    let h_scalar = C::Scalar::random(rng.clone());
    let g = C::get_generator();
    let generators: Vec<C::PreprocessedGroupElement> = (0..max)
      .map(|_| {
        let r = C::Scalar::random(rng.clone());
        g.mul(r).preprocessed()
      })
      .collect();
    Params {
      h: g.mul(h_scalar),
      generators,
    }
  }

  pub fn commit(
    params: &Params<C>,
    v: &[C::Scalar],
    r: &C::Scalar, // random value is provided, in order to be choosen by other parts of the protocol
  ) -> Commitment<C> {
    let msm = C::vartime_multiscalar_mul(v, &params.generators);

    let cm = params.h.mul(r) + msm;
    Commitment(cm)
  }

  pub fn prove(
    params: &Params<C>,
    transcript: &mut C::TE,
    cm: &Commitment<C>,
    v: &Vec<C::Scalar>,
    r: &C::Scalar,
  ) -> Proof<C> {
    let r1 = transcript.squeeze(b"r1").unwrap();
    let d = transcript.batch_squeeze(b"d", v.len()).unwrap();

    let msm = C::vartime_multiscalar_mul(&d, &params.generators);
    let R = params.h.mul(r1) + msm;

    transcript.absorb(b"cm", &cm.0);
    transcript.absorb(b"R", &R);
    let e = transcript.squeeze(b"e").unwrap();

    let u_ = vec_add(&vec_scalar_mul(v, &e), &d);
    let ru_ = e * r + r1;

    Proof { R, u_, ru_ }
  }
  pub fn verify(
    params: &Params<C>,
    transcript: &mut C::TE,
    cm: Commitment<C>,
    proof: Proof<C>,
  ) -> bool {
    // r1, d just to match Prover's transcript
    transcript.squeeze(b"r1").unwrap(); // r_1
    transcript.batch_squeeze(b"d", proof.u_.len()).unwrap(); // d

    transcript.absorb(b"cm", &cm.0);
    transcript.absorb(b"R", &proof.R);
    let e = transcript.squeeze(b"e").unwrap();
    let lhs = proof.R + cm.0.mul(e);

    let msm = C::vartime_multiscalar_mul(&proof.u_, &params.generators);
    let rhs = params.h.mul(proof.ru_) + msm;
    if lhs != rhs {
      return false;
    }
    true
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::provider::bn256_grumpkin::bn256;
  use crate::traits::TranscriptEngineTrait;
  use ff::Field;
  use rand_core::OsRng;

  #[test]
  fn test_pedersen_commitment() {
    const n: usize = 10;
    // setup params
    let params = Pedersen::new_params(OsRng, n);

    // init Prover's transcript
    let mut transcript_p = <bn256::Point as Group>::TE::new(Default::default(), b"pedersen_test");
    transcript_p.squeeze(b"init").unwrap();
    // init Verifier's transcript
    let mut transcript_v = <bn256::Point as Group>::TE::new(Default::default(), b"pedersen_test");
    transcript_v.squeeze(b"init").unwrap();

    let v: Vec<bn256::Scalar> = vec![bn256::Scalar::random(OsRng); n];
    let r: bn256::Scalar = bn256::Scalar::random(OsRng);

    let cm = Pedersen::<bn256::Point>::commit(&params, &v, &r);
    let proof = Pedersen::<bn256::Point>::prove(&params, &mut transcript_p, &cm, &v, &r);
    let v = Pedersen::<bn256::Point>::verify(&params, &mut transcript_v, cm, proof);
    assert!(v);
  }
}
