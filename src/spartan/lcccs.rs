//! This module implements `LinearCommittedCCSTrait` using Spartan that is generic
//! over the polynomial commitment and evaluation argument (i.e., a PCS)
//! This version of Spartan does not use preprocessing so the verifier keeps the entire
//! description of R1CS matrices. This is essentially optimal for the verifier when using
//! an IPA-based polynomial commitment scheme.

use crate::{
  compute_digest,
  errors::NovaError,
  spartan::{
    polys::{eq::EqPolynomial, multilinear::MultiLinearPolynomial, multilinear::SparsePolynomial},
    sumcheck::SumcheckProof,
    PolyEvalInstance, PolyEvalWitness,
  },
  traits::{evaluation::EvaluationEngineTrait, Group, TranscriptEngineTrait},
  CommitmentKey,
};
use ff::Field;

use crate::nimfs::ccs::cccs::CCSWitness;
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::util::spare_matrix::SparseMatrix;
use crate::traits::snark::LinearCommittedCCSTrait;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// A type that represents the prover's key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<G: Group, EE: EvaluationEngineTrait<G>> {
  pk_ee: EE::ProverKey,
  S: CCS<G>,
  vk_digest: G::Scalar, // digest of the verifier's key
}

/// A type that represents the verifier's key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct VerifierKey<G: Group, EE: EvaluationEngineTrait<G>> {
  vk_ee: EE::VerifierKey,
  S: CCS<G>,
  digest: G::Scalar,
}

/// A succinct proof of knowledge of a witness to a LCCCS instance
/// The proof is produced using Spartan's combination of the sum-check and
/// the commitment to a vector viewed as a polynomial commitment
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct LCCCSSNARK<G: Group, EE: EvaluationEngineTrait<G>> {
  sc_proof_inner: SumcheckProof<G>,
  eval_W: G::Scalar,
  eval_arg: EE::EvaluationArgument,
}

impl<G: Group, EE: EvaluationEngineTrait<G>> LinearCommittedCCSTrait<G> for LCCCSSNARK<G, EE> {
  type ProverKey = ProverKey<G, EE>;
  type VerifierKey = VerifierKey<G, EE>;

  fn setup(
    ck: &CommitmentKey<G>,
    S: &CCS<G>,
  ) -> Result<(Self::ProverKey, Self::VerifierKey), NovaError> {
    let (pk_ee, vk_ee) = EE::setup(ck);
    let S = S.pad();
    let vk = {
      let mut vk = VerifierKey {
        vk_ee,
        S: S.clone(),
        digest: G::Scalar::ZERO,
      };
      vk.digest = compute_digest::<G, VerifierKey<G, EE>>(&vk);
      vk
    };

    let pk = ProverKey {
      pk_ee,
      S,
      vk_digest: vk.digest,
    };

    Ok((pk, vk))
  }

  /// produces a succinct proof of satisfiability of a `LCCCS` instance
  fn prove(
    ck: &CommitmentKey<G>,
    pk: &Self::ProverKey,
    U: &LCCCS<G>,      //
    W: &CCSWitness<G>, //
  ) -> Result<Self, NovaError> {
    let W = W.pad(&pk.S); // pad the witness
    let mut transcript = G::TE1::new(Default::default(), b"LCCCSSNARK");

    // append the digest of vk (which includes LCCCS matrices) and the LCCCSInstance to the transcript
    transcript.absorb(b"vk", &pk.vk_digest);
    transcript.absorb(b"U", U);

    // compute the full satisfying assignment by concatenating W.W, U.u, and U.X
    let mut z = [W.w.clone(), vec![U.u], U.x.clone()].concat();

    let num_rounds_y = usize::try_from((pk.S.n - pk.S.l - 1).ilog2()).unwrap() + 1;
    let r_x = U.r_x.clone();

    // inner sum-check
    let r = transcript.squeeze(b"r").unwrap();

    let claim_inner_joint = U.v[0] + r * U.v[1] + r * r * U.v[2];

    let poly_ABC = {
      // compute the initial evaluation table for R(r_x, x)
      let evals_rx = EqPolynomial::new(r_x.clone()).evals();

      // Bounds "row" variables of (A, B, C) matrices viewed as 2d multilinear polynomials
      // Return {A(r_x,y)}_{y\in{0,1}^s'}, {B(r_x,y)}_{y\in{0,1}^s'}, {C(r_x,y)}_{y\in{0,1}^s'}
      let compute_eval_table_sparse =
        |S: &CCS<G>, rx: &[G::Scalar]| -> (Vec<G::Scalar>, Vec<G::Scalar>, Vec<G::Scalar>) {
          assert_eq!(rx.len(), S.m);

          let inner = |M: &SparseMatrix<G::Scalar>, M_evals: &mut Vec<G::Scalar>| {
            for (row, col, val) in M.iter() {
              // dbg!(row, col, val);
              M_evals[col] += rx[row] * val;
            }
          };

          let (A_evals, (B_evals, C_evals)) = rayon::join(
            || {
              let mut M0_evals: Vec<G::Scalar> = vec![G::Scalar::ZERO; 2 * (S.n - S.l - 1)];
              inner(&S.M[0], &mut M0_evals);
              M0_evals
            },
            || {
              rayon::join(
                || {
                  let mut M1_evals: Vec<G::Scalar> = vec![G::Scalar::ZERO; 2 * (S.n - S.l - 1)];
                  inner(&S.M[1], &mut M1_evals);
                  M1_evals
                },
                || {
                  let mut M2_evals: Vec<G::Scalar> = vec![G::Scalar::ZERO; 2 * (S.n - S.l - 1)];
                  inner(&S.M[2], &mut M2_evals);
                  M2_evals
                },
              )
            },
          );

          (A_evals, B_evals, C_evals)
        };

      let (evals_A, evals_B, evals_C) = compute_eval_table_sparse(&pk.S, &evals_rx);
      assert_eq!(evals_A.len(), evals_B.len());
      assert_eq!(evals_A.len(), evals_C.len());
      (0..evals_A.len())
        .into_par_iter()
        .map(|i| evals_A[i] + r * evals_B[i] + r * r * evals_C[i])
        .collect::<Vec<G::Scalar>>()
    };

    let poly_z = {
      z.resize((pk.S.n - pk.S.l - 1) * 2, G::Scalar::ZERO);
      z
    };

    let comb_func = |poly_A_comp: &G::Scalar, poly_B_comp: &G::Scalar| -> G::Scalar {
      *poly_A_comp * *poly_B_comp
    };
    let (sc_proof_inner, r_y, _claims_inner) = SumcheckProof::prove_quad(
      &claim_inner_joint,
      num_rounds_y,
      &mut MultiLinearPolynomial::new(poly_ABC),
      &mut MultiLinearPolynomial::new(poly_z),
      comb_func,
      &mut transcript,
    )
    .unwrap();

    // add additional claims about W polynomials to the list from CC
    let eval_W = MultiLinearPolynomial::evaluate_with(&W.w, &r_y[1..]);
    let (poly_w, poly_u): (PolyEvalWitness<G>, PolyEvalInstance<G>) = (
      PolyEvalWitness { p: W.w.clone() },
      PolyEvalInstance {
        c: U.C,
        x: r_y[1..].to_vec(),
        e: eval_W,
      },
    );

    let eval_arg = EE::prove(
      ck,
      &pk.pk_ee,
      &mut transcript,
      &poly_u.c,
      &poly_w.p,
      &poly_u.x,
      &poly_u.e,
    )
    .unwrap();

    Ok(LCCCSSNARK {
      sc_proof_inner,
      eval_W,
      eval_arg,
    })
  }

  /// verifies a proof of satisfiability of a `LCCCS` instance
  fn verify(&self, vk: &Self::VerifierKey, U: &LCCCS<G>) -> Result<(), NovaError> {
    let mut transcript = G::TE1::new(Default::default(), b"LCCCSSNARK");

    // append the digest of R1CS matrices and the RelaxedR1CSInstance to the transcript
    transcript.absorb(b"vk", &vk.digest);
    transcript.absorb(b"U", U);

    let num_rounds_y = usize::try_from((vk.S.n - vk.S.l - 1).ilog2()).unwrap() + 1;

    // inner sum-check
    let r = transcript.squeeze(b"r").unwrap();
    let claim_inner_joint = U.v[0] + r * U.v[1] + r * r * U.v[2];

    let (claim_inner_final, r_y) = self
      .sc_proof_inner
      .verify(claim_inner_joint, num_rounds_y, 2, &mut transcript)
      .unwrap();

    // verify claim_inner_final
    let eval_Z = {
      let eval_X = {
        // constant term
        let mut poly_X = vec![(0, U.u)];
        //remaining inputs
        poly_X.extend(
          (0..U.x.len())
            .map(|i| (i + 1, U.x[i]))
            .collect::<Vec<(usize, G::Scalar)>>(),
        );
        SparsePolynomial::new(
          usize::try_from((vk.S.n - vk.S.l - 1).ilog2()).unwrap(),
          poly_X,
        )
        .evaluate(&r_y[1..])
      };
      (G::Scalar::ONE - r_y[0]) * self.eval_W + r_y[0] * eval_X
    };

    // compute evaluations of R1CS matrices
    let multi_evaluate = |M_vec: &[&SparseMatrix<G::Scalar>],
                          r_x: &[G::Scalar],
                          r_y: &[G::Scalar]|
     -> Vec<G::Scalar> {
      let evaluate_with_table =
        |M: &SparseMatrix<G::Scalar>, T_x: &[G::Scalar], T_y: &[G::Scalar]| -> G::Scalar {
          M.iter()
            .map(|(row, col, val)| T_x[row] * T_y[col] * val)
            .sum()
        };

      let (T_x, T_y) = rayon::join(
        || EqPolynomial::new(r_x.to_vec()).evals(),
        || EqPolynomial::new(r_y.to_vec()).evals(),
      );

      (0..M_vec.len())
        .into_par_iter()
        .map(|i| evaluate_with_table(M_vec[i], &T_x, &T_y))
        .collect()
    };
    let r_x = U.r_x.clone();
    let evals = multi_evaluate(&[&vk.S.M[0], &vk.S.M[1], &vk.S.M[2]], &r_x, &r_y);

    let claim_inner_final_expected = (evals[0] + r * evals[1] + r * r * evals[2]) * eval_Z;

    // assert_eq!(claim_inner_final, claim_inner_final_expected);
    if claim_inner_final != claim_inner_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    // add claims about W polynomials
    let poly_u: PolyEvalInstance<G> = PolyEvalInstance {
      c: U.C,
      x: r_y[1..].to_vec(),
      e: self.eval_W,
    };

    EE::verify(
      &vk.vk_ee,
      &mut transcript,
      &poly_u.c,
      &poly_u.x,
      &poly_u.e,
      &self.eval_arg,
    )
    .unwrap();

    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::{Group, LinearCommittedCCSTrait, LCCCSSNARK};
  use crate::nimfs::ccs::ccs::test::{get_test_ccs, get_test_z};
  use crate::provider::ipa_pc::EvaluationEngine;
  use rand_core::OsRng;

  fn test_lcccs_with_compression_with<G: Group, LCCCS: LinearCommittedCCSTrait<G>>() {
    // Create a basic CCS circuit
    let ccs = get_test_ccs::<G>();
    let ck = ccs.commitment_key();

    // Generate a satisfying witness
    let z = get_test_z(3);

    // Create the LCCCS instance out of z
    let (running_instance, witness) = ccs.to_lcccs(OsRng, &ck, &z);

    // check the satisfiability of the generated LCCCS instance-witness tuple
    let _ = running_instance.check_relation(&ck, &witness);

    let (pk, vk) = LCCCS::setup(&ck, &ccs).unwrap();

    // produce a LCCCS SNARK
    let lcccs_nsark = LCCCS::prove(&ck, &pk, &running_instance, &witness).unwrap();

    // verify the LCCCS SNARK
    let res = lcccs_nsark.verify(&vk, &running_instance);
    assert!(res.is_ok());
  }

  #[test]
  fn test_lcccs_with_compression() {
    type G1 = pasta_curves::pallas::Point;
    test_lcccs_with_compression_with::<G1, LCCCSSNARK<G1, EvaluationEngine<G1>>>();
  }
}
