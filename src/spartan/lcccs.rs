//! This module implements `RelaxedR1CSSNARKTrait` using Spartan that is generic
//! over the polynomial commitment and evaluation argument (i.e., a PCS)
//! This version of Spartan does not use preprocessing so the verifier keeps the entire
//! description of R1CS matrices. This is essentially optimal for the verifier when using
//! an IPA-based polynomial commitment scheme.

use crate::{
    compute_digest,
    errors::NovaError,
    spartan::{
        polys::{eq::EqPolynomial, multilinear::MultiLinearPolynomial, multilinear::SparsePolynomial},
        powers,
        sumcheck::SumcheckProof,
        PolyEvalInstance, PolyEvalWitness,
    },
    traits::{
        evaluation::EvaluationEngineTrait, Group, TranscriptEngineTrait,
    },
    Commitment, CommitmentKey,
};
use ff::Field;

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use crate::nimfs::ccs::cccs::Witness;
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::util::vec::Matrix;
use crate::traits::snark::LinearCommittedCCSTrait;

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

/// A succinct proof of knowledge of a witness to a relaxed R1CS instance
/// The proof is produced using Spartan's combination of the sum-check and
/// the commitment to a vector viewed as a polynomial commitment
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct LCCCSSNARK<G: Group, EE: EvaluationEngineTrait<G>> {
    sc_proof_outer: SumcheckProof<G>,
    claims_outer: (G::Scalar, G::Scalar, G::Scalar),
    sc_proof_inner: SumcheckProof<G>,
    eval_W: G::Scalar,
    sc_proof_batch: SumcheckProof<G>,
    evals_batch: Vec<G::Scalar>,
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
            S: S.clone(),
            vk_digest: vk.digest,
        };

        Ok((pk, vk))
    }

    /// produces a succinct proof of satisfiability of a `RelaxedR1CS` instance
    fn prove(
        ck: &CommitmentKey<G>,
        pk: &Self::ProverKey,
        U: &LCCCS<G>,
        W: &Witness<G>,
    ) -> Result<Self, NovaError> {
        // let W = W.pad(&pk.S); // pad the witness
        let mut transcript = G::TE::new(Default::default(), b"LCCCSSNARK");

        // sanity check that R1CSShape has certain size characteristics
        // pk.S.check_regular_shape();

        // append the digest of vk (which includes R1CS matrices) and the RelaxedR1CSInstance to the transcript
        transcript.absorb(b"vk", &pk.vk_digest);
        transcript.absorb(b"U", U);

        // compute the full satisfying assignment by concatenating W.W, U.u, and U.X
        let mut z = [W.w.clone(), vec![U.u], U.x.clone()].concat();

        let (num_rounds_x, num_rounds_y) = (
            usize::try_from(pk.S.m.ilog2()).unwrap(),
            (usize::try_from(pk.S.n.ilog2()).unwrap() + 1),
        );

        // outer sum-check
        let tau = (0..num_rounds_x)
            .map(|_i| transcript.squeeze(b"t"))
            .collect::<Result<Vec<G::Scalar>, NovaError>>()?;

        let mut poly_tau = MultiLinearPolynomial::new(EqPolynomial::new(tau).evals());
        let (mut poly_Az, mut poly_Bz, mut poly_Cz) = {
            let (poly_Az, poly_Bz, poly_Cz) = pk.S.multiply_vec(&z)?;
            (
                MultiLinearPolynomial::new(poly_Az),
                MultiLinearPolynomial::new(poly_Bz),
                MultiLinearPolynomial::new(poly_Cz),
            )
        };

        let comb_func_outer =
            |poly_A_comp: &G::Scalar,
             poly_B_comp: &G::Scalar,
             poly_C_comp: &G::Scalar,
             poly_D_comp: &G::Scalar|
             -> G::Scalar { *poly_A_comp * (*poly_B_comp * *poly_C_comp - *poly_D_comp) };
        let (sc_proof_outer, r_x, claims_outer) = SumcheckProof::prove_cubic_with_additive_term(
            &G::Scalar::ZERO, // claim is zero
            num_rounds_x,
            &mut poly_tau,
            &mut poly_Az,
            &mut poly_Bz,
            &mut poly_Cz,
            comb_func_outer,
            &mut transcript,
        )?;

        // claims from the end of sum-check
        let (claim_Az, claim_Bz): (G::Scalar, G::Scalar) = (claims_outer[1], claims_outer[2]);
        let claim_Cz = poly_Cz.evaluate(&r_x);
        transcript.absorb(
            b"claims_outer",
            &[claim_Az, claim_Bz, claim_Cz].as_slice(),
        );

        // inner sum-check
        let r = transcript.squeeze(b"r")?;
        let claim_inner_joint = claim_Az + r * claim_Bz + r * r * claim_Cz;

        let poly_ABC = {
            // compute the initial evaluation table for R(\tau, x)
            let evals_rx = EqPolynomial::new(r_x.clone()).evals();

            // Bounds "row" variables of (A, B, C) matrices viewed as 2d multilinear polynomials
            let compute_eval_table_sparse =
                |S: &CCS<G>, rx: &[G::Scalar]| -> (Vec<G::Scalar>, Vec<G::Scalar>, Vec<G::Scalar>) {
                    assert_eq!(rx.len(), S.m);

                    let inner = |M: &Matrix<G::Scalar>, M_evals: &mut Vec<G::Scalar>| {
                        for (row, cols) in M.iter().enumerate() {
                            for (col, val) in cols.iter().enumerate() {
                                M_evals[col] += rx[row] * val;
                            }
                        }
                    };

                    let (A_evals, (B_evals, C_evals)) = rayon::join(
                        || {
                            let mut M0_evals: Vec<G::Scalar> = vec![G::Scalar::ZERO; 2 * S.n];
                            inner(&S.M[0], &mut M0_evals);
                            M0_evals
                        },
                        || {
                            rayon::join(
                                || {
                                    let mut M1_evals: Vec<G::Scalar> = vec![G::Scalar::ZERO; 2 * S.n];
                                    inner(&S.M[1], &mut M1_evals);
                                    M1_evals
                                },
                                || {
                                    let mut M2_evals: Vec<G::Scalar> = vec![G::Scalar::ZERO; 2 * S.n];
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
            z.resize(pk.S.n * 2, G::Scalar::ZERO);
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
        )?;

        // add additional claims about W and E polynomials to the list from CC
        let mut w_u_vec = Vec::new();
        let eval_W = MultiLinearPolynomial::evaluate_with(&W.w, &r_y[1..]);
        w_u_vec.push((
            PolyEvalWitness { p: W.w.clone() },
            PolyEvalInstance {
                c: U.C,
                x: r_y[1..].to_vec(),
                e: eval_W,
            },
        ));


        // We will now reduce a vector of claims of evaluations at different points into claims about them at the same point.
        // For example, eval_W =? W(r_y[1..]) and eval_E =? E(r_x) into
        // two claims: eval_W_prime =? W(rz) and eval_E_prime =? E(rz)
        // We can them combine the two into one: eval_W_prime + gamma * eval_E_prime =? (W + gamma*E)(rz),
        // where gamma is a public challenge
        // Since commitments to W and E are homomorphic, the verifier can compute a commitment
        // to the batched polynomial.
        assert!(w_u_vec.len() >= 2);

        let (w_vec, u_vec): (Vec<PolyEvalWitness<G>>, Vec<PolyEvalInstance<G>>) =
            w_u_vec.into_iter().unzip();
        let w_vec_padded = PolyEvalWitness::pad(&w_vec); // pad the polynomials to be of the same size
        let u_vec_padded = PolyEvalInstance::pad(&u_vec); // pad the evaluation points

        // generate a challenge
        let rho = transcript.squeeze(b"r")?;
        let num_claims = w_vec_padded.len();
        let powers_of_rho = powers::<G>(&rho, num_claims);
        let claim_batch_joint = u_vec_padded
            .iter()
            .zip(powers_of_rho.iter())
            .map(|(u, p)| u.e * p)
            .sum();

        let mut polys_left: Vec<MultiLinearPolynomial<G::Scalar>> = w_vec_padded
            .iter()
            .map(|w| MultiLinearPolynomial::new(w.p.clone()))
            .collect();
        let mut polys_right: Vec<MultiLinearPolynomial<G::Scalar>> = u_vec_padded
            .iter()
            .map(|u| MultiLinearPolynomial::new(EqPolynomial::new(u.x.clone()).evals()))
            .collect();

        let num_rounds_z = u_vec_padded[0].x.len();
        let comb_func = |poly_A_comp: &G::Scalar, poly_B_comp: &G::Scalar| -> G::Scalar {
            *poly_A_comp * *poly_B_comp
        };
        let (sc_proof_batch, r_z, claims_batch) = SumcheckProof::prove_quad_batch(
            &claim_batch_joint,
            num_rounds_z,
            &mut polys_left,
            &mut polys_right,
            &powers_of_rho,
            comb_func,
            &mut transcript,
        )?;

        let (claims_batch_left, _): (Vec<G::Scalar>, Vec<G::Scalar>) = claims_batch;

        transcript.absorb(b"l", &claims_batch_left.as_slice());

        // we now combine evaluation claims at the same point rz into one
        let gamma = transcript.squeeze(b"g")?;
        let powers_of_gamma: Vec<G::Scalar> = powers::<G>(&gamma, num_claims);
        let comm_joint = u_vec_padded
            .iter()
            .zip(powers_of_gamma.iter())
            .map(|(u, g_i)| u.c * *g_i)
            .fold(Commitment::<G>::default(), |acc, item| acc + item);
        let poly_joint = PolyEvalWitness::weighted_sum(&w_vec_padded, &powers_of_gamma);
        let eval_joint = claims_batch_left
            .iter()
            .zip(powers_of_gamma.iter())
            .map(|(e, g_i)| *e * *g_i)
            .sum();

        let eval_arg = EE::prove(
            ck,
            &pk.pk_ee,
            &mut transcript,
            &comm_joint,
            &poly_joint.p,
            &r_z,
            &eval_joint,
        )?;

        Ok(LCCCSSNARK {
            sc_proof_outer,
            claims_outer: (claim_Az, claim_Bz, claim_Cz),
            sc_proof_inner,
            eval_W,
            sc_proof_batch,
            evals_batch: claims_batch_left,
            eval_arg,
        })
    }

    /// verifies a proof of satisfiability of a `RelaxedR1CS` instance
    fn verify(&self, vk: &Self::VerifierKey, U: &LCCCS<G>) -> Result<(), NovaError> {
        let mut transcript = G::TE::new(Default::default(), b"LCCCSSNARK");

        // append the digest of R1CS matrices and the RelaxedR1CSInstance to the transcript
        transcript.absorb(b"vk", &vk.digest);
        transcript.absorb(b"U", U);

        let (num_rounds_x, num_rounds_y) = (
            usize::try_from(vk.S.m.ilog2()).unwrap(),
            (usize::try_from(vk.S.n.ilog2()).unwrap() + 1),
        );

        // outer sum-check
        let tau = (0..num_rounds_x)
            .map(|_i| transcript.squeeze(b"t"))
            .collect::<Result<Vec<G::Scalar>, NovaError>>()?;

        let (claim_outer_final, r_x) =
            self
                .sc_proof_outer
                .verify(G::Scalar::ZERO, num_rounds_x, 3, &mut transcript)?;

        // verify claim_outer_final
        let (claim_Az, claim_Bz, claim_Cz) = self.claims_outer;
        let taus_bound_rx = EqPolynomial::new(tau).evaluate(&r_x);
        let claim_outer_final_expected =
            taus_bound_rx * (claim_Az * claim_Bz - claim_Cz);
        if claim_outer_final != claim_outer_final_expected {
            return Err(NovaError::InvalidSumcheckProof);
        }

        transcript.absorb(
            b"claims_outer",
            &[
                self.claims_outer.0,
                self.claims_outer.1,
                self.claims_outer.2,
            ]
                .as_slice(),
        );

        // inner sum-check
        let r = transcript.squeeze(b"r")?;
        let claim_inner_joint =
            self.claims_outer.0 + r * self.claims_outer.1 + r * r * self.claims_outer.2;

        let (claim_inner_final, r_y) =
            self
                .sc_proof_inner
                .verify(claim_inner_joint, num_rounds_y, 2, &mut transcript)?;

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
                SparsePolynomial::new(usize::try_from(vk.S.n.ilog2()).unwrap(), poly_X)
                    .evaluate(&r_y[1..])
            };
            (G::Scalar::ONE - r_y[0]) * self.eval_W + r_y[0] * eval_X
        };

        // compute evaluations of R1CS matrices
        let multi_evaluate = |M_vec: &[&Matrix<G::Scalar>],
                              r_x: &[G::Scalar],
                              r_y: &[G::Scalar]|
                              -> Vec<G::Scalar> {
            let evaluate_with_table =
                |M: &Matrix<G::Scalar>, T_x: &[G::Scalar], T_y: &[G::Scalar]| -> G::Scalar {
                    M.par_iter()
                        .map(|row| {
                            row.iter()
                                .enumerate()
                                .filter(|(_, &val)| val.is_zero_vartime())
                                .map(|(col, &val)| T_x[row.len()] * T_y[col] * val)
                                .sum::<G::Scalar>()
                        })
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

        let evals = multi_evaluate(&[&vk.S.M[0], &vk.S.M[1], &vk.S.M[2]], &r_x, &r_y);

        let claim_inner_final_expected = (evals[0] + r * evals[1] + r * r * evals[2]) * eval_Z;
        if claim_inner_final != claim_inner_final_expected {
            return Err(NovaError::InvalidSumcheckProof);
        }

        // add claims about W and E polynomials
        let u_vec: Vec<PolyEvalInstance<G>> = vec![
            PolyEvalInstance {
                c: U.C,
                x: r_y[1..].to_vec(),
                e: self.eval_W,
            },
        ];

        let u_vec_padded = PolyEvalInstance::pad(&u_vec); // pad the evaluation points

        // generate a challenge
        let rho = transcript.squeeze(b"r")?;
        let num_claims = u_vec.len();
        let powers_of_rho = powers::<G>(&rho, num_claims);
        let claim_batch_joint = u_vec
            .iter()
            .zip(powers_of_rho.iter())
            .map(|(u, p)| u.e * p)
            .sum();

        let num_rounds_z = u_vec_padded[0].x.len();
        let (claim_batch_final, r_z) =
            self
                .sc_proof_batch
                .verify(claim_batch_joint, num_rounds_z, 2, &mut transcript)?;

        let claim_batch_final_expected = {
            let poly_rz = EqPolynomial::new(r_z.clone());
            let evals = u_vec_padded
                .iter()
                .map(|u| poly_rz.evaluate(&u.x))
                .collect::<Vec<G::Scalar>>();

            evals
                .iter()
                .zip(self.evals_batch.iter())
                .zip(powers_of_rho.iter())
                .map(|((e_i, p_i), rho_i)| *e_i * *p_i * rho_i)
                .sum()
        };

        if claim_batch_final != claim_batch_final_expected {
            return Err(NovaError::InvalidSumcheckProof);
        }

        transcript.absorb(b"l", &self.evals_batch.as_slice());

        // we now combine evaluation claims at the same point rz into one
        let gamma = transcript.squeeze(b"g")?;
        let powers_of_gamma: Vec<G::Scalar> = powers::<G>(&gamma, num_claims);
        let comm_joint = u_vec_padded
            .iter()
            .zip(powers_of_gamma.iter())
            .map(|(u, g_i)| u.c * *g_i)
            .fold(Commitment::<G>::default(), |acc, item| acc + item);
        let eval_joint = self
            .evals_batch
            .iter()
            .zip(powers_of_gamma.iter())
            .map(|(e, g_i)| *e * *g_i)
            .sum();

        // verify
        EE::verify(
            &vk.vk_ee,
            &mut transcript,
            &comm_joint,
            &r_z,
            &eval_joint,
            &self.eval_arg,
        )?;

        Ok(())
    }
}
