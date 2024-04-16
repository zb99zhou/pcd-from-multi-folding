use bellpepper::gadgets::Assignment;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::{AllocatedNum, Num};
use ff::PrimeField;

use crate::gadgets::ext_allocated_num::ExtendFunc;
use crate::gadgets::nonnative::util::as_allocated_num;
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::espresso::sum_check::verifier::u64_factorial;
use crate::nimfs::espresso::virtual_polynomial::VPAuxInfo;
use crate::nimfs::multifolding::NIMFSProof;
use crate::traits::{Group, TranscriptCircuitEngineTrait, TranscriptReprTrait};

pub struct AllocatedProof<G: Group> {
    pub sum_check_proof: AllocatedIOPProof<G>,
    pub sigmas: Vec<Vec<AllocatedNum<G::Base>>>,
    pub thetas: Vec<Vec<AllocatedNum<G::Base>>>,
}

impl<G: Group> AllocatedProof<G> {
    pub fn from_witness<CS: ConstraintSystem<G::Base>, const R: usize>(mut cs: CS, proof_witness: Option<&NIMFSProof<G>>) -> Result<Self, SynthesisError> {
        let default_ccs = CCS::<G>::default_r1cs();
        let point = (0..default_ccs.s)
            .map(|i| {
                AllocatedNum::alloc(
                    cs.namespace(|| format!("alloc {i}th point")),
                    || proof_witness.get().map(|n| n.point[i])
                )
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;
        let mut proofs = Vec::new();
        for i in 0..default_ccs.s {
            proofs.push(AllocatedIOPProverMessage {
                evaluations: (0..default_ccs.d + 2)
                    .map(|j|AllocatedNum::alloc(
                        cs.namespace(|| format!("alloc {i}-{j}th sigmas")),
                        || proof_witness.get().map(|n| n.proofs[i][j])
                    ))
                    .collect::<Result<Vec<_>, SynthesisError>>()?
            });
        }
        let sigmas = (0..R)
            .map(|i|
                (0..default_ccs.t)
                    .map(|j|AllocatedNum::alloc(
                        cs.namespace(|| format!("alloc {i}-{j}th sigmas")),
                        || proof_witness.get().map(|n| n.sigmas[i][j])
                    ))
                    .collect::<Result<Vec<_>, SynthesisError>>()
            )
            .collect::<Result<Vec<_>, SynthesisError>>()?;
        let thetas = (0..R)
            .map(|i|
                (0..default_ccs.t)
                    .map(|j|AllocatedNum::alloc(
                        cs.namespace(|| format!("alloc {i}-{j}th thetas")),
                        || proof_witness.get().map(|n| n.thetas[i][j])
                    ))
                    .collect::<Result<Vec<_>, SynthesisError>>()
            )
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(Self {
            sum_check_proof: AllocatedIOPProof { point, proofs },
            sigmas,
            thetas,
        })
    }
}

pub struct AllocatedIOPProof<C: Group> {
    pub point: Vec<AllocatedNum<C::Base>>,
    pub proofs: Vec<AllocatedIOPProverMessage<C>>,
}

pub struct AllocatedIOPProverMessage<C: Group> {
    pub(crate) evaluations: Vec<AllocatedNum<C::Base>>,
}

impl<C: Group> TranscriptReprTrait<C> for  AllocatedIOPProverMessage<C> {
    fn to_transcript_nums<CS: ConstraintSystem<C::Base>>(&self, _cs: CS) -> Result<Vec<AllocatedNum<C::Base>>, SynthesisError> {
        Ok(self.evaluations.clone())
    }
}

pub struct AllocatedIOPVerifierState<G: Group> {
    pub(crate) round: usize,
    pub(crate) num_vars: usize,
    pub(crate) max_degree: usize,
    pub(crate) finished: bool,
    /// a list storing the univariate polynomial in evaluation form sent by the
    /// prover at each round
    pub(crate) polynomials_received: Vec<Vec<AllocatedNum<G::Base>>>,
    /// a list storing the randomness sampled by the verifier at each round
    pub(crate) challenges: Vec<AllocatedNum<G::Base>>,
}

pub struct AllocatedSumCheckSubClaim<G: Group> {
    /// the multi-dimensional point that this multilinear extension is evaluated
    /// to
    pub point: Vec<AllocatedNum<G::Base>>,
    /// the expected evaluation
    pub expected_evaluation: AllocatedNum<G::Base>,
}

impl<G: Group> AllocatedIOPVerifierState<G> {
    fn verifier_init(index_info: &VPAuxInfo<G::Base>) -> Self {
        let res = Self {
            round: 1,
            num_vars: index_info.num_variables,
            max_degree: index_info.max_degree,
            finished: false,
            polynomials_received: Vec::with_capacity(index_info.num_variables),
            challenges: Vec::with_capacity(index_info.num_variables),
        };
        res
    }

    fn verify_round_and_update_state<CS: ConstraintSystem<<G as Group>::Base>>(
        &mut self,
        mut cs: CS,
        prover_msg: &AllocatedIOPProverMessage<G>,
        transcript: &mut G::TECircuit,
    ) -> Result<AllocatedNum<G::Base>, SynthesisError> {
        assert!(!self.finished);

        // In an interactive protocol, the verifier should
        //
        // 1. check if the received 'P(0) + P(1) = expected`.
        // 2. set `expected` to P(r)`
        //
        // When we turn the protocol to a non-interactive one, it is sufficient to defer
        // such checks to `check_and_generate_subclaim` after the last round.

        let challenge = transcript.squeeze(
            cs.namespace(|| "calc challenge"),
            b"Internal round",
        )?;
        self.challenges.push(challenge.clone());
        self.polynomials_received
            .push(prover_msg.evaluations.to_vec());

        if self.round == self.num_vars {
            // accept and close
            self.finished = true;
        } else {
            // proceed to the next round
            self.round += 1;
        }

        Ok(challenge)
    }

    fn check_and_generate_subclaim<CS: ConstraintSystem<<G as Group>::Base>>(
        &mut self,
        mut cs: CS,
        asserted_sum: &AllocatedNum<G::Base>,
    ) -> Result<AllocatedSumCheckSubClaim<G>, SynthesisError> {
        assert!(self.finished);
        assert_eq!(self.polynomials_received.len(), self.num_vars);

        // the deferred check during the interactive phase:
        // 2. set `expected` to P(r)`
        let mut expected_vec = self
            .polynomials_received
            .iter()
            .zip(self.challenges.iter())
            .enumerate()
            .map(|(i, (evaluations, challenge))| {
                assert_eq!(evaluations.len(), self.max_degree + 1);
                enforce_interpolate_uni_poly(cs.namespace(|| format!("{i}th interpolate")), challenge, evaluations)
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        // insert the asserted_sum to the first position of the expected vector
        expected_vec.insert(0, asserted_sum.clone());

        for (evaluations, expected) in self
            .polynomials_received
            .iter()
            .zip(expected_vec.iter())
            .take(self.num_vars)
        {
            // the deferred check during the interactive phase:
            // 1. check if the received 'P(0) + P(1) = expected`.
            cs.enforce(
                || "Prover message must be consistent with the claim",
                |lc| lc + evaluations[0].get_variable() + evaluations[1].get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + expected.get_variable(),
            );
        }
        Ok(AllocatedSumCheckSubClaim {
            point: self.challenges.clone(),
            // the last expected value (not checked within this function) will be included in the
            // subclaim
            expected_evaluation: expected_vec[self.num_vars].clone(),
        })
    }
}

pub fn sumcheck_verify<CS: ConstraintSystem<<G as Group>::Base>, G: Group>(
    mut cs: CS,
    claimed_sum: &AllocatedNum<G::Base>,
    proof: &AllocatedIOPProof<G>,
    aux_info: &VPAuxInfo<G::Base>,
    transcript: &mut G::TECircuit,
) -> Result<AllocatedSumCheckSubClaim<G>, SynthesisError> {
    transcript.absorb(cs.namespace(|| "absorb num_variables"), b"aux info", aux_info)?;

    let mut verifier_state = AllocatedIOPVerifierState::verifier_init(aux_info);
    for i in 0..aux_info.num_variables {
        let prover_msg = proof.proofs.get(i).expect("proof is incomplete");
        transcript.absorb(cs.namespace(|| format!("{i}th round absorbing")), b"prover msg", prover_msg)?;
        verifier_state.verify_round_and_update_state(
            cs.namespace(|| format!("verify {i}th round and update state")),
            prover_msg,
            transcript,
        )?;
    }

    verifier_state.check_and_generate_subclaim(cs.namespace(|| "check_and_generate_subclaim"), &claimed_sum)
}

#[allow(clippy::too_many_arguments)]
pub fn enforce_compute_c_from_sigmas_and_thetas<CS: ConstraintSystem<<G as Group>::Base>, G, G1>(
    mut cs: CS,
    ccs_params: &CCS<G1>,
    vec_sigmas: &[Vec<AllocatedNum<G::Base>>],
    vec_thetas: &[Vec<AllocatedNum<G::Base>>],
    gamma: AllocatedNum<G::Base>,
    beta: &[AllocatedNum<G::Base>],
    vec_r_x: Vec<Vec<AllocatedNum<G::Base>>>,
    r_x_prime: &[AllocatedNum<G::Base>],
) -> Result<AllocatedNum<G::Base>, SynthesisError>
    where
        G: Group<Base = <G1 as Group>::Scalar>,
        G1: Group<Base = <G as Group>::Scalar>,
{
    let mut c_lc = Num::zero();

    let mut e_lcccs = Vec::new();
    for (i, r_x) in vec_r_x.into_iter().enumerate() {
        e_lcccs.push(enforce_eq_eval(
            cs.namespace(|| format!("{}th r_x", i)),
            &r_x,
            r_x_prime
        )?);
    }
    for (i, sigmas) in vec_sigmas.iter().enumerate() {
        // (sum gamma^j * e_i * sigma_j)
        for (j, sigma_j) in sigmas.iter().enumerate() {
            let mut cs = cs.namespace(|| format!("sigma_{i}_{j}"));
            let gamma_j = gamma.pow_constant(cs.namespace(|| "gamma_j"), i * ccs_params.t + j)?;
            let acc = gamma_j.mul(
                cs.namespace(|| "gamma_j * e_lcccs[i]"),
                &e_lcccs[i]
            )?.mul(
                cs.namespace(|| "gamma_j * e_lcccs[i] * sigma_j"),
                &sigma_j
            )?;
            c_lc = c_lc.add(&Num::from(acc));
        }
    }

    let mu = vec_sigmas.len();
    let e2 = enforce_eq_eval(cs.namespace(|| "alloc e2"), beta, r_x_prime)?;
    for (k, thetas) in vec_thetas.iter().enumerate() {
        let mut cs = cs.namespace(|| format!("theta_{k}"));
        // + gamma^{t+1} * e2 * sum c_i * prod theta_j
        let mut lhs = Num::zero();
        for i in 0..ccs_params.q {
            let mut prod = AllocatedNum::one(cs.namespace(|| format!("alloc {i}th one")))?;
            for j in ccs_params.S[i].clone() {
                prod = prod.mul(
                    cs.namespace(|| format!("prod * thetas[{j}]")),
                    &thetas[j]
                )?;
            }
            lhs = lhs.add(&Num::from(prod).scale(ccs_params.c[i]));
        }
        let gamma_t1 = gamma.pow_constant(cs.namespace(|| "gamma_t1"), mu * ccs_params.t + k)?;
        let acc = gamma_t1.mul(
            cs.namespace(|| "gamma_t1 * e2"),
            &e2
        )?.mul_lc(
            cs.namespace(|| "gamma_t1 * e2 * lhs"),
            lhs
        )?;
        c_lc = c_lc.add(&Num::from(acc));
    }

    let final_c = as_allocated_num(cs.namespace(|| "alloc final_c"), c_lc)?;
    Ok(final_c)
}

pub fn enforce_interpolate_uni_poly<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    eval_at: &AllocatedNum<F>,
    p_i: &[AllocatedNum<F>],
) -> Result<AllocatedNum<F>, SynthesisError> {
    let len = p_i.len();
    assert!(len <= 20);

    let mut prod = eval_at.clone();
    let mut evals = vec![];
    evals.push(eval_at.clone());

    // `prod = \prod_{j} (eval_at - j)`
    for j in 1..len {
        let mut cs = cs.namespace(|| format!("product {}th", j));

        let allocated_j = F::from(j as u64);
        let eval_at_sub_j = eval_at.sub_constant(
            cs.namespace(|| "eval_at - j"),
            allocated_j
        )?;

        prod = prod.mul(cs.namespace(|| "calc new product"), &eval_at_sub_j)?;
        evals.push(eval_at_sub_j);
    }

    let last_denominator = F::from(u64_factorial(len - 1));
    let mut ratio_numerator = 1i64;
    let mut ratio_denominator = 1u64;

    let mut res_lc = Num::zero();
    for i in (0..len).rev() {
        let mut cs = cs.namespace(|| format!("res {}th", i));

        let ratio_numerator_f = if ratio_numerator < 0 {
            -F::from((-ratio_numerator) as u64)
        } else {
            F::from(ratio_numerator as u64)
        };

        // res += p_i[i] * prod * G::Base::from(ratio_denominator)
        //     * (last_denominator * ratio_numerator_f * evals[i]).invert().unwrap();
        let scale = last_denominator * ratio_numerator_f;
        let inv_part = evals[i].invert_with_scale(
            cs.namespace(|| "(last_denominator * ratio_numerator_f * evals[i]).invert()"),
            scale
        )?;
        let res = p_i[i]
            .mul_with_scale(cs.namespace(|| "p_i[i] * prod"), &prod, F::from(ratio_denominator))?
            .mul(cs.namespace(|| "calc final result"), &inv_part)?;
        res_lc = res_lc.add(&Num::from(res));

        // compute denom for the next step is current_denom * (len-i)/i
        if i != 0 {
            ratio_numerator *= -(len as i64 - i as i64);
            ratio_denominator *= i as u64;
        }
    }

    let final_res = AllocatedNum::alloc(
        cs.namespace(|| "alloc tmp"),
        || res_lc.get_value().get().copied()
    )?;
    cs.enforce(
        || "constraints tmp = self - constant",
        |_lc| res_lc.lc(F::ONE),
        |lc| lc + CS::one(),
        |lc| lc + final_res.get_variable(),
    );
    Ok(final_res)
}

/// Evaluate eq polynomial.
pub fn enforce_eq_eval<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    x: &[AllocatedNum<F>],
    y: &[AllocatedNum<F>]
) -> Result<AllocatedNum<F>, SynthesisError> {
    assert_eq!(x.len(), y.len());
    
    let mut res = AllocatedNum::alloc(cs.namespace(|| "alloc one"), || Ok(F::ONE))?;
    for (i, (xi, yi)) in x.iter().zip(y.iter()).enumerate() {
        let mut cs = cs.namespace(||format!("calc {}th eq eval", i));
        let xi_yi = xi.mul(cs.namespace(|| "xi * yi"), yi)?;
        
        // res *= xi_yi + xi_yi - xi - yi + F::ONE;
        let lc = Num::from(xi_yi).scale(F::from(2))
            .add(&Num::from(xi.clone()).scale(-F::ONE))
            .add(&Num::from(yi.clone()).scale(-F::ONE))
            .add_bool_with_coeff(CS::one(), &Boolean::Constant(true), F::ONE);
        res = res.mul_lc(
            cs.namespace(|| "update eq eval result"),
            lc
        )?;
    }
    
    Ok(res)
}