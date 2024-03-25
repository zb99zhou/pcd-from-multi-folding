use std::marker::PhantomData;
use std::ops::{Add, Mul};

use ff::Field;
use serde::{Deserialize, Serialize};

use crate::Commitment;
use crate::nimfs::ccs::cccs::{CCCS, CCSWitness};
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::ccs::util::compute_all_sum_Mz_evals;
use crate::nimfs::espresso::sum_check::{PolyIOP, SumCheck, verifier::interpolate_uni_poly};
use crate::nimfs::espresso::sum_check::structs::IOPProof as SumCheckProof;
use crate::nimfs::espresso::virtual_polynomial::{eq_eval, VirtualPolynomial, VPAuxInfo};
use crate::nimfs::util::hypercube::BooleanHypercube;
use crate::traits::{Group, TranscriptEngineTrait};
use crate::traits::commitment::CommitmentEngineTrait;

#[allow(clippy::upper_case_acronyms)]
pub type NIMFS<C> = MultiFolding<C>;
#[allow(clippy::upper_case_acronyms)]
pub type NIMFSProof<C> = ProofWitness<C>;

/// Proof defines a multi-folding proof
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProofWitness<C: Group> {
    pub point: Vec<C::Base>,
    pub proofs: Vec<Vec<C::Base>>,
    pub sigmas: Vec<Vec<C::Base>>,
    pub thetas: Vec<Vec<C::Base>>,
}

impl<C: Group, G: Group> From<Proof<G>> for ProofWitness<C>
where
    C: Group<Base = <G as Group>::Scalar>,
    G: Group<Base = <C as Group>::Scalar>,
{
    fn from(value: Proof<G>) -> Self {
        Self {
            point: value.sum_check_proof.point,
            proofs: value.sum_check_proof.proofs.into_iter().map(|i| i.evaluations).collect(),
            sigmas: value.sigmas,
            thetas: value.thetas,
        }
    }
}

/// Proof defines a multi-folding proof
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct Proof<C: Group> {
    pub sum_check_proof: SumCheckProof<C>,
    pub sigmas: Vec<Vec<C::Scalar>>,
    pub thetas: Vec<Vec<C::Scalar>>,
}

#[derive(Debug)]
pub struct MultiFolding<C: Group> {
    pub _c: PhantomData<C>,
}

impl<C: Group> MultiFolding<C> {
    /// Compute the arrays of sigma_i and theta_i from step 4 corresponding to the LCCCS and CCCS
    /// instances
    pub fn compute_sigmas_and_thetas(
        ccs: &CCS<C>,
        z_lcccs: &[Vec<C::Scalar>],
        z_cccs: &[Vec<C::Scalar>],
        r_x_prime: &[C::Scalar],
    ) -> (Vec<Vec<C::Scalar>>, Vec<Vec<C::Scalar>>) {
        let mut sigmas: Vec<Vec<C::Scalar>> = Vec::new();
        for z_lcccs_i in z_lcccs {
            // sigmas
            let sigma_i = compute_all_sum_Mz_evals(&ccs.M, z_lcccs_i, r_x_prime, ccs.s_prime);
            sigmas.push(sigma_i);
        }
        let mut thetas: Vec<Vec<C::Scalar>> = Vec::new();
        for z_cccs_i in z_cccs {
            // thetas
            let theta_i = compute_all_sum_Mz_evals(&ccs.M, z_cccs_i, r_x_prime, ccs.s_prime);
            thetas.push(theta_i);
        }
        (sigmas, thetas)
    }

    /// Compute the right-hand-side of step 5 of the multifolding scheme
    pub fn compute_c_from_sigmas_and_thetas(
        ccs: &CCS<C>,
        vec_sigmas: &[Vec<C::Scalar>],
        vec_thetas: &[Vec<C::Scalar>],
        gamma: C::Scalar,
        beta: &[C::Scalar],
        vec_r_x: &Vec<Vec<C::Scalar>>,
        r_x_prime: &[C::Scalar],
    ) -> C::Scalar {
        let mut c = C::Scalar::default();

        let mut e_lcccs = Vec::new();
        for r_x in vec_r_x {
            e_lcccs.push(eq_eval(r_x, r_x_prime).unwrap());
        }
        for (i, sigmas) in vec_sigmas.iter().enumerate() {
            // (sum gamma^j * e_i * sigma_j)
            for (j, sigma_j) in sigmas.iter().enumerate() {
                let gamma_j = gamma.pow([(i * ccs.t + j) as u64]);
                c += gamma_j * e_lcccs[i] * sigma_j;
            }
        }

        let mu = vec_sigmas.len();
        let e2 = eq_eval(beta, r_x_prime).unwrap();
        for (k, thetas) in vec_thetas.iter().enumerate() {
            // + gamma^{t+1} * e2 * sum c_i * prod theta_j
            let mut lhs = C::Scalar::default();
            for i in 0..ccs.q {
                let mut prod = C::Scalar::ONE;
                for j in ccs.S[i].clone() {
                    prod *= thetas[j];
                }
                lhs += ccs.c[i] * prod;
            }
            let gamma_t1 = gamma.pow([(mu * ccs.t + k) as u64]);
            c += gamma_t1 * e2 * lhs;
        }
        c
    }

    /// Compute g(x) polynomial for the given inputs.
    pub fn compute_g(
        running_instances: &[LCCCS<C>],
        cccs_instances: &[CCCS<C>],
        z_lcccs: &[Vec<C::Scalar>],
        z_cccs: &[Vec<C::Scalar>],
        gamma: C::Scalar,
        beta: &[C::Scalar],
    ) -> VirtualPolynomial<C::Scalar> {
        let mu = running_instances.len();
        let mut vec_Ls: Vec<VirtualPolynomial<C::Scalar>> = Vec::new();
        for (i, running_instance) in running_instances.iter().enumerate() {
            let mut Ls = running_instance.compute_Ls(&z_lcccs[i]);
            vec_Ls.append(&mut Ls);
        }
        let mut vec_Q: Vec<VirtualPolynomial<C::Scalar>> = Vec::new();
        for (i, cccs_instance) in cccs_instances.iter().enumerate() {
            let Q = cccs_instance.compute_Q(&z_cccs[i], beta);
            vec_Q.push(Q);
        }
        let mut g = vec_Ls[0].clone();

        // note: the following two loops can be integrated in the previous two loops, but left
        // separated for clarity in the PoC implementation.
        for (j, L_j) in vec_Ls.iter_mut().enumerate().skip(1) {
            let gamma_j = gamma.pow([j as u64]);
            L_j.scalar_mul(&gamma_j);
            g = g.add(L_j);
        }
        for (i, Q_i) in vec_Q.iter_mut().enumerate() {
            let gamma_mut_i = gamma.pow([(mu * cccs_instances[0].ccs.t + i) as u64]);
            Q_i.scalar_mul(&gamma_mut_i);
            g = g.add(Q_i);
        }
        g
    }

    pub fn fold(
        lcccs: &[LCCCS<C>],
        cccs: &[CCCS<C>],
        sigmas: &[Vec<C::Scalar>],
        thetas: &[Vec<C::Scalar>],
        r_x_prime: Vec<C::Scalar>,
        rho: C::Scalar,
    ) -> LCCCS<C> {
        let mut C_folded = <<C as Group>::CE as CommitmentEngineTrait<C>>::Commitment::default();
        let mut u_folded = C::Scalar::default();
        let mut x_folded: Vec<C::Scalar> = vec![C::Scalar::default(); lcccs[0].x.len()];
        let mut v_folded: Vec<C::Scalar> = vec![C::Scalar::default(); sigmas[0].len()];

        for i in 0..(lcccs.len() + cccs.len()) {
            let rho_i = rho.pow([i as u64]);

            let c: Commitment<C>;
            let u: C::Scalar;
            let x: Vec<C::Scalar>;
            let v: Vec<C::Scalar>;
            if i < lcccs.len() {
                c = lcccs[i].C;
                u = lcccs[i].u;
                x = lcccs[i].x.clone();
                v = sigmas[i].clone();
            } else {
                c = cccs[i - lcccs.len()].C;
                u = C::Scalar::ONE;
                x = cccs[i - lcccs.len()].x.clone();
                v = thetas[i - lcccs.len()].clone();
            }

            C_folded = C_folded.add(c.mul(rho_i));
            u_folded += rho_i * u;
            x_folded = x_folded
                .iter()
                .zip(
                    x.iter()
                        .map(|x_i| *x_i * rho_i)
                        .collect::<Vec<C::Scalar>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();

            v_folded = v_folded
                .iter()
                .zip(
                    v.iter()
                        .map(|x_i| *x_i * rho_i)
                        .collect::<Vec<C::Scalar>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();
        }

        LCCCS::<C> {
            C: C_folded,
            ccs: lcccs[0].ccs.clone(),
            u: u_folded,
            x: x_folded,
            r_x: r_x_prime,
            v: v_folded,
        }
    }

    pub fn fold_witness(
        w_lcccs: &[CCSWitness<C>],
        w_cccs: &[CCSWitness<C>],
        rho: C::Scalar,
    ) -> CCSWitness<C> {
        let mut w_folded: Vec<C::Scalar> = vec![C::Scalar::default(); w_lcccs[0].w.len()];
        let mut r_w_folded = C::Scalar::default();

        for i in 0..(w_lcccs.len() + w_cccs.len()) {
            let rho_i = rho.pow([i as u64]);
            let w: Vec<C::Scalar>;
            let r_w: C::Scalar;

            if i < w_lcccs.len() {
                w = w_lcccs[i].w.clone();
                r_w = w_lcccs[i].r_w;
            } else {
                w = w_cccs[i - w_lcccs.len()].w.clone();
                r_w = w_cccs[i - w_lcccs.len()].r_w;
            }

            w_folded = w_folded
                .iter()
                .zip(
                    w.iter()
                        .map(|x_i| *x_i * rho_i)
                        .collect::<Vec<C::Scalar>>(),
                )
                .map(|(a_i, b_i)| *a_i + b_i)
                .collect();

            r_w_folded += rho_i * r_w;
        }
        CCSWitness {
            w: w_folded,
            r_w: r_w_folded,
        }
    }

    /// Perform the multifolding prover.
    ///
    /// Given μ LCCCS instances and ν CCS instances, fold them into a single LCCCS instance. Since
    /// this is the prover, also fold their witness.
    ///
    /// Return the final folded LCCCS, the folded witness, the sumcheck proof, and the helper
    /// sumcheck claims sigmas and thetas.
    pub fn prove(
        transcript: &mut C::TE,
        running_instances: &[LCCCS<C>],
        new_instances: &[CCCS<C>],
        w_lcccs: &[CCSWitness<C>],
        w_cccs: &[CCSWitness<C>],
    ) -> (Proof<C>, LCCCS<C>, CCSWitness<C>) {
        // TODO appends to transcript

        assert!(!running_instances.is_empty());
        assert!(!new_instances.is_empty());

        // construct the LCCCS z vector from the relaxation factor, public IO and witness
        // XXX this deserves its own function in LCCCS
        let mut z_lcccs = Vec::new();
        for (i, running_instance) in running_instances.iter().enumerate() {
            let z_1: Vec<C::Scalar> = [
                vec![running_instance.u],
                running_instance.x.clone(),
                w_lcccs[i].w.to_vec(),
            ]
            .concat();
            z_lcccs.push(z_1);
        }
        // construct the CCCS z vector from the public IO and witness
        let mut z_cccs = Vec::new();
        for (i, new_instance) in new_instances.iter().enumerate() {
            let z_2: Vec<C::Scalar> = [
                vec![C::Scalar::ONE],
                new_instance.x.clone(),
                w_cccs[i].w.to_vec(),
            ]
            .concat();
            z_cccs.push(z_2);
        }

        // Step 1: Get some challenges
        let gamma = transcript.squeeze(b"gamma").unwrap();
        let beta = transcript
            .batch_squeeze(b"beta", running_instances[0].ccs.s).unwrap();

        // Compute g(x)
        let g = Self::compute_g(
            running_instances,
            new_instances,
            &z_lcccs,
            &z_cccs,
            gamma,
            &beta,
        );

        // Step 3: Run the sumcheck prover
        let sumcheck_proof =
            <PolyIOP<C::Scalar> as SumCheck<C>>::prove(&g, transcript).unwrap(); // XXX unwrap

        // Note: The following two "sanity checks" are done for this prototype, in a final version
        // they should be removed.
        //
        // Sanity check 1: evaluate g(x) over x \in {0,1} (the boolean hypercube), and check that
        // its sum is equal to the extracted_sum from the SumCheck.
        //////////////////////////////////////////////////////////////////////
        let mut g_over_bhc = C::Scalar::default();
        for x in BooleanHypercube::new(running_instances[0].ccs.s) {
            g_over_bhc += g.evaluate(&x).unwrap();
        }

        // note: this is the sum of g(x) over the whole boolean hypercube
        let extracted_sum =
            <PolyIOP<C::Scalar> as SumCheck<C>>::extract_sum(&sumcheck_proof);
        assert_eq!(extracted_sum, g_over_bhc);
        // Sanity check 2: expect \sum v_j * gamma^j to be equal to the sum of g(x) over the
        // boolean hypercube (and also equal to the extracted_sum from the SumCheck).
        let mut sum_v_j_gamma = C::Scalar::default();
        for (i, running_instance) in running_instances.iter().enumerate() {
            for j in 0..running_instance.v.len() {
                let gamma_j = gamma.pow([(i * running_instances[0].ccs.t + j) as u64]);
                sum_v_j_gamma += running_instance.v[j] * gamma_j;
            }
        }
        assert_eq!(g_over_bhc, sum_v_j_gamma);
        assert_eq!(extracted_sum, sum_v_j_gamma);
        //////////////////////////////////////////////////////////////////////

        // Step 2: dig into the sumcheck and extract r_x_prime
        let r_x_prime = sumcheck_proof.point.clone();

        // Step 4: compute sigmas and thetas
        let (sigmas, thetas) = Self::compute_sigmas_and_thetas(
            &running_instances[0].ccs,
            &z_lcccs,
            &z_cccs,
            &r_x_prime,
        );

        // Step 6: Get the folding challenge
        let rho = transcript.squeeze(b"rho").unwrap();

        // Step 7: Create the folded instance
        let folded_lcccs = Self::fold(
            running_instances,
            new_instances,
            &sigmas,
            &thetas,
            r_x_prime,
            rho,
        );

        // Step 8: Fold the witnessesG::Base
        let folded_witness = Self::fold_witness(w_lcccs, w_cccs, rho);

        (
            Proof::<C> {
                sum_check_proof: sumcheck_proof,
                sigmas,
                thetas,
            },
            folded_lcccs,
            folded_witness,
        )
    }

    /// Perform the multifolding verifier:
    ///
    /// Given μ LCCCS instances and ν CCS instances, fold them into a single LCCCS instance.
    ///
    /// Return the folded LCCCS instance.
    pub fn verify(
        transcript: &mut C::TE,
        running_instances: &[LCCCS<C>],
        new_instances: &[CCCS<C>],
        proof: Proof<C>,
    ) -> LCCCS<C> {
        // TODO appends to transcript

        assert!(!running_instances.is_empty());
        assert!(!new_instances.is_empty());

        // Step 1: Get some challenges
        let gamma = transcript.squeeze(b"gamma").unwrap();
        let beta = transcript
            .batch_squeeze(b"beta", running_instances[0].ccs.s)
            .unwrap();

        let vp_aux_info = VPAuxInfo::<C::Scalar> {
            max_degree: running_instances[0].ccs.d + 1,
            num_variables: running_instances[0].ccs.s,
            phantom: PhantomData::<C::Scalar>,
        };

        // Step 3: Start verifying the sumcheck
        // First, compute the expected sumcheck sum: \sum gamma^j v_j
        let mut sum_v_j_gamma = C::Scalar::default();
        for (i, running_instance) in running_instances.iter().enumerate() {
            for j in 0..running_instance.v.len() {
                let gamma_j = gamma.pow([(i * running_instances[0].ccs.t + j) as u64]);
                sum_v_j_gamma += running_instance.v[j] * gamma_j;
            }
        }

        // Verify the interactive part of the sumcheck
        let sumcheck_subclaim = <PolyIOP<C::Scalar> as SumCheck<C>>::verify(
            sum_v_j_gamma,
            &proof.sum_check_proof,
            &vp_aux_info,
            transcript,
        )
        .unwrap();

        // Step 2: Dig into the sumcheck claim and extract the randomness used
        let r_x_prime = sumcheck_subclaim.point.clone();

        // Step 5: Finish verifying sumcheck (verify the claim c)
        let c = Self::compute_c_from_sigmas_and_thetas(
            &new_instances[0].ccs,
            &proof.sigmas,
            &proof.thetas,
            gamma,
            &beta,
            &running_instances
                .iter()
                .map(|lcccs| lcccs.r_x.clone())
                .collect(),
            &r_x_prime,
        );
        // check that the g(r_x') from the sumcheck proof is equal to the computed c from sigmas&thetas
        assert_eq!(c, sumcheck_subclaim.expected_evaluation);

        // Sanity check: we can also compute g(r_x') from the proof last evaluation value, and
        // should be equal to the previously obtained values.
        let g_on_rxprime_from_sumcheck_last_eval = interpolate_uni_poly::<C::Scalar>(
            &proof.sum_check_proof.proofs.last().unwrap().evaluations,
            *r_x_prime.last().unwrap(),
        )
        .unwrap();
        assert_eq!(g_on_rxprime_from_sumcheck_last_eval, c);
        assert_eq!(
            g_on_rxprime_from_sumcheck_last_eval,
            sumcheck_subclaim.expected_evaluation
        );

        // Step 6: Get the folding challenge
        let rho = transcript.squeeze(b"rho").unwrap();

        // Step 7: Compute the folded instance
        Self::fold(
            running_instances,
            new_instances,
            &proof.sigmas,
            &proof.thetas,
            r_x_prime,
            rho,
        )
    }
}

#[cfg(test)]
pub mod test {
    use halo2curves::bn256::Fr;
    use rand_core::OsRng;

    use crate::nimfs::ccs::ccs::test::{get_test_ccs, get_test_z};
    use crate::provider::bn256_grumpkin::bn256::Point;
    use crate::provider::poseidon::PoseidonConstantsCircuit;

    use super::*;

    // NIMFS: Non Interactive Multi-folding Scheme
    type NIMFS = MultiFolding<Point>;

    #[test]
    fn test_compute_sigmas_and_thetas() -> () {
        let rng = OsRng;

        let ccs = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let gamma: Fr = Fr::random(&mut OsRng);
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::random(&mut OsRng)).collect();
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::random(&mut OsRng)).collect();

        // Initialize a multifolding object
        let ck = ccs.commitment_key();
        let (lcccs_instance, _) = ccs.to_lcccs(rng, &ck, &z1);
        let (cccs_instance, _) = ccs.to_cccs(rng, &ck, &z2);

        let (sigmas, thetas) = NIMFS::compute_sigmas_and_thetas(
            &lcccs_instance.ccs,
            &vec![z1.clone()],
            &vec![z2.clone()],
            &r_x_prime,
        );

        let g = NIMFS::compute_g(
            &vec![lcccs_instance.clone()],
            &vec![cccs_instance.clone()],
            &vec![z1.clone()],
            &vec![z2.clone()],
            gamma,
            &beta,
        );

        // we expect g(r_x_prime) to be equal to:
        // c = (sum gamma^j * e1 * sigma_j) + gamma^{t+1} * e2 * sum c_i * prod theta_j
        // from compute_c_from_sigmas_and_thetas
        let expected_c = g.evaluate(&r_x_prime).unwrap();
        let c = NIMFS::compute_c_from_sigmas_and_thetas(
            &ccs,
            &sigmas,
            &thetas,
            gamma,
            &beta,
            &vec![lcccs_instance.r_x],
            &r_x_prime,
        );
        assert_eq!(c, expected_c);
    }

    #[test]
    fn test_compute_g() -> () {
        let ccs = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let rng = OsRng;
        let gamma: Fr = Fr::random(rng);
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::random(rng)).collect();

        // Initialize a multifolding object
        let ck = ccs.commitment_key();
        let (lcccs_instance, _) = ccs.to_lcccs(rng, &ck, &z1);
        let (cccs_instance, _) = ccs.to_cccs(rng, &ck, &z2);

        let mut sum_v_j_gamma = Fr::zero();
        for j in 0..lcccs_instance.v.len() {
            let gamma_j = gamma.pow([j as u64]);
            sum_v_j_gamma += lcccs_instance.v[j] * gamma_j;
        }

        // Compute g(x) with that r_x
        let g = NIMFS::compute_g(
            &vec![lcccs_instance.clone()],
            &vec![cccs_instance.clone()],
            &vec![z1.clone()],
            &vec![z2.clone()],
            gamma,
            &beta,
        );

        // evaluate g(x) over x \in {0,1}^s
        let mut g_on_bhc = Fr::zero();
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            g_on_bhc += g.evaluate(&x).unwrap();
        }

        // evaluate sum_{j \in [t]} (gamma^j * Lj(x)) over x \in {0,1}^s
        let mut sum_Lj_on_bhc = Fr::zero();
        let vec_L = lcccs_instance.compute_Ls(&z1);
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            for j in 0..vec_L.len() {
                let gamma_j = gamma.pow([j as u64]);
                sum_Lj_on_bhc += vec_L[j].evaluate(&x).unwrap() * gamma_j;
            }
        }

        // Q(x) over bhc is assumed to be zero, as checked in the test 'test_compute_Q'
        assert_ne!(g_on_bhc, Fr::zero());

        // evaluating g(x) over the boolean hypercube should give the same result as evaluating the
        // sum of gamma^j * Lj(x) over the boolean hypercube
        assert_eq!(g_on_bhc, sum_Lj_on_bhc);

        // evaluating g(x) over the boolean hypercube should give the same result as evaluating the
        // sum of gamma^j * v_j over j \in [t]
        assert_eq!(g_on_bhc, sum_v_j_gamma);
    }

    #[test]
    fn test_fold() -> () {
        let ccs = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);
        ccs.check_relation(&z1).unwrap();
        ccs.check_relation(&z2).unwrap();

        let rng = OsRng;
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::random(rng)).collect();

        // Initialize a multifolding object
        let ck = ccs.commitment_key();
        let (running_instance, _) = ccs.to_lcccs(rng, &ck, &z1);

        let (sigmas, thetas) = MultiFolding::<Point>::compute_sigmas_and_thetas(
            &running_instance.ccs,
            &vec![z1.clone()],
            &vec![z2.clone()],
            &r_x_prime,
        );

        let ck = ccs.commitment_key();

        let (lcccs, w1) = ccs.to_lcccs(rng, &ck, &z1);
        let (cccs, w2) = ccs.to_cccs(rng, &ck, &z2);

        lcccs.check_relation(&ck, &w1).unwrap();
        cccs.check_relation(&ck, &w2).unwrap();

        let rng = OsRng;
        let rho = Fr::random(rng);

        let folded = MultiFolding::<Point>::fold(
            &vec![lcccs],
            &vec![cccs],
            &sigmas,
            &thetas,
            r_x_prime,
            rho,
        );

        let w_folded = MultiFolding::<Point>::fold_witness(&vec![w1], &vec![w2], rho);

        // check lcccs relation
        folded.check_relation(&ck, &w_folded).unwrap();
    }

    /// Perform multifolding of an LCCCS instance with a CCCS instance (as described in the paper)
    #[test]
    pub fn test_basic_multifolding() {
        let rng = OsRng;

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<Point>();
        let ck = ccs.commitment_key();

        // Generate a satisfying witness
        let z_1 = get_test_z(3);
        // Generate another satisfying witness
        let z_2 = get_test_z(4);

        // Create the LCCCS instance out of z_1
        let (running_instance, w1) = ccs.to_lcccs(rng, &ck, &z_1);
        // Create the CCCS instance out of z_2
        let (new_instance, w2) = ccs.to_cccs(rng, &ck, &z_2);

        // Prover's transcript
        let constants = PoseidonConstantsCircuit::<Fr>::default();
        let mut transcript_p = <Point as Group>::TE::new(constants, b"multifolding");
        transcript_p.squeeze(b"init").unwrap();
        // Verifier's transcript
        let mut transcript_v = transcript_p.clone();

        // Run the prover side of the multi-folding
        let (proof, folded_lcccs, folded_witness) = NIMFS::prove(
            &mut transcript_p,
            &vec![running_instance.clone()],
            &vec![new_instance.clone()],
            &vec![w1],
            &vec![w2],
        );


        // Run the verifier side of the multi-folding
        let folded_lcccs_v = NIMFS::verify(
            &mut transcript_v,
            &vec![running_instance.clone()],
            &vec![new_instance.clone()],
            proof,
        );
        assert_eq!(folded_lcccs, folded_lcccs_v);

        // Check that the folded LCCCS instance is a valid instance with respect to the folded witness
        folded_lcccs
            .check_relation(&ck, &folded_witness)
            .unwrap();
    }

    /// Perform multiple steps of multifolding of an LCCCS instance with a CCCS instance
    #[test]
    pub fn test_multifolding_two_instances_multiple_steps() {
        let rng = OsRng;

        let ccs = get_test_ccs::<Point>();

        let ck = ccs.commitment_key();

        // LCCCS witness
        let z_1 = get_test_z(2);
        let (mut running_instance, mut w1) = ccs.to_lcccs(rng, &ck, &z_1);

        let constants = PoseidonConstantsCircuit::<Fr>::default();
        // Prover's transcript
        let mut transcript_p = <Point as Group>::TE::new(constants, b"multifolding");
        transcript_p.squeeze(b"init").unwrap();
        // Verifier's transcript
        let mut transcript_v = transcript_p.clone();

        let n: usize = 10;
        for i in 3..n {
            println!("\niteration: i {}", i); // DBG

            // CCS witness
            let z_2 = get_test_z(i);
            println!("z_2 {:?}", z_2); // DBG

            let (new_instance, w2) = ccs.to_cccs(rng, &ck, &z_2);

            // run the prover side of the multifolding
            let (proof, folded_lcccs, folded_witness) = NIMFS::prove(
                &mut transcript_p,
                &vec![running_instance.clone()],
                &vec![new_instance.clone()],
                &vec![w1],
                &vec![w2],
            );

            // run the verifier side of the multifolding
            let folded_lcccs_v = NIMFS::verify(
                &mut transcript_v,
                &vec![running_instance.clone()],
                &vec![new_instance.clone()],
                proof,
            );

            assert_eq!(folded_lcccs, folded_lcccs_v);

            // check that the folded instance with the folded witness holds the LCCCS relation
            println!("check_relation {}", i);
            folded_lcccs
                .check_relation(&ck, &folded_witness)
                .unwrap();

            running_instance = folded_lcccs;
            w1 = folded_witness;
        }
    }

    /// Test that generates mu>1 and nu>1 instances, and folds them in a single multifolding step.
    #[test]
    pub fn test_multifolding_mu_nu_instances() {
        let rng = OsRng;

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<Point>();
        let ck = ccs.commitment_key();

        let mu = 10;
        let nu = 15;

        // Generate a mu LCCCS & nu CCCS satisfying witness
        let mut z_lcccs = Vec::new();
        for i in 0..mu {
            let z = get_test_z(i + 3);
            z_lcccs.push(z);
        }
        let mut z_cccs = Vec::new();
        for i in 0..nu {
            let z = get_test_z(nu + i + 3);
            z_cccs.push(z);
        }

        // Create the LCCCS instances out of z_lcccs
        let mut lcccs_instances = Vec::new();
        let mut w_lcccs = Vec::new();
        for i in 0..mu {
            let (running_instance, w) = ccs.to_lcccs(rng, &ck, &z_lcccs[i]);
            lcccs_instances.push(running_instance);
            w_lcccs.push(w);
        }
        // Create the CCCS instance out of z_cccs
        let mut cccs_instances = Vec::new();
        let mut w_cccs = Vec::new();
        for i in 0..nu {
            let (new_instance, w) = ccs.to_cccs(rng, &ck, &z_cccs[i]);
            cccs_instances.push(new_instance);
            w_cccs.push(w);
        }

        let constants = PoseidonConstantsCircuit::<Fr>::default();
        // Prover's transcript
        let mut transcript_p = <Point as Group>::TE::new(constants, b"multifolding");
        transcript_p.squeeze(b"init").unwrap();
        // Verifier's transcript
        let mut transcript_v = transcript_p.clone();

        // Run the prover side of the multi-folding
        let (proof, folded_lcccs, folded_witness) = NIMFS::prove(
            &mut transcript_p,
            &lcccs_instances,
            &cccs_instances,
            &w_lcccs,
            &w_cccs,
        );

        // Run the verifier side of the multifolding
        let folded_lcccs_v =
            NIMFS::verify(&mut transcript_v, &lcccs_instances, &cccs_instances, proof);
        assert_eq!(folded_lcccs, folded_lcccs_v);

        // Check that the folded LCCCS instance is a valid instance with respect to the folded witness
        folded_lcccs
            .check_relation(&ck, &folded_witness)
            .unwrap();
    }

    /// Test that generates mu>1 and nu>1 instances, and folds them in a single multifolding step
    /// and repeats the process doing multiple steps.
    #[test]
    pub fn test_multifolding_mu_nu_instances_multiple_steps() {
        let rng = OsRng;

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<Point>();
        let ck = ccs.commitment_key();

        let constants = PoseidonConstantsCircuit::<Fr>::default();
        // Prover's transcript
        let mut transcript_p = <Point as Group>::TE::new(constants, b"multifolding");
        transcript_p.squeeze(b"init").unwrap();
        // Verifier's transcript
        let mut transcript_v = transcript_p.clone();

        let n_steps = 3;

        // number of LCCCS & CCCS instances in each multi-folding step
        let mu = 10;
        let nu = 15;

        // Generate a mu LCCCS & nu CCCS satisfying witness, for each step
        for step in 0..n_steps {
            let mut z_lcccs = Vec::new();
            for i in 0..mu {
                let z = get_test_z(step + i + 3);
                z_lcccs.push(z);
            }
            let mut z_cccs = Vec::new();
            for i in 0..nu {
                let z = get_test_z(nu + i + 3);
                z_cccs.push(z);
            }

            // Create the LCCCS instances out of z_lcccs
            let mut lcccs_instances = Vec::new();
            let mut w_lcccs = Vec::new();
            for i in 0..mu {
                let (running_instance, w) = ccs.to_lcccs(rng, &ck, &z_lcccs[i]);
                lcccs_instances.push(running_instance);
                w_lcccs.push(w);
            }
            // Create the CCCS instance out of z_cccs
            let mut cccs_instances = Vec::new();
            let mut w_cccs = Vec::new();
            for i in 0..nu {
                let (new_instance, w) = ccs.to_cccs(rng, &ck, &z_cccs[i]);
                cccs_instances.push(new_instance);
                w_cccs.push(w);
            }

            // Run the prover side of the multi-folding
            let (proof, folded_lcccs, folded_witness) = NIMFS::prove(
                &mut transcript_p,
                &lcccs_instances,
                &cccs_instances,
                &w_lcccs,
                &w_cccs,
            );

            // Run the verifier side of the multi-folding
            let folded_lcccs_v =
                NIMFS::verify(&mut transcript_v, &lcccs_instances, &cccs_instances, proof);
            assert_eq!(folded_lcccs, folded_lcccs_v);

            // Check that the folded LCCCS instance is a valid instance with respect to the folded witness
            folded_lcccs
                .check_relation(&ck, &folded_witness)
                .unwrap();
        }
    }
}
