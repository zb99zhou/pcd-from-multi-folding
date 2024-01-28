use bellpepper::gadgets::Assignment;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::{AllocatedNum, Num};
use ff::Field;
use crate::constants::{NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use crate::gadgets::cccs::{AllocatedCCCSPrimaryPart, AllocatedCCCSSecondPart, AllocatedLCCCSPrimaryPart, multi_folding, multi_folding_with_primary_part};
use crate::gadgets::ext_allocated_num::ExtendFunc;
use crate::gadgets::sumcheck::{AllocatedProof, enforce_compute_c_from_sigmas_and_thetas, enforce_interpolate_uni_poly, sumcheck_verify};
use crate::gadgets::utils::{alloc_num_equals, alloc_zero, conditionally_select_vec_allocated_num, le_bits_to_num};
use crate::nimfs::ccs::cccs::CCCS;
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::espresso::virtual_polynomial::VPAuxInfo;
use crate::nimfs::multifolding::NIMFSProof;
use crate::traits::{Group, ROCircuitTrait, ROConstantsCircuit, TEConstantsCircuit, TranscriptCircuitEngineTrait};
use crate::traits::circuit::StepCircuit;

pub struct PCDUnitParams<G: Group>{
    pub(crate) mu: usize,
    pub(crate) nu: usize,
    pub(crate) ccs: CCS<G>,
    pub(crate) io_num: usize,
    pub(crate) limb_width: usize,
    pub(crate) n_limbs: usize,
    pub(crate) is_primary_circuit: bool, // A boolean indicating if this is the primary circuit
}

impl<G: Group> PCDUnitParams<G> {
    pub const fn new(
        limb_width: usize,
        n_limbs: usize,
        is_primary_circuit: bool,
        mu: usize,
        nu: usize,
        io_num: usize,
        ccs: CCS<G>
    ) -> Self {
        Self {
            mu,
            nu,
            ccs,
            io_num,
            limb_width,
            n_limbs,
            is_primary_circuit,
        }
    }
}

// #[derive(Debug, Serialize, Deserialize)]
// #[serde(bound = "")]
pub struct PCDUnitInputs<G: Group> {
    params: G::Scalar, // Hash(Shape of u2, Gens for u2). Needed for computing the challenge.
    // i: G::Scalar,
    z0: Vec<G::Scalar>,
    zi: Option<Vec<G::Scalar>>,
    lcccs: Option<Vec<LCCCS<G>>>,
    cccs: Option<Vec<CCCS<G>>>,
    r: usize
    // T: Option<Commitment<G>>,
}

impl<G: Group> PCDUnitInputs<G> {
    /// Create new inputs/witness for the verification circuit
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        params: G::Scalar,
        z0: Vec<G::Scalar>,
        zi: Option<Vec<G::Scalar>>,
        lcccs: Option<Vec<LCCCS<G>>>,
        cccs: Option<Vec<CCCS<G>>>,
        r: usize
    ) -> Self {
        Self {
            params,
            z0,
            zi,
            lcccs,
            cccs,
            r,
        }
    }
}

pub struct PCDUnitPrimaryCircuit<'a, G: Group, SC: StepCircuit<G::Scalar>> {
    params: &'a PCDUnitParams<G>,
    ro_consts: ROConstantsCircuit<G>, // random oracle
    te_consts: TEConstantsCircuit<G>, // Transcript Engine
    inputs: Option<PCDUnitInputs<G>>,
    proof: NIMFSProof<G>,
    step_circuit: &'a SC, // The function that is applied for each step
}

impl<'a, G: Group, SC: StepCircuit<G::Scalar>> PCDUnitPrimaryCircuit<'a, G, SC> {
    /// Create a new verification circuit for the input relaxed r1cs instances
    pub const fn new(
        params: &'a PCDUnitParams<G>,
        inputs: Option<PCDUnitInputs<G>>,
        step_circuit: &'a SC,
        proof: NIMFSProof<G>,
        ro_consts: ROConstantsCircuit<G>,
        te_consts: TEConstantsCircuit<G>,
    ) -> Self {
        Self {
            params,
            inputs,
            proof,
            step_circuit,
            ro_consts,
            te_consts,
        }
    }

    /// Allocate all witnesses and return
    fn alloc_witness<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &self,
        mut cs: CS,
        arity: usize,
    ) -> Result<
        (
            AllocatedProof<G>,
            Vec<AllocatedNum<G::Scalar>>,
            Vec<AllocatedNum<G::Scalar>>,
            Vec<AllocatedLCCCSPrimaryPart<G>>,
            Vec<AllocatedCCCSPrimaryPart<G>>,
        ),
        SynthesisError,
    > {
        // Allocate the params
        let nimfs_proof = AllocatedProof::from_witness(
            cs.namespace(|| "params"),
            &self.proof,
        )?;

        // Allocate i
        // let i = AllocatedNum::alloc(cs.namespace(|| "i"), || Ok(self.inputs.get()?.i))?;

        // Allocate z0
        let z_0 = (0..arity)
            .map(|i| {
                AllocatedNum::alloc(cs.namespace(|| format!("z0_{i}")), || {
                    Ok(self.inputs.get()?.z0[i])
                })
            })
            .collect::<Result<Vec<AllocatedNum<G::Scalar>>, _>>()?;

        // Allocate zi. If inputs.zi is not provided (base case) allocate default value 0
        let zero = vec![G::Scalar::ZERO; arity];
        let z_i = (0..arity)
            .map(|i| {
                AllocatedNum::alloc(cs.namespace(|| format!("zi_{i}")), || {
                    Ok(self.inputs.get()?.zi.as_ref().unwrap_or(&zero)[i])
                })
            })
            .collect::<Result<Vec<AllocatedNum<G::Scalar>>, _>>()?;

        // Allocate the running instance
        let lcccs: AllocatedLCCCSPrimaryPart<G> = AllocatedLCCCSPrimaryPart::alloc(
            cs.namespace(|| "Allocate lcccs"),
            self.inputs.get().as_ref().map_or(None, |inputs| {
                inputs.lcccs.get().as_ref().map_or(None, |U| Some(&U[0])) // TODO: deal multi lcccs
            }),
            self.params.io_num,
            self.params.limb_width,
            self.params.n_limbs,
        )?;

        // Allocate the instance to be folded in
        let cccs = AllocatedCCCSPrimaryPart::alloc(
            cs.namespace(|| "allocate instance cccs to fold"),
            self.inputs.get().as_ref().map_or(None, |inputs| {
                inputs.cccs.get().as_ref().map_or(None, |u| Some(&u[0])) // TODO: deal multi lcccs
            }),
            self.params.io_num,
        )?;


        Ok((nimfs_proof, z_0, z_i, vec![lcccs], vec![cccs]))
    }

    /// Synthesizes base case and returns the new relaxed `R1CSInstance`
    fn synthesize_base_case<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &self,
        mut cs: CS,
        cccs: AllocatedCCCSPrimaryPart<G>,
    ) -> Result<AllocatedLCCCSPrimaryPart<G>, SynthesisError> {
        let lcccs_default = if self.params.is_primary_circuit {
            // The primary circuit just returns the default R1CS instance
            AllocatedLCCCSPrimaryPart::default(
                cs.namespace(|| "Allocate lcccs default"),
                self.params.io_num,
                self.params.ccs.s,
                self.params.ccs.t,
                self.params.limb_width,
                self.params.n_limbs,
            )?
        } else {
            // The secondary circuit returns the incoming LCCCS instance
            AllocatedLCCCSPrimaryPart::from_cccs(
                cs.namespace(|| "Allocate lcccs default"),
                cccs,
                self.params.limb_width,
                self.params.n_limbs,
            )?
        };
        Ok(lcccs_default)
    }

    /// Synthesizes non base case and returns the new relaxed `R1CSInstance`
    /// And a boolean indicating if all checks pass
    #[allow(clippy::too_many_arguments)]
    fn synthesize_non_base_case<CS: ConstraintSystem<<G as Group>::Scalar>>(
        &self,
        mut cs: CS,
        params: &PCDUnitParams<G>,
        _z_0: &[AllocatedNum<G::Scalar>],
        _z_i: &[AllocatedNum<G::Scalar>],
        lcccs: Vec<AllocatedLCCCSPrimaryPart<G>>,
        cccs: Vec<AllocatedCCCSPrimaryPart<G>>,
        proof: &AllocatedProof<G>,
    ) -> Result<(AllocatedLCCCSPrimaryPart<G>, AllocatedBit), SynthesisError> {
        assert!(!lcccs.is_empty());
        assert!(!cccs.is_empty());

        let mut transcript = G::TECircuit::new(
            self.te_consts.clone(),
            cs.namespace(|| "init NIMFS transcript"),
            b"multifolding"
        );
        // Step 1: Get some challenges
        let gamma = transcript.squeeze(cs.namespace(|| "alloc gamma"), b"gamma")?;
        let beta = transcript.batch_squeeze(
            cs.namespace(|| "alloc beta"),
            b"beta",
            params.ccs.s,
        )?;

        // Step 3: Start verifying the sumcheck
        // First, compute the expected sumcheck sum: \sum gamma^j v_j
        let mut sum_v_j_gamma_lc = Num::zero();
        for (i, running_instance) in lcccs.iter().enumerate() {
            for j in 0..running_instance.Vs.len() {
                let gamma_j = gamma.pow_constant(cs.namespace(|| "alloc gamma_j"), i * params.ccs.t + j)?;
                let res = running_instance.Vs[j].mul(cs.namespace(|| "v * gamma_j"), &gamma_j)?;
                sum_v_j_gamma_lc = sum_v_j_gamma_lc.add(&res.into());
            }
        }
        let sum_v_j_gamma = AllocatedNum::alloc(
            cs.namespace(|| "alloc tmp"),
            || sum_v_j_gamma_lc.get_value().get().copied()
        )?;
        cs.enforce(
            || "constraints final lc",
            |_lc| sum_v_j_gamma_lc.lc(G::Scalar::ONE),
            |lc| lc + CS::one(),
            |lc| lc + sum_v_j_gamma.get_variable(),
        );

        let vp_aux_info = VPAuxInfo::<G::Scalar> {
            max_degree: params.ccs.d + 1,
            num_variables: params.ccs.s,
            phantom: std::marker::PhantomData::<G::Scalar>,
        };
        let sumcheck_subclaim = sumcheck_verify(
            cs.namespace(|| "verify sumcheck proof"),
            &sum_v_j_gamma,
            &proof.sum_check_proof,
            &vp_aux_info,
            &mut transcript,
        )?;

        // Step 2: Dig into the sumcheck claim and extract the randomness used
        let r_x_prime = sumcheck_subclaim.point.clone();

        // Step 5: Finish verifying sumcheck (verify the claim c)
        let c = enforce_compute_c_from_sigmas_and_thetas(
            cs.namespace(|| "calc c"),
            &params.ccs,
            &proof.sigmas,
            &proof.thetas,
            gamma,
            &beta,
            lcccs
                .iter()
                .map(|lcccs| lcccs.r_x.clone())
                .collect(),
            &r_x_prime,
        )?;
        let check_pass1 = alloc_num_equals(
            cs.namespace(|| "check that the g(r_x') from the sumcheck proof is equal to the computed c from sigmas&thetas"),
            &c,
            &sumcheck_subclaim.expected_evaluation
        )?;

        // Sanity check: we can also compute g(r_x') from the proof last evaluation value, and
        // should be equal to the previously obtained values.
        let g_on_rxprime_from_sumcheck_last_eval = enforce_interpolate_uni_poly(
            cs.namespace(|| "g_on_rxprime_from_sumcheck_last_eval"),
            r_x_prime.last().unwrap(),
            &proof.sum_check_proof.proofs.last().unwrap().evaluations,
        )?;
        let check_pass2 = alloc_num_equals(
            cs.namespace(|| "check that the g(r_x') from the sumcheck proof is equal to the computed c from sigmas&thetas"),
            &c,
            &g_on_rxprime_from_sumcheck_last_eval
        )?;
        let check_pass3 = alloc_num_equals(
            cs.namespace(|| "check that the g(r_x') from the sumcheck proof is equal to the computed c from sigmas&thetas"),
            &sumcheck_subclaim.expected_evaluation,
            &g_on_rxprime_from_sumcheck_last_eval
        )?;

        // Step 6: Get the folding challenge
        let rho = transcript.squeeze(cs.namespace(|| "alloc rho"), b"rho")?;

        // Run NIMFS Verifier part 1
        let new_lcccs = multi_folding_with_primary_part(
            cs.namespace(|| "compute fold of U and u"),
            &lcccs,
            &cccs,
            rho,
            &proof.sigmas,
            &proof.thetas,
            self.params.limb_width,
            self.params.n_limbs,
        )?;
        let C = multi_folding_with_second_part();

        let check_pass = AllocatedBit::and(
            cs.namespace(|| "check pass 1 and 2"),
            &check_pass1,
            &check_pass2,
        )?;
        let check_pass = AllocatedBit::and(
            cs.namespace(|| "check pass 1 and 2 and 3"),
            &check_pass,
            &check_pass3,
        )?;

        Ok((new_lcccs, check_pass))
    }
}

impl<'a, G: Group, SC: StepCircuit<G::Scalar>> PCDUnitPrimaryCircuit<'a, G, SC> {
    /// synthesize circuit giving constraint system
    pub fn synthesize<CS: ConstraintSystem<<G as Group>::Scalar>>(
        self,
        cs: &mut CS,
    ) -> Result<Vec<AllocatedNum<G::Scalar>>, SynthesisError> {
        let arity = self.step_circuit.arity();

        // Allocate all witnesses
        let (
            nimfs_proof, z_0, z_i,
            lcccs, cccs,
        ) = self.alloc_witness(cs.namespace(|| "allocate the circuit witness"), arity)?;
        let Xs = cccs.iter().flat_map(|c|c.Xs.to_vec()).collect::<Vec<_>>();

        // Compute variable indicating if this is the base case
        let zero = alloc_zero(cs.namespace(|| "zero"))?;
        let is_base_case = alloc_num_equals(cs.namespace(|| "Check if base case"), &lcccs[0].C.is_infinity, &zero)?;

        // Synthesize the circuit for the base case and get the new running instance
        let lcccs_base = self.synthesize_base_case(cs.namespace(|| "base case"), cccs[0].clone())?;

        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let (Unew_non_base, check_non_base_pass) = self.synthesize_non_base_case(
            cs.namespace(|| "synthesize non base case"),
            &self.params,
            &z_0,
            &z_i,
            lcccs,
            cccs,
            &nimfs_proof
        )?;

        // Either check_non_base_pass=true or we are in the base case
        let should_be_false = AllocatedBit::nor(
            cs.namespace(|| "check_non_base_pass nor base_case"),
            &check_non_base_pass,
            &is_base_case,
        )?;
        cs.enforce(
            || "check_non_base_pass nor base_case = false",
            |lc| lc + should_be_false.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        // Compute the U_new
        let lcccs = lcccs_base.conditionally_select(
            cs.namespace(|| "compute U_new"),
            &Unew_non_base,
            &Boolean::from(is_base_case.clone()),
        )?;

        // Compute z_{i+1}
        let z_input = conditionally_select_vec_allocated_num(
            cs.namespace(|| "select input to F"),
            &z_0,
            &z_i,
            &Boolean::from(is_base_case),
        )?;

        let z_next = self
            .step_circuit
            .synthesize(&mut cs.namespace(|| "F"), &z_input)?;

        if z_next.len() != arity {
            return Err(SynthesisError::IncompatibleLengthVector(
                "z_next".to_string(),
            ));
        }

        // Compute the new hash H(params, Unew, i+1, z0, z_{i+1})
        let mut ro = G::ROCircuit::new(self.ro_consts, NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * arity);
        // ro.absorb(&params);
        for e in &z_0 {
            ro.absorb(e);
        }
        for e in &z_next {
            ro.absorb(e);
        }
        lcccs.absorb_in_ro(cs.namespace(|| "absorb U_new"), &mut ro)?;
        let hash_bits = ro.squeeze(cs.namespace(|| "output hash bits"), NUM_HASH_BITS)?;
        let hash = le_bits_to_num(cs.namespace(|| "convert hash to num"), &hash_bits)?;

        // Outputs the computed hash and u.X[1] that corresponds to the hash of the other circuit
        for X in Xs.into_iter() {
            X.inputize(cs.namespace(|| "Output unmodified hash of the other circuit"))?; // this circuit's Xs
        }
        hash.inputize(cs.namespace(|| "output new hash of this circuit"))?; // this circuit's x1

        Ok(z_next)
    }
}