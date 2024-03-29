use bellpepper::gadgets::Assignment;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::{AllocatedNum, Num};
use ff::Field;
use serde::Serialize;
use crate::constants::{NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use crate::gadgets::cccs::{AllocatedCCCSPrimaryPart, AllocatedLCCCSPrimaryPart, multi_folding_with_primary_part};
use crate::gadgets::ext_allocated_num::ExtendFunc;
use crate::gadgets::r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance};
use crate::gadgets::sumcheck::{AllocatedProof, enforce_compute_c_from_sigmas_and_thetas, enforce_interpolate_uni_poly, sumcheck_verify};
use crate::gadgets::utils::{alloc_num_equals, alloc_zero, conditionally_select_vec_allocated_num, le_bits_to_num, multi_and};
use crate::nimfs::ccs::cccs::CCCS;
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::espresso::virtual_polynomial::VPAuxInfo;
use crate::nimfs::multifolding::NIMFSProof;
use crate::traits::{Group, ROCircuitTrait, ROConstantsCircuit, TEConstantsCircuit, TranscriptCircuitEngineTrait};
use crate::traits::circuit::StepCircuit;
use crate::{Commitment, compute_digest};
use crate::gadgets::ecc::AllocatedPoint;
use crate::traits::commitment::CommitmentTrait;

#[derive(Serialize)]
pub struct PCDUnitParams<G: Group>{
    pub(crate) mu: usize,
    pub(crate) nu: usize,
    pub(crate) ccs: CCS<G>,
    pub(crate) io_num: usize,
    pub(crate) limb_width: usize,
    pub(crate) n_limbs: usize,
    pub(crate) digest: G::Scalar,
}

impl<G: Group> PCDUnitParams<G> {
    pub fn new(
        limb_width: usize,
        n_limbs: usize,
        mu: usize,
        nu: usize,
        io_num: usize,
        ccs: CCS<G>
    ) -> Self {
        let mut pp = Self {
            mu,
            nu,
            ccs,
            io_num,
            limb_width,
            n_limbs,
            digest: G::Scalar::ZERO,
        };
        pp.digest = compute_digest::<G, PCDUnitParams<G>>(&pp);

        pp
    }

}

// #[derive(Debug, Serialize, Deserialize)]
// #[serde(bound = "")]
#[derive(Clone)]
pub struct PCDUnitInputs<G: Group> {
    params: G::Base, // Hash(Shape of u2, Gens for u2). Needed for computing the challenge.
    z0: Vec<G::Base>,
    zi: Option<Vec<G::Base>>,
    lcccs: Option<Vec<LCCCS<G>>>,
    cccs: Option<Vec<CCCS<G>>>,
    r: usize,
    T: Option<Vec<Commitment<G>>>,
}

impl<G: Group> PCDUnitInputs<G> {
    /// Create new inputs/witness for the verification circuit
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        params: G::Base,
        z0: Vec<G::Base>,
        zi: Option<Vec<G::Base>>,
        lcccs: Option<Vec<LCCCS<G>>>,
        cccs: Option<Vec<CCCS<G>>>,
        r: usize,
        T: Option<Vec<Commitment<G>>>,
    ) -> Self {
        Self {
            params,
            z0,
            zi,
            lcccs,
            cccs,
            r,
            T,
        }
    }
}

#[derive(Clone)]
pub struct PCDUnitPrimaryCircuit<'a, G: Group, G1: Group, SC: StepCircuit<G::Base>> {
    params: &'a PCDUnitParams<G1>,
    ro_consts: ROConstantsCircuit<G>, // random oracle
    te_consts: TEConstantsCircuit<G>, // Transcript Engine
    inputs: Option<PCDUnitInputs<G>>,
    proof: NIMFSProof<G>,
    step_circuit: &'a SC, // The function that is applied for each step
}

impl<'a, G: Group, G1: Group, SC: StepCircuit<G::Base>> PCDUnitPrimaryCircuit<'a, G, G1, SC> {
    /// Create a new verification circuit for the input relaxed r1cs instances
    pub const fn new(
        params: &'a PCDUnitParams<G1>,
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
    fn alloc_witness<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        arity: usize,
    ) -> Result<
        (
            AllocatedProof<G>,
            Vec<AllocatedNum<G::Base>>,
            Vec<AllocatedNum<G::Base>>,
            Vec<AllocatedLCCCSPrimaryPart<G>>,
            Vec<AllocatedCCCSPrimaryPart<G>>,
            Vec<AllocatedPoint<G>>,
        ),
        SynthesisError,
    > {
        // Allocate the params
        let nimfs_proof = AllocatedProof::from_witness(
            cs.namespace(|| "params"),
            &self.proof,
        )?;

        // Allocate z0
        let z_0 = (0..arity)
            .map(|i| {
                AllocatedNum::alloc(cs.namespace(|| format!("z0_{i}")), || {
                    Ok(self.inputs.get()?.z0[i])
                })
            })
            .collect::<Result<Vec<AllocatedNum<G::Base>>, _>>()?;

        // Allocate zi. If inputs.zi is not provided (base case) allocate default value 0
        let zero = vec![G::Base::ZERO; arity];
        let z_i = (0..arity)
            .map(|i| {
                AllocatedNum::alloc(cs.namespace(|| format!("zi_{i}")), || {
                    Ok(self.inputs.get()?.zi.as_ref().unwrap_or(&zero)[i])
                })
            })
            .collect::<Result<Vec<AllocatedNum<G::Base>>, _>>()?;

        // Allocate the running instance

        let lcccs = (0..self.params.mu)
            .map(|i| {
                AllocatedLCCCSPrimaryPart::alloc(
                    cs.namespace(|| format!("allocate instance lcccs_{i} to fold")),
                    self
                        .inputs
                        .as_ref()
                        .and_then(|inputs| inputs.lcccs.as_ref().map(|U|&U[i])),
                    self.params.io_num,
                    self.params.limb_width,
                    self.params.n_limbs,
                )
            })
            .collect::<Result<Vec<AllocatedLCCCSPrimaryPart<G>>, _>>()?;

        // Allocate the instance to be folded in
        let cccs = (0..self.params.mu)
            .map(|i| {
                AllocatedCCCSPrimaryPart::alloc(
                    cs.namespace(|| format!("allocate instance cccs_{i} to fold")),
                    self
                        .inputs
                        .as_ref()
                        .and_then(|inputs| inputs.cccs.as_ref().map(|u|&u[i])),
                    self.params.io_num,
                )
            })
            .collect::<Result<Vec<AllocatedCCCSPrimaryPart<G>>, _>>()?;
        
        let T = (0..self.params.mu)
            .map(|i| {
                AllocatedPoint::alloc(
                    cs.namespace(|| format!("Allocate T_{i}")),
                    self
                        .inputs
                        .as_ref()
                        .and_then(|inputs| inputs.T.as_ref().map(|T| T[i].clone().to_coordinates())),
                )
            })
            .collect::<Result<Vec<AllocatedPoint<G>>, _>>()?;
        
        for (i,t) in T.iter().enumerate(){
            t.check_on_curve(cs.namespace(|| format!("check T_{i} on curve")))?;
        }

        Ok((nimfs_proof, z_0, z_i, lcccs, cccs, T))
    }

    /// Synthesizes base case and returns the new `LCCCS`
    fn synthesize_genesis_based_nimfs<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
    ) -> Result<AllocatedLCCCSPrimaryPart<G>, SynthesisError> {
        AllocatedLCCCSPrimaryPart::default(
            cs.namespace(|| "Allocate lcccs default"),
            self.params.io_num,
            self.params.ccs.s,
            self.params.ccs.t,
            self.params.limb_width,
            self.params.n_limbs,
        )
    }

    /// Synthesizes base case and returns the new `relaxed r1cs instance`
    fn synthesize_genesis_based_nifs<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
    ) -> Result<AllocatedRelaxedR1CSInstance<G>, SynthesisError> {
        AllocatedRelaxedR1CSInstance::default(
            cs.namespace(|| "Allocate relaxed r1cs instance default"),
            self.params.limb_width,
            self.params.n_limbs,
        )
    }
}

impl<'a, G, G1, SC: StepCircuit<G::Base>> PCDUnitPrimaryCircuit<'a, G, G1, SC>
where
    G: Group<Base = <G1 as Group>::Scalar>,
    G1: Group<Base = <G as Group>::Scalar>,
{
    /// synthesize circuit giving constraint system
    pub fn synthesize<CS: ConstraintSystem<<G as Group>::Base>>(
        self,
        cs: &mut CS,
    ) -> Result<Vec<AllocatedNum<G::Base>>, SynthesisError> {
        let arity = self.step_circuit.arity();

        // Allocate all witnesses
        let (
            nimfs_proof, z_0, z_i,
            lcccs, cccs, _t
        ) = self.alloc_witness(cs.namespace(|| "allocate the circuit witness"), arity)?;
        let Xs = cccs.iter().flat_map(|c|c.Xs.to_vec()).collect::<Vec<_>>();

        // Compute variable indicating if this is the base case
        let zero = alloc_zero(cs.namespace(|| "zero"))?;
        let mut is_base_case_flags = Vec::new();
        for (i, l) in lcccs.iter().enumerate() {
            is_base_case_flags.push(l.is_null(cs.namespace(|| format!("{}th lcccs", i)), &zero)?);
        }
        for (i, c) in cccs.iter().enumerate() {
            is_base_case_flags.push(c.is_null(cs.namespace(|| format!("{}th cccs", i)), &zero)?);
        }
        let is_base_case = multi_and(cs.namespace(|| "is base case"), &is_base_case_flags)?;

        // Synthesize the circuit for the base case and get the new running instance
        let lcccs_base = self.synthesize_genesis_based_nimfs(cs.namespace(|| "generate base case based nimfs"))?;

        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let (Unew_non_base, check_non_base_pass) = self
            .synthesize_based_nimfs(
                cs.namespace(|| "generate non base case based nimfs"),
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


    /// Synthesizes non-base case and returns the new `LCCCS`
    /// And a boolean indicating if all checks pass
    #[allow(clippy::too_many_arguments)]
    fn synthesize_based_nimfs<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        params: &PCDUnitParams<G1>,
        _z_0: &[AllocatedNum<G::Base>],
        _z_i: &[AllocatedNum<G::Base>],
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
            |_lc| sum_v_j_gamma_lc.lc(G::Base::ONE),
            |lc| lc + CS::one(),
            |lc| lc + sum_v_j_gamma.get_variable(),
        );

        let vp_aux_info = VPAuxInfo::<G::Base> {
            max_degree: params.ccs.d + 1,
            num_variables: params.ccs.s,
            phantom: std::marker::PhantomData::<G::Base>,
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
        let c = enforce_compute_c_from_sigmas_and_thetas::<_, G, G1>(
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



    /// Synthesizes non base case and returns the new relaxed `R1CSInstance`
    /// And a boolean indicating if all checks pass
    #[allow(clippy::too_many_arguments)]
    fn synthesize_based_nifs<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        params: &AllocatedNum<G::Base>,
        U: Vec<AllocatedRelaxedR1CSInstance<G>>,
        u: &AllocatedR1CSInstance<G>,
        T: Vec<AllocatedPoint<G>>,
        arity: usize,
    ) -> Result<(AllocatedRelaxedR1CSInstance<G>, AllocatedBit), SynthesisError> {
        assert!(!U.is_empty());
        // Check that u.x[0] = Hash(params, U)
        let Len = U.len();
        let mut ro = G::ROCircuit::new(
            self.ro_consts.clone(),
            NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * arity,
        );
        ro.absorb(params);
        for x in 0..Len{
            U[x].absorb_in_ro(cs.namespace(|| "absorb U"), &mut ro)?;
        }

        let hash_bits = ro.squeeze(cs.namespace(|| "Input hash"), NUM_HASH_BITS)?;
        let hash = le_bits_to_num(cs.namespace(|| "bits to hash"), &hash_bits)?;
        let check_pass = alloc_num_equals(
            cs.namespace(|| "check consistency of u.X[0] with H(params, U, i)"),
            &u.X0,
            &hash,
        )?;

        // Run NIFS Verifier
        let mut U_temp = U[0].clone();
        for x in 1..Len{
            U_temp = U_temp.fold_with_relaxed_r1cs(
                cs.namespace(|| "compute fold of U and U"),
                params,
                &U[x],
                &T[x-1],
                self.ro_consts.clone(),
                self.params.limb_width,
                self.params.n_limbs
            )?;
        }
        let U_fold = U_temp.fold_with_r1cs(
            cs.namespace(|| "compute fold of U and u"),
            params,
            u,
            &T[Len-1],
            self.ro_consts.clone(),
            self.params.limb_width,
            self.params.n_limbs,
        )?;
        Ok((U_fold, check_pass))
    }
}