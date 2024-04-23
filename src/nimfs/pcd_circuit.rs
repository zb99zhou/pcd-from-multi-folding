use bellpepper::gadgets::Assignment;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::{AllocatedNum, Num};
use ff::Field;
use serde::Serialize;
use crate::constants::NUM_HASH_BITS;
use crate::gadgets::cccs::{AllocatedCCCS, AllocatedCCCSPrimaryPart, AllocatedLCCCS, AllocatedLCCCSPrimaryPart, multi_folding_with_primary_part};
use crate::gadgets::ext_allocated_num::ExtendFunc;
use crate::gadgets::r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance};
use crate::gadgets::sumcheck::{AllocatedProof, enforce_compute_c_from_sigmas_and_thetas, enforce_interpolate_uni_poly, sumcheck_verify};
use crate::gadgets::utils::{alloc_num_equals, alloc_scalar_as_base,alloc_zero,conditionally_select_vec_allocated_num,le_bits_to_num, multi_and};
// use crate::gadgets::utils::{alloc_num_equals, alloc_scalar_as_base,le_bits_to_num, multi_and};
use crate::nimfs::ccs::cccs::{CCCSForBase, PointForScalar};
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::ccs::lcccs::LCCCSForBase;
use crate::nimfs::espresso::virtual_polynomial::VPAuxInfo;
use crate::nimfs::multifolding::NIMFSProof;
use crate::traits::{Group, ROCircuitTrait, ROConstantsCircuit, TEConstantsCircuit, TranscriptCircuitEngineTrait};
use crate::traits::circuit::PCDStepCircuit;
use crate::{Commitment, compute_digest};
use crate::gadgets::ecc::{AllocatedPoint, AllocatedSimulatedPoint};
use crate::r1cs::{R1CSInstance, RelaxedR1CSInstance};
use crate::traits::commitment::CommitmentTrait;

// R: the number of multi-folding PCD node
#[derive(Serialize, Clone)]
pub struct PCDUnitParams<G: Group, const ARITY: usize, const R: usize>{
    pub(crate) ccs: CCS<G>,
    pub(crate) limb_width: usize,
    pub(crate) n_limbs: usize,
    pub(crate) digest: G::Scalar,
}

impl<G: Group, const ARITY: usize, const R: usize> PCDUnitParams<G, ARITY, R> {
    pub fn new(
        limb_width: usize,
        n_limbs: usize,
        ccs: CCS<G>,
    ) -> Self {
        let mut pp = Self {
            ccs,
            limb_width,
            n_limbs,
            digest: G::Scalar::ZERO,
        };
        pp.digest = compute_digest::<G, PCDUnitParams<G, ARITY, R>>(&pp);

        pp
    }

    pub fn default_for_pcd(
        limb_width: usize,
        n_limbs: usize,
    ) -> Self {
        let mut pp = Self {
            ccs: CCS::default_r1cs(),
            limb_width,
            n_limbs,
            digest: G::Scalar::ZERO,
        };
        pp.digest = compute_digest::<G, PCDUnitParams<G, ARITY, R>>(&pp);

        pp
    }
}

#[derive(Clone)]
pub struct PCDUnitInputs<G: Group> {
    params: G::Scalar, // Hash(Shape of u2, Gens for u2). Needed for computing the challenge.
    z0: Vec<G::Base>,
    zi: Option<Vec<Vec<G::Base>>>,
    lcccs: Option<Vec<LCCCSForBase<G>>>,
    cccs: Option<Vec<CCCSForBase<G>>>,
    relaxed_r1cs_instance: Option<Vec<RelaxedR1CSInstance<G>>>,
    r1cs_instance: Option<R1CSInstance<G>>,
    new_lcccs_C: Option<PointForScalar<G>>,
    T: Option<Vec<Commitment<G>>>,
    proof: Option<NIMFSProof<G>>,
}

impl<G: Group> PCDUnitInputs<G> {
    /// Create new inputs/witness for the verification circuit
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        params: G::Scalar,
        z0: Vec<G::Base>,
        zi: Option<Vec<Vec<G::Base>>>,
        lcccs: Option<Vec<LCCCSForBase<G>>>,
        cccs: Option<Vec<CCCSForBase<G>>>,
        relaxed_r1cs_instance: Option<Vec<RelaxedR1CSInstance<G>>>,
        r1cs_instance: Option<R1CSInstance<G>>,
        new_lcccs_C: Option<PointForScalar<G>>,
        T: Option<Vec<Commitment<G>>>,
        proof: Option<NIMFSProof<G>>,
    ) -> Self {
        Self {
            params,
            z0,
            zi,
            lcccs,
            cccs,
            relaxed_r1cs_instance,
            r1cs_instance,
            new_lcccs_C,
            T,
            proof,
        }
    }
}

#[derive(Clone)]
pub struct PCDUnitPrimaryCircuit<'a, G, G1, SC, const ARITY: usize, const R: usize>
where
    G: Group,
    G1: Group,
    SC: PCDStepCircuit<G::Base, ARITY, R>
{
    params: &'a PCDUnitParams<G1, ARITY, R>,
    ro_consts: ROConstantsCircuit<G>, // random oracle
    te_consts: TEConstantsCircuit<G>, // Transcript Engine
    inputs: Option<PCDUnitInputs<G>>,
    step_circuit: &'a SC, // The function that is applied for each step
}

impl<'a, G, G1, SC, const ARITY: usize, const R: usize> PCDUnitPrimaryCircuit<'a, G, G1, SC, ARITY, R>
where
    G: Group,
    G1: Group,
    SC: PCDStepCircuit<G::Base, ARITY, R>
{
    /// Create a new verification circuit for the input relaxed r1cs instances
    pub const fn new(
        params: &'a PCDUnitParams<G1, ARITY, R>,
        inputs: Option<PCDUnitInputs<G>>,
        step_circuit: &'a SC,
        ro_consts: ROConstantsCircuit<G>,
        te_consts: TEConstantsCircuit<G>,
    ) -> Self {
        Self {
            params,
            inputs,
            step_circuit,
            ro_consts,
            te_consts,
        }
    }

    /// Allocate all witnesses and return
    fn alloc_witness<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
    ) -> Result<
        (
            AllocatedNum<G::Base>, Vec<AllocatedNum<G::Base>>, Vec<Vec<AllocatedNum<G::Base>>>,
            Vec<AllocatedLCCCS<G>>, Vec<AllocatedCCCS<G>>, AllocatedProof<G>,
            Vec<AllocatedRelaxedR1CSInstance<G>>, AllocatedR1CSInstance<G>,
            AllocatedSimulatedPoint<G>, Vec<AllocatedPoint<G>>,
        ),
        SynthesisError,
    > {
        // Allocate the params
        let params = alloc_scalar_as_base::<G, _>(
            cs.namespace(|| "params"),
            self.inputs.get().map_or(None, |inputs| Some(inputs.params)),
        )?;

        let nimfs_proof = AllocatedProof::from_witness::<_, R>(
            cs.namespace(|| "params"),
            self.inputs.as_ref().and_then(|i| i.proof.as_ref()),
        )?;

        // Allocate z0
        let z_0 = (0..ARITY)
            .map(|i| {
                AllocatedNum::alloc(cs.namespace(|| format!("z0_{i}")), || {
                    Ok(self.inputs.get()?.z0[i])
                })
            })
            .collect::<Result<Vec<AllocatedNum<G::Base>>, _>>()?;

        // Allocate zi. If inputs.zi is not provided (base case) allocate default value 0
        let z_i = (0..R).map(|i|
            (0..ARITY).map(|j|
                AllocatedNum::alloc(cs.namespace(|| format!("zi is {j}th_io for {i}th lcccs")), || {
                    Ok(self.inputs.get()?
                        .zi
                        .as_ref()
                        .map(|zs| zs[i][j])
                        .unwrap_or_default()
                    )
                })
            ).collect::<Result<Vec<_>, SynthesisError>>()
        )
            .collect::<Result<Vec<Vec<AllocatedNum<G::Base>>>, SynthesisError>>()?;

        // Allocate the running instance
        let lcccs = (0..R)
            .map(|i| {
                AllocatedLCCCS::alloc(
                    cs.namespace(|| format!("allocate instance lcccs_{i} to fold")),
                    self
                        .inputs
                        .as_ref()
                        .and_then(|inputs| inputs.lcccs.as_ref().map(|U| &U[i])),
                    ARITY,
                    (self.params.ccs.t, self.params.ccs.s),
                    (self.params.limb_width, self.params.n_limbs),
                )
            })
            .collect::<Result<Vec<AllocatedLCCCS<G>>, _>>()?;

        // Allocate the instance to be folded in
        let cccs = (0..R)
            .map(|i| {
                AllocatedCCCS::alloc(
                    cs.namespace(|| format!("allocate instance cccs_{i} to fold")),
                    self
                        .inputs
                        .as_ref()
                        .and_then(|inputs| inputs.cccs.as_ref().map(|u|&u[i])),
                    self.params.limb_width,
                    self.params.n_limbs,
                    ARITY,
                )
            })
            .collect::<Result<Vec<AllocatedCCCS<G>>, _>>()?;
        let relaxed_r1cs_inst = (0..R)
            .map(|i| {
                AllocatedRelaxedR1CSInstance::alloc(
                    cs.namespace(|| format!("Allocate {i}th relaxed r1cs instance")),
                    self.inputs.as_ref().and_then(|inputs| {
                        inputs.relaxed_r1cs_instance.as_ref().and_then(|U| Some(&U[i]))
                    }),
                    self.params.limb_width,
                    self.params.n_limbs,
                )
            })
            .collect::<Result<Vec<AllocatedRelaxedR1CSInstance<G>>, _>>()?;
        let r1cs_inst = AllocatedR1CSInstance::alloc(
            cs.namespace(|| "Allocate r1cs instance"),
            self.inputs.as_ref().and_then(|inputs| {
                inputs.r1cs_instance.as_ref().and_then(|u| Some(u))
            }),
        )?;

        let new_lcccs_C = AllocatedSimulatedPoint::alloc(
            cs.namespace(|| "Allocate new lcccs C"),
            self.inputs.as_ref().and_then(|inputs| {
                inputs.new_lcccs_C.as_ref().and_then(|U| Some(*U))
            }),
            self.params.limb_width,
            self.params.n_limbs,
        )?;

        let T = (0..R)
            .map(|i| {
                AllocatedPoint::alloc(
                    cs.namespace(|| format!("Allocate T_{i}")),
                    self.inputs
                        .as_ref()
                        .and_then(|inputs|
                            inputs.T.as_ref().map(|T| T[i].clone().to_coordinates())
                        )
                )
            })
            .collect::<Result<Vec<AllocatedPoint<G>>, _>>()?;
        for (i,t) in T.iter().enumerate(){
            t.check_on_curve(cs.namespace(|| format!("check T_{i} on curve")))?;
        }

        Ok((
            params, z_0, z_i,
            lcccs, cccs, nimfs_proof,
            relaxed_r1cs_inst, r1cs_inst, new_lcccs_C, T
        ))
    }

    /// Synthesizes base case and returns the new `LCCCS`
    fn synthesize_genesis_based_nimfs<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
    ) -> Result<AllocatedLCCCS<G>, SynthesisError> {
        let primary_part = AllocatedLCCCSPrimaryPart::default(
            cs.namespace(|| "Allocate lcccs default"),
            ARITY,
            self.params.ccs.s,
            self.params.ccs.t,
        )?;
        let second_part = AllocatedSimulatedPoint::default(
            cs.namespace(|| "Allocate second part default Simulated Point"),
            self.params.limb_width,
            self.params.n_limbs,
        )?;

        Ok(AllocatedLCCCS::new(primary_part, second_part))
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

impl<'a, G, G1, SC, const ARITY: usize, const R: usize> PCDUnitPrimaryCircuit<'a, G, G1, SC, ARITY, R>
where
    G: Group<Base = <G1 as Group>::Scalar>,
    G1: Group<Base = <G as Group>::Scalar>,
    SC: PCDStepCircuit<G::Base, ARITY, R>
{
    /// synthesize circuit giving constraint system
    pub fn synthesize<CS: ConstraintSystem<<G as Group>::Base>>(
        self,
        cs: &mut CS,
    ) -> Result<Vec<AllocatedNum<G::Base>>, SynthesisError> {
        // Allocate all witnesses
        let (
            params, z_0, z_i,
            lcccs, cccs, nimfs_proof,
            relaxed_r1cs_inst, r1cs_inst, new_lcccs_second_part, T
        ) = self.alloc_witness(cs.namespace(|| "allocate the circuit witness"))?;

        // Compute variable indicating if this is the base case
        let zero = alloc_zero(cs.namespace(|| "zero"))?;
        let mut is_base_case_flags = Vec::new();
        for (i, l) in lcccs.iter().enumerate() {
            is_base_case_flags.push(l.is_null(cs.namespace(|| format!("{}th lcccs", i)), &zero)?);
        }
        for (i, c) in cccs.iter().enumerate() {
            is_base_case_flags.push(c.is_null(cs.namespace(|| format!("{}th cccs", i)), &zero)?);
        }
        let is_base_case = Boolean::from(multi_and(cs.namespace(|| "is base case"), &is_base_case_flags)?);

        let is_correct_public_input = self.check_public_input(
            cs.namespace(|| "is_correct_public_input"),
            &cccs,
            &params,
            &z_0,
            &z_i,
            &lcccs,
            &relaxed_r1cs_inst
        )?;
        Boolean::enforce_equal(
            cs.namespace(|| "is_correct_public_input or is_base case"),
            &is_correct_public_input,
            &is_base_case.not()
        )?;

        // cs.print_vers_cons();
        // Synthesize the circuit for the base case and get the new running instance
        let lcccs_base = self.synthesize_genesis_based_nimfs(cs.namespace(|| "generate base case based nimfs"))?;
        // cs.print_vers_cons();
        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let (new_lcccs_primary_part, check_non_base_pass) = self
            .synthesize_based_nimfs(
                cs.namespace(|| "generate non base case based nimfs"),
                &self.params,
                &lcccs.into_iter().map(|l| l.primary_part).collect::<Vec<_>>(),
                &cccs.into_iter().map(|l| l.primary_part).collect::<Vec<_>>(),
                &nimfs_proof
            )?;
        let new_lcccs = AllocatedLCCCS::new(new_lcccs_primary_part, new_lcccs_second_part);

        // Either check_non_base_pass=true or we are in the base case
        Boolean::enforce_equal(
            cs.namespace(|| "check_non_base_pass nor base_case"),
            &check_non_base_pass.into(),
            &is_base_case,
        )?;

        // Update the lcccs and relaxed R1CS instance
        let new_lcccs = lcccs_base.conditionally_select(
            cs.namespace(|| "compute U_new"),
            &new_lcccs,
            &Boolean::from(is_base_case.clone()),
        )?;
        let relaxed_r1cs_inst = self.synthesize_based_nifs(
            cs.namespace(|| "generate non base case based nifs"),
            &params,
            relaxed_r1cs_inst,
            &r1cs_inst,
            T,
        )?;

        // select correct z
        let z_input = z_i
            .into_iter()
            .enumerate()
            .map(|(i, z)|
                conditionally_select_vec_allocated_num(
                    cs.namespace(|| format!("select {i}th input to F")),
                    &z_0,
                    &z,
                    &Boolean::from(is_base_case.clone()),
                )
            )
            .collect::<Result<Vec<Vec<_>>, SynthesisError>>()?;

        let new_z = self
            .step_circuit
            .synthesize(
                &mut cs.namespace(|| "F"),
                &z_input.iter().map(|z| &z[..]).collect::<Vec<_>>()
            )?;
        if new_z.len() != ARITY {
            return Err(SynthesisError::IncompatibleLengthVector(
                "z_next".to_string(),
            ));
        }

        let hash = self.commit_explicit_public_input(
            cs.namespace(|| "commit public input"),
            &params,
            &z_0,
            &new_z,
            &new_lcccs,
            &relaxed_r1cs_inst
        )?;
        hash.inputize(cs.namespace(|| "output new hash of this circuit"))?; // this circuit's public input
        // let hash = AllocatedNum::<<G1 as Group>::Scalar>::one(cs.namespace(|| "")).unwrap();
        // hash.inputize(cs.namespace(|| "output new hash of this circuit"))?; // this circuit's public input
        // let new_z = vec![AllocatedNum::<<G1 as Group>::Scalar>::one(cs.namespace(|| "")).unwrap(); ARITY];
        Ok(new_z)
    }


    /// Synthesizes non-base case and returns the new `LCCCS`
    /// And a boolean indicating if all checks pass
    #[allow(clippy::too_many_arguments)]
    fn synthesize_based_nimfs<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        params: &PCDUnitParams<G1, ARITY, R>,
        lcccs: &[AllocatedLCCCSPrimaryPart<G>],
        cccs: &[AllocatedCCCSPrimaryPart<G>],
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
            cs.namespace(|| "check c"),
            &c,
            &g_on_rxprime_from_sumcheck_last_eval
        )?;
        let check_pass3 = alloc_num_equals(
            cs.namespace(|| "check evaluation"),
            &sumcheck_subclaim.expected_evaluation,
            &g_on_rxprime_from_sumcheck_last_eval
        )?;

        // Step 6: Get the folding challenge
        let rho = transcript.squeeze(cs.namespace(|| "alloc rho"), b"rho")?;

        // Run NIMFS Verifier part 1
        let mut new_lcccs = multi_folding_with_primary_part(
            cs.namespace(|| "compute fold of U and u"),
            &lcccs,
            &cccs,
            rho,
            &proof.sigmas,
            &proof.thetas,
        )?;
        new_lcccs.r_x = r_x_prime;

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

    /// Synthesizes non-base case and returns the new relaxed `R1CSInstance`
    /// And a boolean indicating if all checks pass
    #[allow(clippy::too_many_arguments)]
    fn synthesize_based_nifs<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        params: &AllocatedNum<G::Base>,
        mut U: Vec<AllocatedRelaxedR1CSInstance<G>>,
        u: &AllocatedR1CSInstance<G>,
        mut T: Vec<AllocatedPoint<G>>,
    ) -> Result<AllocatedRelaxedR1CSInstance<G>, SynthesisError> {
        assert!(!U.is_empty());
        let last_T = T.pop().unwrap();
        let mut U_folded_U = U.remove(0);

        // Run NIFS Verifier
        use itertools::Itertools;
        for (U, T) in U.into_iter().zip_eq(T){
            U_folded_U = U_folded_U.fold_with_relaxed_r1cs(
                cs.namespace(|| "compute fold of U and U"),
                params,
                &U,
                &T,
                self.ro_consts.clone(),
                self.params.limb_width,
                self.params.n_limbs
            )?;
        }
        let U_folded = U_folded_U.fold_with_r1cs(
            cs.namespace(|| "compute fold of U and u"),
            params,
            u,
            &last_T,
            self.ro_consts.clone(),
            self.params.limb_width,
            self.params.n_limbs,
        )?;

        Ok(U_folded)
    }

    /// check the correctness of the all cccs's X(public input)
    pub fn check_public_input<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        cccs: &[AllocatedCCCS<G>],
        params: &AllocatedNum<G::Base>,
        z_0: &[AllocatedNum<G::Base>],
        new_z: &[Vec<AllocatedNum<G::Base>>],
        lcccs: &[AllocatedLCCCS<G>],
        relaxed_r1cs_inst: &[AllocatedRelaxedR1CSInstance<G>],
    ) -> Result<Boolean, SynthesisError> {
        let mut is_correct = Vec::new();
        for (i, c) in cccs.iter()
            .enumerate()
        {
            let public_hash = self.commit_explicit_public_input(
                cs.namespace(|| "commit public input"),
                params,
                &z_0,
                &new_z[i],
                &lcccs[i],
                &relaxed_r1cs_inst[i]
            )?;
            let is_eq = alloc_num_equals(
                cs.namespace(|| "check public_hash"),
                &public_hash,
                &c.primary_part.Xs[0]
            )?;
            is_correct.push(is_eq.into())
        }
        multi_and(cs.namespace(|| "is correct public inputs"), &is_correct).map(Into::into)
    }

    /// Compute the new hash H(params, z0, z, lcccs, relaxed R1CS instance)
    pub fn commit_explicit_public_input<CS: ConstraintSystem<<G as Group>::Base>>(
        &self,
        mut cs: CS,
        params: &AllocatedNum<G::Base>,
        z_0: &[AllocatedNum<G::Base>],
        new_z: &[AllocatedNum<G::Base>],
        lcccs: &AllocatedLCCCS<G>,
        relaxed_r1cs_inst: &AllocatedRelaxedR1CSInstance<G>,
    ) -> Result<AllocatedNum<G::Base>, SynthesisError> {
        let num_absorbs = 1 + 2 * ARITY + lcccs.element_num() + relaxed_r1cs_inst.element_num();
        let mut ro = G::ROCircuit::new(self.ro_consts.clone(), num_absorbs);

        ro.absorb(params);
        z_0.iter().for_each(|e| ro.absorb(e));
        new_z.iter().for_each(|e| ro.absorb(e));
        lcccs.absorb_in_ro(cs.namespace(|| "absorb lcccs"), &mut ro)?;
        relaxed_r1cs_inst.absorb_in_ro(cs.namespace(|| "absorb relaxed r1cs instance"), &mut ro)?;

        let hash_bits = ro.squeeze(cs.namespace(|| "output hash bits"), NUM_HASH_BITS)?;
        let hash = le_bits_to_num(cs.namespace(|| "convert hash to num"), &hash_bits)?;
        Ok(hash)
    }
}