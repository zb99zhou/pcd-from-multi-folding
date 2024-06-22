use crate::constants::{NUM_CHALLENGE_BITS, NUM_HASH_BITS};
use crate::gadgets::cccs::{
  multi_folding_with_primary_part, AllocatedCCCS, AllocatedCCCSPrimaryPart,
};
use crate::gadgets::ecc::{AllocatedPoint, AllocatedSimulatedPoint};
use crate::gadgets::ext_allocated_num::ExtendFunc;
use crate::gadgets::lcccs::{AllocatedLCCCS, AllocatedLCCCSPrimaryPart};
use crate::gadgets::nonnative::bignat::BigNat;
use crate::gadgets::r1cs_instance::{
  AllocatedR1CSInstanceBasedSimulatedX, AllocatedRelaxedR1CSInstance,
};
use crate::gadgets::sumcheck::{
  enforce_compute_c_from_sigmas_and_thetas, sumcheck_verify, AllocatedProof,
};
use crate::gadgets::utils::{
  alloc_num_equals, alloc_scalar_as_base, conditionally_select_vec_allocated_num,
  from_le_bits_to_num, le_bits_to_num, multi_and,
};
use crate::nifs::r1cs::{R1CSInstance, RelaxedR1CSInstance};
use crate::nimfs::ccs::cccs::{CCCSForBase, PointForScalar};
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::ccs::lcccs::{LCCCSForBase, LCCCS};
use crate::nimfs::espresso::virtual_polynomial::VPAuxInfo;
use crate::nimfs::multifolding::NIMFSProof;
use crate::pcd_aux_circuit::NovaAuxiliaryParams;
use crate::traits::circuit::PCDStepCircuit;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::{
  Group, ROCircuitTrait, ROConstantsCircuit, TEConstantsCircuit, TranscriptCircuitEngineTrait,
};
use crate::{compute_digest, Commitment};
use bellpepper::gadgets::Assignment;
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::{AllocatedNum, Num};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;
use itertools::{Either, Itertools};
use serde::Serialize;

// R: the number of multi-folding PCD node
#[derive(Serialize, Clone)]
pub struct PCDUnitParams<G: Group, const ARITY: usize, const R: usize> {
  pub(crate) ccs: CCS<G>,
  pub(crate) limb_width: usize,
  pub(crate) n_limbs: usize,
  pub(crate) digest: G::Scalar,
}

impl<G: Group, const ARITY: usize, const R: usize> PCDUnitParams<G, ARITY, R> {
  pub fn new(limb_width: usize, n_limbs: usize, ccs: CCS<G>) -> Self {
    let mut pp = Self {
      ccs,
      limb_width,
      n_limbs,
      digest: G::Scalar::ZERO,
    };
    pp.digest = compute_digest::<G, PCDUnitParams<G, ARITY, R>>(&pp);

    pp
  }

  pub fn default_for_pcd(limb_width: usize, n_limbs: usize, s: usize, s_prime: usize) -> Self {
    let mut pp = Self {
      ccs: CCS::default_r1cs(s, s_prime),
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
  secondary_params: G::Scalar,
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
    secondary_params: G::Scalar,
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
      secondary_params,
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
pub struct PCDUnitPrimaryCircuit<'a, G1, G2, SC, const ARITY: usize, const R: usize>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  SC: PCDStepCircuit<G1::Base, ARITY, R>,
{
  params: &'a PCDUnitParams<G2, ARITY, R>,
  secondary_params: &'a NovaAuxiliaryParams<G1>,
  ro_consts: ROConstantsCircuit<G1>, // random oracle
  te_consts: TEConstantsCircuit<G1>, // Transcript Engine
  inputs: Option<PCDUnitInputs<G1>>,
  pub step_circuit: &'a SC, // The function that is applied for each step
}

impl<'a, G1, G2, SC, const ARITY: usize, const R: usize>
  PCDUnitPrimaryCircuit<'a, G1, G2, SC, ARITY, R>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  SC: PCDStepCircuit<G1::Base, ARITY, R>,
{
  /// Create a new verification circuit for the input relaxed r1cs instances
  pub const fn new(
    params: &'a PCDUnitParams<G2, ARITY, R>,
    secondary_params: &'a NovaAuxiliaryParams<G1>,
    inputs: Option<PCDUnitInputs<G1>>,
    step_circuit: &'a SC,
    ro_consts: ROConstantsCircuit<G1>,
    te_consts: TEConstantsCircuit<G1>,
  ) -> Self {
    Self {
      params,
      inputs,
      step_circuit,
      ro_consts,
      te_consts,
      secondary_params,
    }
  }

  /// Allocate all witnesses and return
  fn alloc_witness<CS: ConstraintSystem<<G1 as Group>::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<
    (
      AllocatedNum<G1::Base>,
      AllocatedNum<G1::Base>,
      Vec<AllocatedNum<G1::Base>>,
      Vec<Vec<AllocatedNum<G1::Base>>>,
      Vec<AllocatedLCCCS<G1>>,
      Vec<AllocatedCCCS<G1>>,
      AllocatedProof<G1>,
      Vec<AllocatedRelaxedR1CSInstance<G1>>,
      AllocatedR1CSInstanceBasedSimulatedX<G1>,
      AllocatedSimulatedPoint<G1>,
      Vec<AllocatedPoint<G1>>,
    ),
    SynthesisError,
  > {
    // Allocate the params
    let primary_params = alloc_scalar_as_base::<G1, _>(
      cs.namespace(|| "primary_params"),
      self.inputs.get().map_or(None, |inputs| Some(inputs.params)),
    )?;
    let secondary_params = alloc_scalar_as_base::<G1, _>(
      cs.namespace(|| "secondary_params"),
      self
        .inputs
        .get()
        .map_or(None, |inputs| Some(inputs.secondary_params)),
    )?;

    let nimfs_proof = AllocatedProof::from_witness::<_, R>(
      cs.namespace(|| "nimfs_proof"),
      self.inputs.as_ref().and_then(|i| i.proof.as_ref()),
      self.params.ccs.s,
      self.params.ccs.d,
      self.params.ccs.t,
    )?;

    // Allocate z0
    let z_0 = (0..ARITY)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("z0_{i}")), || {
          Ok(self.inputs.get()?.z0[i])
        })
      })
      .collect::<Result<Vec<AllocatedNum<G1::Base>>, _>>()?;

    // Allocate zi. If inputs.zi is not provided (base case) allocate default value 0
    let z_i = (0..R)
      .map(|i| {
        (0..ARITY)
          .map(|j| {
            AllocatedNum::alloc(
              cs.namespace(|| format!("zi is {j}th_io for {i}th lcccs")),
              || {
                Ok(
                  self
                    .inputs
                    .get()?
                    .zi
                    .as_ref()
                    .map(|zs| zs[i][j])
                    .unwrap_or_default(),
                )
              },
            )
          })
          .collect::<Result<Vec<_>, SynthesisError>>()
      })
      .collect::<Result<Vec<Vec<AllocatedNum<G1::Base>>>, SynthesisError>>()?;

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
      .collect::<Result<Vec<AllocatedLCCCS<G1>>, _>>()?;

    // Allocate the instance to be folded in
    let cccs = (0..R)
      .map(|i| {
        AllocatedCCCS::alloc(
          cs.namespace(|| format!("allocate instance cccs_{i} to fold")),
          self
            .inputs
            .as_ref()
            .and_then(|inputs| inputs.cccs.as_ref().map(|u| &u[i])),
          self.params.limb_width,
          self.params.n_limbs,
          ARITY,
        )
      })
      .collect::<Result<Vec<AllocatedCCCS<G1>>, _>>()?;
    let relaxed_r1cs_inst = (0..R)
      .map(|i| {
        AllocatedRelaxedR1CSInstance::alloc(
          cs.namespace(|| format!("Allocate {i}th relaxed r1cs instance")),
          self
            .inputs
            .as_ref()
            .and_then(|inputs| inputs.relaxed_r1cs_instance.as_ref().map(|U| &U[i])),
          self.secondary_params.io_num,
          self.params.limb_width,
          self.params.n_limbs,
        )
      })
      .collect::<Result<Vec<AllocatedRelaxedR1CSInstance<G1>>, _>>()?;
    let r1cs_inst = AllocatedR1CSInstanceBasedSimulatedX::alloc(
      cs.namespace(|| "Allocate r1cs instance"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.r1cs_instance.as_ref()),
      self.secondary_params.io_num,
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    let new_lcccs_C = AllocatedSimulatedPoint::alloc(
      cs.namespace(|| "Allocate new lcccs C"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.new_lcccs_C.as_ref().map(|C| *C)),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    let T = (0..R)
      .map(|i| {
        AllocatedPoint::alloc(
          cs.namespace(|| format!("Allocate T_{i}")),
          self
            .inputs
            .as_ref()
            .and_then(|inputs| inputs.T.as_ref().map(|T| T[i].clone().to_coordinates())),
        )
      })
      .collect::<Result<Vec<AllocatedPoint<G1>>, _>>()?;
    for (i, t) in T.iter().enumerate() {
      t.check_on_curve(cs.namespace(|| format!("check T_{i} on curve")))?;
    }

    Ok((
      primary_params,
      secondary_params,
      z_0,
      z_i,
      lcccs,
      cccs,
      nimfs_proof,
      relaxed_r1cs_inst,
      r1cs_inst,
      new_lcccs_C,
      T,
    ))
  }

  /// Synthesizes base case and returns the new `LCCCS`
  fn synthesize_genesis_based_nimfs<CS: ConstraintSystem<<G1 as Group>::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<AllocatedLCCCS<G1>, SynthesisError> {
    let default_lcccs =
      LCCCSForBase::<G1>::from(LCCCS::<G2>::default_for_pcd(self.params.ccs.clone()));
    let lcccs = AllocatedLCCCS::alloc(
      cs.namespace(|| "allocate default instance lcccs to fold"),
      Some(&default_lcccs),
      ARITY,
      (self.params.ccs.t, self.params.ccs.s),
      (self.params.limb_width, self.params.n_limbs),
    )?;
    Ok(lcccs)
  }

  /// Synthesizes base case and returns the new `relaxed r1cs instance`
  fn synthesize_genesis_based_nifs<CS: ConstraintSystem<<G1 as Group>::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<AllocatedRelaxedR1CSInstance<G1>, SynthesisError> {
    AllocatedRelaxedR1CSInstance::default(
      cs.namespace(|| "Allocate relaxed r1cs instance default"),
      self.params.limb_width,
      self.params.n_limbs,
      self.secondary_params.io_num,
    )
  }
}

impl<'a, G1, G2, SC, const ARITY: usize, const R: usize>
  PCDUnitPrimaryCircuit<'a, G1, G2, SC, ARITY, R>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  SC: PCDStepCircuit<G1::Base, ARITY, R>,
{
  /// synthesize circuit giving constraint system
  pub fn synthesize<CS: ConstraintSystem<<G1 as Group>::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<G1::Base>>, SynthesisError> {
    // Allocate all witnesses
    let (
      primary_params,
      secondary_params,
      z_0,
      z_i,
      lcccs,
      cccs,
      nimfs_proof,
      relaxed_r1cs_inst,
      mut r1cs_inst,
      new_lcccs_second_part,
      T,
    ) = self.alloc_witness(cs.namespace(|| "allocate the circuit witness"))?;

    // Compute variable indicating if this is the base case
    let zero = crate::gadgets::utils::alloc_zero(cs.namespace(|| "zero"))?;
    let mut is_base_case_flags = Vec::new();
    for (i, l) in lcccs.iter().enumerate() {
      is_base_case_flags.push(l.is_null(cs.namespace(|| format!("{}th lcccs", i)), &zero)?);
    }
    for (i, c) in cccs.iter().enumerate() {
      is_base_case_flags.push(c.is_null(cs.namespace(|| format!("{}th cccs", i)), &zero)?);
    }
    let is_base_case = Boolean::from(multi_and(
      cs.namespace(|| "is base case"),
      &is_base_case_flags,
    )?);

    let is_correct_primary_public_input = self.check_public_input(
      cs.namespace(|| "is correct primary public_input"),
      &primary_params,
      &z_0,
      &z_i,
      &cccs,
      &lcccs,
      &relaxed_r1cs_inst,
    )?;
    Boolean::enforce_equal(
      cs.namespace(|| "is correct secondary public_input or is base case"),
      &is_correct_primary_public_input,
      &is_base_case.not(),
    )?;

    // Synthesize the circuit for the base case and get the new running instance
    let lcccs_base =
      self.synthesize_genesis_based_nimfs(cs.namespace(|| "generate base case based nimfs"))?;
    let relaxed_r1cs_inst_base =
      self.synthesize_genesis_based_nifs(cs.namespace(|| "generate base case based nifs"))?;

    // Synthesize the circuit for the non-base case and get the new running
    // instance along with a boolean indicating if all checks have passed
    let (new_lcccs_primary_part, check_non_base_pass, rho) = self.synthesize_based_nimfs(
      cs.namespace(|| "generate non base case based nimfs"),
      self.params,
      &lcccs
        .iter()
        .map(|l| l.primary_part.clone())
        .collect::<Vec<_>>(),
      &cccs
        .iter()
        .map(|l| l.primary_part.clone())
        .collect::<Vec<_>>(),
      &nimfs_proof,
    )?;
    // Either check_non_base_pass=true or we are in the base case
    Boolean::enforce_equal(
      cs.namespace(|| "check_non_base_pass nor base_case"),
      &Boolean::from(check_non_base_pass).not(),
      &is_base_case,
    )?;

    let new_lcccs = AllocatedLCCCS::new(new_lcccs_primary_part, new_lcccs_second_part);
    self.update_secondary_public_input(
      cs.namespace(|| "is correct secondary public_input"),
      rho,
      &cccs,
      &lcccs,
      &new_lcccs,
      &mut r1cs_inst,
    )?;

    let new_lcccs = lcccs_base.conditionally_select(
      cs.namespace(|| "compute lcccs_new"),
      &new_lcccs,
      &is_base_case.clone(),
    )?;
    let calc_relaxed_r1cs_inst = self.synthesize_based_nifs(
      cs.namespace(|| "generate non base case based nifs"),
      &secondary_params,
      relaxed_r1cs_inst,
      &r1cs_inst,
      T,
    )?;
    let new_relaxed_r1cs_inst = relaxed_r1cs_inst_base.conditionally_select(
      cs.namespace(|| "compute U_new"),
      &calc_relaxed_r1cs_inst,
      &is_base_case.clone(),
    )?;

    // select correct z
    let z_input = z_i
      .into_iter()
      .enumerate()
      .map(|(i, z)| {
        conditionally_select_vec_allocated_num(
          cs.namespace(|| format!("select {i}th input to F")),
          &z_0,
          &z,
          &is_base_case.clone(),
        )
      })
      .collect::<Result<Vec<Vec<_>>, SynthesisError>>()?;

    let new_z = self.step_circuit.synthesize(
      &mut cs.namespace(|| "F"),
      &z_input.iter().map(|z| &z[..]).collect::<Vec<_>>(),
    )?;
    if new_z.len() != ARITY {
      return Err(SynthesisError::IncompatibleLengthVector(
        "z_next".to_string(),
      ));
    }

    let hash = self.commit_explicit_public_input(
      cs.namespace(|| "commit public input"),
      &primary_params,
      &z_0,
      &new_z,
      &new_lcccs,
      &new_relaxed_r1cs_inst,
    )?;
    hash.inputize(cs.namespace(|| "output new hash of this circuit"))?; // this circuit's unique public input

    Ok(new_z)
  }

  /// Synthesizes non-base case and returns the new `LCCCS`
  /// And a boolean indicating if all checks pass
  #[allow(clippy::too_many_arguments)]
  fn synthesize_based_nimfs<CS: ConstraintSystem<<G1 as Group>::Base>>(
    &self,
    mut cs: CS,
    params: &PCDUnitParams<G2, ARITY, R>,
    lcccs: &[AllocatedLCCCSPrimaryPart<G1>],
    cccs: &[AllocatedCCCSPrimaryPart<G1>],
    proof: &AllocatedProof<G1>,
  ) -> Result<
    (
      AllocatedLCCCSPrimaryPart<G1>,
      AllocatedBit,
      AllocatedNum<G1::Base>,
    ),
    SynthesisError,
  > {
    assert!(!lcccs.is_empty());
    assert!(!cccs.is_empty());

    let mut transcript = G1::FoldTECircuit::new(
      self.te_consts.clone(),
      cs.namespace(|| "init NIMFS transcript"),
      b"multifolding",
    );
    transcript.squeeze(cs.namespace(|| "squeeze init"), b"init")?;

    // Step 1: Get some challenges
    let gamma = transcript.squeeze(cs.namespace(|| "alloc gamma"), b"gamma")?;
    let beta = transcript.batch_squeeze(cs.namespace(|| "alloc beta"), b"beta", params.ccs.s)?;

    // Step 3: Start verifying the sumcheck
    // First, compute the expected sumcheck sum: \sum gamma^j v_j
    let mut sum_v_j_gamma_lc = Num::zero();
    for (i, running_instance) in lcccs.iter().enumerate() {
      for j in 0..running_instance.Vs.len() {
        let mut cs = cs.namespace(|| format!("{i}th lcccs's sum_v_{j}"));
        let gamma_j = gamma.pow_constant(cs.namespace(|| "alloc gamma_j"), i * params.ccs.t + j)?;
        let res = running_instance.Vs[j].mul(cs.namespace(|| "v * gamma_j"), &gamma_j)?;
        sum_v_j_gamma_lc = sum_v_j_gamma_lc.add(&res.into());
      }
    }
    let sum_v_j_gamma = AllocatedNum::alloc(cs.namespace(|| "alloc tmp"), || {
      sum_v_j_gamma_lc.get_value().get().copied()
    })?;
    cs.enforce(
      || "constraints final lc",
      |_lc| sum_v_j_gamma_lc.lc(G1::Base::ONE),
      |lc| lc + CS::one(),
      |lc| lc + sum_v_j_gamma.get_variable(),
    );

    let vp_aux_info = VPAuxInfo::<G1::Base> {
      max_degree: params.ccs.d + 1,
      num_variables: params.ccs.s,
      phantom: std::marker::PhantomData::<G1::Base>,
    };
    let (sumcheck_subclaim, check_sumcheck_v) = sumcheck_verify(
      cs.namespace(|| "verify sumcheck proof"),
      &sum_v_j_gamma,
      &proof.sum_check_proof,
      &vp_aux_info,
      &mut transcript,
    )?;

    // Step 2: Dig into the sumcheck claim and extract the randomness used
    let r_x_prime = sumcheck_subclaim.point.clone();

    // Step 5: Finish verifying sumcheck (verify the claim c)
    let c = enforce_compute_c_from_sigmas_and_thetas::<_, G1, G2>(
      cs.namespace(|| "calc c"),
      &params.ccs,
      &proof.sigmas,
      &proof.thetas,
      gamma,
      &beta,
      lcccs.iter().map(|lcccs| lcccs.r_x.clone()).collect(),
      &r_x_prime,
    )?;
    let check_pass = alloc_num_equals(
        cs.namespace(|| "check that the g(r_x') from the sumcheck proof is equal to the computed c from sigmas&thetas"),
        &c,
        &sumcheck_subclaim.expected_evaluation
    )?;

    // Step 6: Get the folding challenge
    let rho = transcript.squeeze(cs.namespace(|| "alloc rho"), b"rho")?;

    // Run NIMFS Verifier part 1
    let mut new_lcccs = multi_folding_with_primary_part(
      cs.namespace(|| "compute fold of U and u"),
      lcccs,
      cccs,
      &rho,
      &proof.sigmas,
      &proof.thetas,
    )?;
    new_lcccs.r_x = r_x_prime;

    let check_pass = AllocatedBit::and(
      cs.namespace(|| "check pass 1 and 2 and 3 and check_sumcheck_v"),
      &check_pass,
      &check_sumcheck_v,
    )?;

    Ok((new_lcccs, check_pass, rho))
  }

  /// Synthesizes non-base case and returns the new relaxed `R1CSInstance`
  /// And a boolean indicating if all checks pass
  #[allow(clippy::too_many_arguments)]
  fn synthesize_based_nifs<CS: ConstraintSystem<<G1 as Group>::Base>>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<G1::Base>,
    mut U: Vec<AllocatedRelaxedR1CSInstance<G1>>,
    u: &AllocatedR1CSInstanceBasedSimulatedX<G1>,
    mut T: Vec<AllocatedPoint<G1>>,
  ) -> Result<AllocatedRelaxedR1CSInstance<G1>, SynthesisError> {
    assert!(!U.is_empty());
    // Compute r
    let mut ro = G1::ROCircuit::new(self.ro_consts.clone(), 0);
    ro.absorb(params);
    for (i, U) in U.iter().enumerate() {
      U.absorb_in_ro(
        cs.namespace(|| format!("absorb {i}th running instance")),
        &mut ro,
      )?;
    }
    u.absorb_simulated_x_in_ro(cs.namespace(|| "absorb r1cs instance in_ro"), &mut ro)?;

    let last_T = T.pop().unwrap();
    let mut U_folded_U = U.remove(0);

    // Run NIFS Verifier
    for (i, (U, T)) in U.into_iter().zip_eq(T).enumerate() {
      T.absorb_in_ro(&mut ro);

      let mut cs = cs.namespace(|| format!("{i}th folded U"));
      let r_bits = ro.squeeze(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
      U_folded_U = U_folded_U.fold_with_relaxed_r1cs(
        cs.namespace(|| "compute fold of U and U"),
        &U,
        &T,
        r_bits,
        self.params.limb_width,
        self.params.n_limbs,
      )?;
    }
    last_T.absorb_in_ro(&mut ro);
    let r_bits = ro.squeeze(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
    let U_folded = U_folded_U.fold_with_r1cs(
      cs.namespace(|| "compute fold of U and u"),
      Either::Right(u),
      &last_T,
      r_bits,
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    Ok(U_folded)
  }

  /// check the correctness of the all cccs's X(public input)
  #[allow(clippy::too_many_arguments)]
  pub fn check_public_input<CS: ConstraintSystem<<G1 as Group>::Base>>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<G1::Base>,
    z_0: &[AllocatedNum<G1::Base>],
    new_z: &[Vec<AllocatedNum<G1::Base>>],
    cccs: &[AllocatedCCCS<G1>],
    lcccs: &[AllocatedLCCCS<G1>],
    relaxed_r1cs_inst: &[AllocatedRelaxedR1CSInstance<G1>],
  ) -> Result<Boolean, SynthesisError> {
    let mut is_correct = Vec::new();
    for (i, c) in cccs.iter().enumerate() {
      let mut cs = cs.namespace(|| format!("check {i}th cccs"));
      let public_hash = self.commit_explicit_public_input(
        cs.namespace(|| "commit public input"),
        params,
        z_0,
        &new_z[i],
        &lcccs[i],
        &relaxed_r1cs_inst[i],
      )?;
      assert_eq!(c.primary_part.Xs.len(), 1);
      let is_eq = alloc_num_equals(
        cs.namespace(|| "check public_hash"),
        &public_hash,
        &c.primary_part.Xs[0],
      )?;
      is_correct.push(is_eq.into())
    }
    multi_and(cs.namespace(|| "is correct public inputs"), &is_correct).map(Into::into)
  }

  /// update the secondary r1cs instance's X(public input)
  #[allow(clippy::too_many_arguments)]
  pub fn update_secondary_public_input<CS: ConstraintSystem<<G1 as Group>::Base>>(
    &self,
    mut cs: CS,
    rho: AllocatedNum<G1::Base>,
    cccs: &[AllocatedCCCS<G1>],
    lcccs: &[AllocatedLCCCS<G1>],
    new_lcccs: &AllocatedLCCCS<G1>,
    r1cs_inst: &mut AllocatedR1CSInstanceBasedSimulatedX<G1>,
  ) -> Result<(), SynthesisError> {
    let mut public_inputs = Vec::new();
    let mut ecc_parity_container = Vec::new();
    public_inputs.push(BigNat::from_num(
      cs.namespace(|| "convert rho from num to big_nat"),
      &rho.into(),
      self.params.limb_width,
      self.params.n_limbs,
    )?);
    for (i, c) in lcccs.iter().enumerate() {
      public_inputs.push(c.C.x.clone());
      ecc_parity_container.push(
        c.C
          .get_y_parity(cs.namespace(|| format!("{i}th lcccs.C parity")))?,
      );
    }
    for (i, c) in cccs.iter().enumerate() {
      public_inputs.push(c.C.x.clone());
      ecc_parity_container.push(
        c.C
          .get_y_parity(cs.namespace(|| format!("{i}th cccs.C parity")))?,
      );
    }
    public_inputs.push(new_lcccs.C.x.clone());
    ecc_parity_container.push(
      new_lcccs
        .C
        .get_y_parity(cs.namespace(|| "new lcccs.C parity"))?,
    );

    let ecc_compression_num = from_le_bits_to_num(
      cs.namespace(|| "alloc ecc_compression_num"),
      &ecc_parity_container,
    )?;
    public_inputs.push(BigNat::from_num(
      cs.namespace(|| "convert ecc_compression_num from num to big_nat"),
      &ecc_compression_num.into(),
      self.params.limb_width,
      self.params.n_limbs,
    )?);

    // only sanity check, replace circuit equality constraints with assignment
    // assert!(r1cs_inst
    //   .X
    //   .iter()
    //   .zip_eq(public_inputs.iter())
    //   .all(|(external, internal)| external.value == internal.value));
    r1cs_inst.X = public_inputs;
    Ok(())
  }

  /// Compute the new hash H(params, z0, z, lcccs, relaxed R1CS instance)
  pub fn commit_explicit_public_input<CS: ConstraintSystem<<G1 as Group>::Base>>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<G1::Base>,
    z_0: &[AllocatedNum<G1::Base>],
    new_z: &[AllocatedNum<G1::Base>],
    lcccs: &AllocatedLCCCS<G1>,
    relaxed_r1cs_inst: &AllocatedRelaxedR1CSInstance<G1>,
  ) -> Result<AllocatedNum<G1::Base>, SynthesisError> {
    let mut ro = G1::ROCircuit::new(self.ro_consts.clone(), 0);

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
