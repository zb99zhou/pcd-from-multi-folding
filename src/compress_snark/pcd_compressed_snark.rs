use std::marker::PhantomData;
use std::mem::size_of_val;

use crate::bellpepper::r1cs::NovaShape;
use crate::bellpepper::shape_cs::ShapeCS;
use serde::{Deserialize, Serialize};

use crate::compress_snark::math::Math;
use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use crate::errors::NovaError;
use crate::gadgets::utils::scalar_as_base;
use crate::nifs::r1cs::{RelaxedR1CSInstance, RelaxedR1CSWitness};
use crate::nimfs::ccs::cccs::{CCSWitness, CCCS};
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::multifolding::{MultiFolding, Proof, NIMFS};
use crate::pcd_aux_circuit::{
  NovaAuxiliaryInputs, NovaAuxiliaryParams, NovaAuxiliarySecondCircuit,
};
use crate::pcd_circuit::{PCDUnitParams, PCDUnitPrimaryCircuit};
use crate::traits::circuit::PCDStepCircuit;
use crate::traits::snark::{LinearCommittedCCSTrait, RelaxedR1CSSNARKTrait};
use crate::traits::{
  AbsorbInROTrait, Group, ROConstants, ROConstantsCircuit, ROTrait, TEConstantsCircuit,
  TranscriptEngineTrait,
};
use crate::CommitmentKey;

pub struct PCDPublicParams<G1, G2, SC, const ARITY: usize, const R: usize>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  SC: PCDStepCircuit<G1::Scalar, ARITY, R>,
{
  pub(crate) ro_consts_primary: ROConstants<G2>,
  pub(crate) ro_consts_circuit_primary: ROConstantsCircuit<G2>,
  pub(crate) te_consts_circuit_primary: TEConstantsCircuit<G2>,
  pub(crate) ck_primary: CommitmentKey<G1>,
  pub(crate) ck_secondary: CommitmentKey<G2>,
  pub(crate) primary_circuit_params: PCDUnitParams<G1, ARITY, R>,
  pub(crate) secondary_circuit_params: NovaAuxiliaryParams<G2>,
  pub(crate) _p_c: PhantomData<SC>,
}

impl<G1, G2, SC, const ARITY: usize, const R: usize> PCDPublicParams<G1, G2, SC, ARITY, R>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  SC: PCDStepCircuit<G1::Scalar, ARITY, R>,
{
  pub fn setup(circuit: &SC) -> Self {
    let ro_consts_primary: ROConstants<G2> = Default::default();
    let ro_consts_circuit_primary: ROConstantsCircuit<G2> = Default::default();
    let te_consts_circuit_primary: TEConstantsCircuit<G2> = Default::default();

    let aux_circuit_setup_input = NovaAuxiliaryInputs::<G1>::new(None, None, None, None, R);
    let aux_circuit_setup =
      NovaAuxiliarySecondCircuit::<G1>::new(aux_circuit_setup_input, BN_LIMB_WIDTH, BN_N_LIMBS);
    let mut cs_aux_helper: ShapeCS<G2> = ShapeCS::new();
    let _ = aux_circuit_setup.synthesize(&mut cs_aux_helper);
    let (aux_r1cs_shape, ck_secondary) = cs_aux_helper.r1cs_shape();

    let secondary_circuit_params = NovaAuxiliaryParams::new(aux_r1cs_shape, R * 2 + 3);

    // find eligible s and s_prime for satisfy PCD primary circuit
    let (mut s, mut s_prime) = (16, 16);
    let cs_pcd_helper = loop {
      let primary_circuit_params =
        PCDUnitParams::<G1, ARITY, R>::default_for_pcd(BN_LIMB_WIDTH, BN_N_LIMBS, s, s_prime);
      let pcd_circuit_setup = PCDUnitPrimaryCircuit::<'_, G2, G1, SC, ARITY, R>::new(
        &primary_circuit_params,
        &secondary_circuit_params,
        None,
        circuit,
        ro_consts_circuit_primary.clone(),
        te_consts_circuit_primary.clone(),
      );
      let mut cs_pcd_helper: ShapeCS<G1> = ShapeCS::new();
      let _ = pcd_circuit_setup
        .synthesize(&mut cs_pcd_helper)
        .expect("Failed to setup PCD circuit");
      if 2usize.pow(s as u32) >= cs_pcd_helper.num_constraints()
        && 2usize.pow(s_prime as u32) >= cs_pcd_helper.num_vars()
      {
        break cs_pcd_helper;
      }
      if 2usize.pow(s as u32) < cs_pcd_helper.num_constraints() {
        s = cs_pcd_helper.num_constraints().log_2();
      }
      if 2usize.pow(s_prime as u32) < cs_pcd_helper.num_vars() {
        s_prime = cs_pcd_helper.num_vars().log_2();
      }
    };

    let (r1cs_shape_primary, ck_primary) = cs_pcd_helper.r1cs_shape();
    let ccs_primary = CCS::<G1>::from(r1cs_shape_primary);
    let primary_circuit_params =
      PCDUnitParams::<G1, ARITY, R>::new(BN_LIMB_WIDTH, BN_N_LIMBS, ccs_primary);

    Self {
      ro_consts_primary,
      ro_consts_circuit_primary,
      te_consts_circuit_primary,
      ck_primary,
      ck_secondary,
      primary_circuit_params,
      secondary_circuit_params,
      _p_c: PhantomData,
    }
  }
}

pub struct PCDRecursiveSNARK<G1, G2, SC, const ARITY: usize, const R: usize>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  SC: PCDStepCircuit<G1::Scalar, ARITY, R>,
{
  r_w_primary: CCSWitness<G1>,
  r_u_primary: CCCS<G1>,
  r_W_primary: CCSWitness<G1>,
  r_U_primary: LCCCS<G1>,
  r_W_secondary: RelaxedR1CSWitness<G2>,
  r_U_secondary: RelaxedR1CSInstance<G2>,
  zi_primary: Vec<G1::Scalar>,
  _p_c: PhantomData<SC>,
}

impl<G1, G2, SC, const ARITY: usize, const R: usize> PCDRecursiveSNARK<G1, G2, SC, ARITY, R>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  SC: PCDStepCircuit<G1::Scalar, ARITY, R>,
{
  pub fn new(
    r_w_primary: CCSWitness<G1>,
    r_u_primary: CCCS<G1>,
    r_W_primary: CCSWitness<G1>,
    r_U_primary: LCCCS<G1>,
    r_W_secondary: RelaxedR1CSWitness<G2>,
    r_U_secondary: RelaxedR1CSInstance<G2>,
    zi_primary: Vec<G1::Scalar>,
  ) -> Self {
    Self {
      r_w_primary,
      r_u_primary,
      r_W_primary,
      r_U_primary,
      r_W_secondary,
      r_U_secondary,
      zi_primary,
      _p_c: PhantomData::<SC>,
    }
  }

  pub fn size_of_this(
    &self
  ) -> usize {
    let self_size =
        (
          self.r_u_primary.x.len() * size_of_val(&self.r_u_primary.x[0])
              + size_of_val(&self.r_u_primary.C)
        )
            + (
          size_of_val(&self.r_U_primary.C)
              + size_of_val(&self.r_U_primary.u)
              + self.r_U_primary.x.len()
              * size_of_val(&self.r_U_primary.x[0])
              + self.r_U_primary.r_x.len()
              * size_of_val(&self.r_U_primary.r_x[0])
              + self.r_U_primary.v.len()
              * size_of_val(&self.r_U_primary.v[0])
        )
            + (
          size_of_val(&self.r_W_primary.r_w)
              + self.r_W_primary.w.len()
              * size_of_val(&self.r_W_primary.w[0])
        )
            + (
          size_of_val(&self.r_w_primary.r_w)
              + self.r_w_primary.w.len()
              * size_of_val(&self.r_w_primary.w[0])
        )
            + (
          self.r_U_secondary.X.len()
              * size_of_val(&self.r_U_secondary.X[0])
              + size_of_val(&self.r_U_secondary.u)
              + size_of_val(&self.r_U_secondary.comm_E)
              + size_of_val(&self.r_U_secondary.comm_W)
        )
            + (
          self.r_W_secondary.W.len()
              * size_of_val(&self.r_W_secondary.W[0])
              + self.r_W_secondary.E.len()
              * size_of_val(&self.r_W_secondary.E[0])
        );

    self_size
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PCDProverKey<G1, G2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  S1: LinearCommittedCCSTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  pk_primary: S1::ProverKey,
  pk_secondary: S2::ProverKey,
}

/// A type that holds the verifier key for `PCDRecursiveSNARK`
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PCDVerifierKey<G1, G2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  S1: LinearCommittedCCSTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  ro_consts: ROConstants<G2>,
  digest: G1::Scalar,
  vk_primary: S1::VerifierKey,
  vk_secondary: S2::VerifierKey,
  secondary_io_num: usize,
}

/// A SNARK that proves the knowledge of a valid `RecursiveSNARK`
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PCDCompressedSNARK<G1, G2, SC, S1, S2, const ARITY: usize, const R: usize>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  SC: PCDStepCircuit<G1::Scalar, ARITY, R>,
  S1: LinearCommittedCCSTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  r_u_primary: CCCS<G1>,
  r_U_primary: LCCCS<G1>,
  nimfs_proof: Proof<G1>,
  f_W_snark_primary: S1,

  r_U_secondary: RelaxedR1CSInstance<G2>,
  r_W_snark_secondary: S2,

  zn_primary: Vec<G1::Scalar>,

  _p_c: PhantomData<SC>,
}

impl<G1, G2, SC, S1, S2, const ARITY: usize, const R: usize>
  PCDCompressedSNARK<G1, G2, SC, S1, S2, ARITY, R>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  SC: PCDStepCircuit<G1::Scalar, ARITY, R>,
  S1: LinearCommittedCCSTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  const TRANSCRIPT_INIT_STR: &'static [u8; 4] = b"init";

  /// Creates prover and verifier keys for `CompressedSNARK`
  pub fn setup(
    pp: &PCDPublicParams<G1, G2, SC, ARITY, R>,
  ) -> Result<(PCDProverKey<G1, G2, S1, S2>, PCDVerifierKey<G1, G2, S1, S2>), NovaError> {
    let (pk_primary, vk_primary) = S1::setup(&pp.ck_primary, &pp.primary_circuit_params.ccs)?;
    let (pk_secondary, vk_secondary) =
      S2::setup(&pp.ck_secondary, &pp.secondary_circuit_params.r1cs_shape)?;

    let pk = PCDProverKey {
      pk_primary,
      pk_secondary,
    };

    let vk = PCDVerifierKey {
      ro_consts: pp.ro_consts_primary.clone(),
      digest: pp.primary_circuit_params.digest,
      vk_primary,
      vk_secondary,
      secondary_io_num: pp.secondary_circuit_params.io_num,
    };

    Ok((pk, vk))
  }

  /// Create a new `CompressedSNARK`
  pub fn prove<const ENABLE_SANITY_CHECK: bool>(
    pp: &PCDPublicParams<G1, G2, SC, ARITY, R>,
    pk: &PCDProverKey<G1, G2, S1, S2>,
    recursive_snark: &PCDRecursiveSNARK<G1, G2, SC, ARITY, R>,
  ) -> Result<Self, NovaError> {
    // Prover's transcript
    let mut transcript_p = G1::FoldTE::new(Default::default(), b"multifolding");
    transcript_p.squeeze(Self::TRANSCRIPT_INIT_STR).unwrap();

    // fold the primary circuit's instance
    let res_primary = MultiFolding::prove::<ENABLE_SANITY_CHECK>(
      &mut transcript_p,
      &[recursive_snark.r_U_primary.clone()],
      &[recursive_snark.r_u_primary.clone()],
      &[recursive_snark.r_W_primary.clone()],
      &[recursive_snark.r_w_primary.clone()],
    );
    let (nimfs_proof, f_U_primary, f_W_primary) = res_primary;
    let (f_W_snark_primary, r_W_snark_secondary) = (
      S1::prove(&pp.ck_primary, &pk.pk_primary, &f_U_primary, &f_W_primary).unwrap(),
      S2::prove(
        &pp.ck_secondary,
        &pk.pk_secondary,
        &recursive_snark.r_U_secondary,
        &recursive_snark.r_W_secondary,
      )
      .unwrap(),
    );

    Ok(Self {
      r_u_primary: recursive_snark.r_u_primary.clone(),
      r_U_primary: recursive_snark.r_U_primary.clone(),
      nimfs_proof,
      f_W_snark_primary,

      r_U_secondary: recursive_snark.r_U_secondary.clone(),
      r_W_snark_secondary,

      zn_primary: recursive_snark.zi_primary.clone(),

      _p_c: Default::default(),
    })
  }

  /// Verify the correctness of the `CompressedSNARK`
  pub fn verify(
    &self,
    vk: &PCDVerifierKey<G1, G2, S1, S2>,
    z0_primary: Vec<G1::Scalar>,
  ) -> Result<Vec<G1::Scalar>, NovaError> {
    // check if the instances have two public outputs
    if self.r_u_primary.x.len() != ARITY
      || self.r_U_primary.x.len() != ARITY
      || self.r_U_secondary.X.len() != vk.secondary_io_num
    {
      return Err(NovaError::InvalidInputLength);
    }

    // check if the output hashes in R1CS instances point to the right running instances
    let hash_primary = {
      let mut hasher =
        <G2 as Group>::RO::new(vk.ro_consts.clone(), NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * ARITY);
      hasher.absorb(vk.digest);
      for e in z0_primary {
        hasher.absorb(e);
      }
      for e in &self.zn_primary {
        hasher.absorb(*e);
      }
      self.r_U_primary.absorb_in_ro::<G2>(&mut hasher);
      self.r_U_secondary.absorb_in_ro(&mut hasher);

      hasher.squeeze(NUM_HASH_BITS)
    };

    if scalar_as_base::<G2>(hash_primary) != self.r_u_primary.x[0] {
      return Err(NovaError::InvalidInput);
    }

    // Verifier's transcript
    let mut transcript_v = G1::FoldTE::new(Default::default(), b"multifolding");
    transcript_v.squeeze(Self::TRANSCRIPT_INIT_STR).unwrap();

    // fold the running instance and last instance to get a folded instance
    let f_U_primary = NIMFS::verify(
      &mut transcript_v,
      &[self.r_U_primary.clone()],
      &[self.r_u_primary.clone()],
      self.nimfs_proof.clone(),
    );

    // check the satisfiability of the folded instances using SNARKs proving the knowledge of their satisfying witnesses
    let (res_primary, res_secondary) = rayon::join(
      || self.f_W_snark_primary.verify(&vk.vk_primary, &f_U_primary),
      || {
        self
          .r_W_snark_secondary
          .verify(&vk.vk_secondary, &self.r_U_secondary)
      },
    );

    res_primary?;
    res_secondary?;

    Ok(self.zn_primary.clone())
  }

  pub fn size_of_this(
    &self
  ) -> usize {
    let self_size =
        (
          self.r_u_primary.x.len() * size_of_val(&self.r_u_primary.x[0])
              + size_of_val(&self.r_u_primary.C)
        )
            + (
          size_of_val(&self.r_U_primary.C)
              + size_of_val(&self.r_U_primary.u)
              + self.r_U_primary.x.len()
              * size_of_val(&self.r_U_primary.x[0])
              + self.r_U_primary.r_x.len()
              * size_of_val(&self.r_U_primary.r_x[0])
              + self.r_U_primary.v.len()
              * size_of_val(&self.r_U_primary.v[0])
        )
            + (
          self.nimfs_proof.sigmas.len() *
              self.nimfs_proof.sigmas[0].len() *
              size_of_val(&self.nimfs_proof.sigmas[0][0])
          + self.nimfs_proof.thetas.len() *
              self.nimfs_proof.thetas[0].len() *
              size_of_val(&self.nimfs_proof.thetas[0][0])
          + self.nimfs_proof.sum_check_proof.point.len() *
              size_of_val(&self.nimfs_proof.sum_check_proof.point[0])
          + self.nimfs_proof.sum_check_proof.proofs.len() *
              (
                  self.nimfs_proof.sum_check_proof.proofs[0].evaluations.len() *
                      size_of_val(&self.nimfs_proof.sum_check_proof.proofs[0].evaluations[0])
                  )
        )
            + (
          self.f_W_snark_primary.size_of_this()
        )
            + (
          self.r_U_secondary.X.len()
              * size_of_val(&self.r_U_secondary.X[0])
              + size_of_val(&self.r_U_secondary.u)
              + size_of_val(&self.r_U_secondary.comm_E)
              + size_of_val(&self.r_U_secondary.comm_W)
        )
            + (
          self.r_W_snark_secondary.size_of_this()
        );

    self_size
  }
}

#[cfg(test)]
mod test {
  use std::time::Instant;

  use crate::compress_snark::lcccs_snark::LCCCSSNARK;
  use crate::compress_snark::r1cs_snark::RelaxedR1CSSNARK;
  use crate::compress_snark::{PCDCompressedSNARK, PCDPublicParams, PCDRecursiveSNARK};

  use crate::nifs::r1cs::{RelaxedR1CSInstance, RelaxedR1CSWitness};
  use crate::pcd_node::PCDNode;
  use crate::provider::ipa_pc::EvaluationEngine;
  use crate::provider::pedersen::CommitmentKeyExtTrait;
  // use crate::traits::circuit::TrivialTestCircuit;
  use crate::multi_hash_circuit::MultiHashCircuit;
  use crate::traits::commitment::CommitmentEngineTrait;
  use crate::traits::evaluation::EvaluationEngineTrait;
  use crate::traits::Group;
  use ff::Field;
  use rand_core::OsRng;
  // use std::time::Instant;

  fn test_pcd_with_compressed_verify_with<G1, G2, const R: usize, const IO_NUM: usize, EE1, EE2>()
  where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
    <G1::CE as CommitmentEngineTrait<G1>>::CommitmentKey: CommitmentKeyExtTrait<G1>,
    <G2::CE as CommitmentEngineTrait<G2>>::CommitmentKey: CommitmentKeyExtTrait<G2>,
    EE1: EvaluationEngineTrait<G1>,
    EE2: EvaluationEngineTrait<G2>,
  {
    let z0 = vec![G1::Scalar::ZERO; IO_NUM];
    // let test_circuit = TrivialTestCircuit::<<G2 as Group>::Base>::default();
    let test_circuit = MultiHashCircuit::<<G2 as Group>::Base, IO_NUM, R>::new();
    let pp = PCDPublicParams::<G1, G2, _, IO_NUM, R>::setup(&test_circuit);

    let rng = OsRng;
    let z = vec![G1::Scalar::ZERO; pp.primary_circuit_params.ccs.n];
    let (default_cccs, default_w_cccs) =
      pp.primary_circuit_params
        .ccs
        .to_cccs(rng, &pp.ck_primary, &z);
    let (default_lcccs, default_w_lcccs) =
      pp.primary_circuit_params
        .ccs
        .to_lcccs(rng, &pp.ck_primary, &z);
    let default_relaxed_r1cs_instance =
      RelaxedR1CSInstance::<G2>::default_for_pcd(pp.secondary_circuit_params.r1cs_shape.num_io);
    let default_relaxed_r1cs_witness =
      RelaxedR1CSWitness::<G2>::default(&pp.secondary_circuit_params.r1cs_shape);

    // define input for an initial node
    let node_input_lcccs = vec![default_lcccs; R];
    let node_input_cccs = vec![default_cccs; R];
    let node_input_relaxed_r1cs_instance = vec![default_relaxed_r1cs_instance; R];
    let node_input_lcccs_witness = vec![default_w_lcccs; R];
    let node_input_cccs_witness = vec![default_w_cccs; R];
    let node_input_relaxed_r1cs_witness = vec![default_relaxed_r1cs_witness; R];

    // define an initial node
    let node_initial = PCDNode::<G1, G2, IO_NUM, R>::new(
      node_input_lcccs,
      node_input_cccs,
      z0.clone(),
      None,
      Some(node_input_relaxed_r1cs_instance),
      Some(node_input_lcccs_witness),
      Some(node_input_cccs_witness),
      Some(node_input_relaxed_r1cs_witness),
    );

    println!("=================================================Proving initial node=================================================");
    let (
      node_lcccs,
      node_cccs,
      node_relaxed_r1cs_instance,
      node_lcccs_witness,
      node_cccs_witness,
      node_relaxed_r1cs_witness,
      node_zi,
    ) = node_initial
      .prove_step::<_, true, false>(&pp, &test_circuit)
      .unwrap();

    // define input for an intermediate node
    let node_input_lcccs = vec![node_lcccs; R];
    let node_input_cccs = vec![node_cccs; R];
    let node_input_zi = vec![node_zi; R];
    let node_input_relaxed_r1cs_instance = vec![node_relaxed_r1cs_instance; R];
    let node_input_lcccs_witness = vec![node_lcccs_witness; R];
    let node_input_cccs_witness = vec![node_cccs_witness; R];
    let node_input_relaxed_r1cs_witness = vec![node_relaxed_r1cs_witness; R];

    // define an intermediate node
    let node_intermed = PCDNode::<G1, G2, IO_NUM, R>::new(
      node_input_lcccs,
      node_input_cccs,
      z0.clone(),
      Some(node_input_zi),
      Some(node_input_relaxed_r1cs_instance),
      Some(node_input_lcccs_witness),
      Some(node_input_cccs_witness),
      Some(node_input_relaxed_r1cs_witness),
    );

    println!("=================================================Proving intermediate node=================================================");
    let (
      node_lcccs,
      node_cccs,
      node_relaxed_r1cs_instance,
      node_lcccs_witness,
      node_cccs_witness,
      node_relaxed_r1cs_witness,
      node_zi,
    ) = node_intermed
      .prove_step::<_, false, true>(&pp, &test_circuit)
      .unwrap();

    let recursive_snark = PCDRecursiveSNARK::<G1, G2, _, IO_NUM, R>::new(
      node_cccs_witness,
      node_cccs,
      node_lcccs_witness,
      node_lcccs,
      node_relaxed_r1cs_witness,
      node_relaxed_r1cs_instance,
      node_zi,
    );


    println!("The size of recursive_snark: {} bytes", recursive_snark.size_of_this());

    let (compressed_pk, compressed_vk) = PCDCompressedSNARK::<
      G1,
      G2,
      _,
      LCCCSSNARK<G1, EE1>,
      RelaxedR1CSSNARK<G2, EE2>,
      IO_NUM,
      R,
    >::setup(&pp)
    .unwrap();

    println!("=================================================Proving compressedSNARK=================================================");
    let start_prv = Instant::now();
    let compress_snark = PCDCompressedSNARK::<
      G1,
      G2,
      _,
      LCCCSSNARK<G1, EE1>,
      RelaxedR1CSSNARK<G2, EE2>,
      IO_NUM,
      R,
    >::prove::<false>(&pp, &compressed_pk, &recursive_snark)
    .unwrap();
    let duration_prv = start_prv.elapsed();
    println!("Time elapsed in proving compressedSNARK:{:?}", duration_prv);

    println!("The size of compressed_snark: {} bytes", compress_snark.size_of_this());

    // add proof size

    println!("=================================================Verifying compressedSNARK=================================================");
    let start_vry = Instant::now();
    let res = compress_snark.verify(&compressed_vk, z0);
    let duration_vry = start_vry.elapsed();
    println!(
      "Time elapsed in verifying compressedSNARK:{:?}",
      duration_vry
    );
    assert!(res.is_ok());
  }

  // #[ignore]
  #[test]
  fn test_pcd_with_compressed_verify() {
    type G1 = pasta_curves::pallas::Point;
    type G2 = pasta_curves::vesta::Point;
    const R: usize = 2;
    const ARITY: usize = 1;
    test_pcd_with_compressed_verify_with::<
      G1,
      G2,
      R,
      ARITY,
      EvaluationEngine<G1>,
      EvaluationEngine<G2>,
    >();
  }
}
