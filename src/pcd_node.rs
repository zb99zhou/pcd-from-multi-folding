use crate::bellpepper::r1cs::NovaWitness;
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::compress_snark::PCDPublicParams;
use crate::constants::{NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use crate::errors::NovaError;
use crate::gadgets::utils::scalar_as_base;
use crate::nifs::r1cs::{RelaxedR1CSInstance, RelaxedR1CSWitness};
use crate::nifs::NIFS;
use crate::nimfs::ccs::cccs::{CCSWitness, CCCS};
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::multifolding::{ProofWitness, NIMFS};
use crate::pcd_aux_circuit::{NovaAuxiliaryInputs, NovaAuxiliarySecondCircuit};
use crate::pcd_circuit::{PCDUnitInputs, PCDUnitPrimaryCircuit};
use crate::traits::circuit::PCDStepCircuit;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::{AbsorbInROTrait, Group, ROTrait, TranscriptEngineTrait};
use crate::Commitment;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::{ConstraintSystem, SynthesisError};

#[derive(Clone)]
pub struct PCDNode<G1, G2, const ARITY: usize, const R: usize>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  lcccs: Vec<LCCCS<G1>>,
  cccs: Vec<CCCS<G1>>,
  z0: Vec<G1::Scalar>,
  zi: Option<Vec<Vec<G1::Scalar>>>,
  relaxed_r1cs_instance: Option<Vec<RelaxedR1CSInstance<G2>>>,
  w_lcccs: Option<Vec<CCSWitness<G1>>>,
  w_cccs: Option<Vec<CCSWitness<G1>>>,
  w_relaxed_r1cs: Option<Vec<RelaxedR1CSWitness<G2>>>,
}

impl<G1, G2, const ARITY: usize, const R: usize> PCDNode<G1, G2, ARITY, R>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  #[allow(clippy::too_many_arguments)]
  pub fn new(
    lcccs: Vec<LCCCS<G1>>,
    cccs: Vec<CCCS<G1>>,
    z0: Vec<G1::Scalar>,
    zi: Option<Vec<Vec<G1::Scalar>>>,
    relaxed_r1cs_instance: Option<Vec<RelaxedR1CSInstance<G2>>>,
    w_lcccs: Option<Vec<CCSWitness<G1>>>,
    w_cccs: Option<Vec<CCSWitness<G1>>>,
    w_relaxed_r1cs: Option<Vec<RelaxedR1CSWitness<G2>>>,
  ) -> Self {
    Self {
      lcccs,
      cccs,
      z0,
      zi,
      relaxed_r1cs_instance,
      w_lcccs,
      w_cccs,
      w_relaxed_r1cs,
    }
  }

  pub fn prove_step<
    SC: PCDStepCircuit<<G2 as Group>::Base, ARITY, R>,
    const IS_GENESIS: bool,
    const ENABLE_SANITY_CHECK: bool,
  >(
    &self,
    pp: &PCDPublicParams<G1, G2, SC, ARITY, R>,
    pcd_step_circuit: &SC,
  ) -> Result<
    (
      LCCCS<G1>,
      CCCS<G1>,
      RelaxedR1CSInstance<G2>,
      CCSWitness<G1>,
      CCSWitness<G1>,
      RelaxedR1CSWitness<G2>,
      Vec<G1::Scalar>,
    ),
    NovaError,
  > {
    // First, handling PCD auxiliary secondary circuit
    // println!("=================================================proving NIMFS=================================================");
    let mut transcript_p = <G1 as Group>::FoldTE::new(Default::default(), b"multifolding");
    transcript_p.squeeze(b"init").unwrap();
    let (nimfs_proof, lcccs, lcccs_witness) = NIMFS::prove::<ENABLE_SANITY_CHECK>(
      &mut transcript_p,
      &self.lcccs,
      &self.cccs,
      self.w_lcccs.as_ref().unwrap(),
      self.w_cccs.as_ref().unwrap(),
    );
    if !IS_GENESIS && ENABLE_SANITY_CHECK {
      let mut transcript_v = <G1 as Group>::FoldTE::new(Default::default(), b"multifolding");
      transcript_v.squeeze(b"init")?;
      let verified_lcccs = NIMFS::verify(
        &mut transcript_v,
        &self.lcccs,
        &self.cccs,
        nimfs_proof.clone(),
      );
      assert_eq!(verified_lcccs, lcccs);
    }

    let rho = scalar_as_base::<G1>(transcript_p.get_last_state());
    let aux_circuit_input = NovaAuxiliaryInputs::<G1>::new(
      Some(pp.secondary_circuit_params.digest),
      Some(self.lcccs.to_vec()),
      Some(self.cccs.to_vec()),
      Some(rho),
      R,
    );
    let aux_circuit = NovaAuxiliarySecondCircuit::<G1>::new(
      aux_circuit_input,
      pp.primary_circuit_params.limb_width,
      pp.primary_circuit_params.n_limbs,
    );

    if ENABLE_SANITY_CHECK {
      // println!("=================================================test aux circuit satisfiability=================================================");
      let mut test_cs = TestConstraintSystem::new();
      aux_circuit.clone().synthesize(&mut test_cs)?;
      assert!(test_cs.is_satisfied());
      println!(
        "number of secondary constraints: {}",
        test_cs.num_constraints()
      );
    }

    // println!("=================================================proving aux circuit=================================================");
    let mut cs_secondary = SatisfyingAssignment::<G2>::new();
    aux_circuit.synthesize(&mut cs_secondary)?;

    let (aux_r1cs_instance, aux_r1cs_witness) = cs_secondary
      .r1cs_instance_and_witness(&pp.secondary_circuit_params.r1cs_shape, &pp.ck_secondary)?;

    // Then, handling the PCD primary circuit
    // println!("=================================================proving NIFS=================================================");
    let (nifs_proof, (relaxed_r1cs_instance, relaxed_r1cs_witness)) =
      NIFS::prove_with_multi_relaxed(
        &pp.ck_secondary,
        &pp.ro_consts_primary,
        &pp.secondary_circuit_params.digest,
        &pp.secondary_circuit_params.r1cs_shape,
        self.relaxed_r1cs_instance.as_ref().unwrap(),
        self.w_relaxed_r1cs.as_ref().unwrap(),
        &aux_r1cs_instance,
        &aux_r1cs_witness,
      )?;
    if !IS_GENESIS && ENABLE_SANITY_CHECK {
      let verified_relaxed_r1cs_instance = NIFS::verify_with_multi_relaxed(
        &nifs_proof,
        &pp.ro_consts_primary,
        &pp.secondary_circuit_params.digest,
        self.relaxed_r1cs_instance.as_ref().unwrap(),
        &aux_r1cs_instance,
      )
      .unwrap();
      assert_eq!(verified_relaxed_r1cs_instance, relaxed_r1cs_instance);
    }

    let pcd_circuit_input = PCDUnitInputs::<G2>::new(
      scalar_as_base::<G1>(pp.primary_circuit_params.digest),
      pp.secondary_circuit_params.digest,
      self.z0.clone(),
      self.zi.clone(),
      Some(self.lcccs.iter().cloned().map(Into::into).collect()),
      Some(self.cccs.iter().cloned().map(Into::into).collect()),
      self.relaxed_r1cs_instance.clone(),
      Some(aux_r1cs_instance),
      Some(lcccs.C.to_coordinates()),
      Some(
        nifs_proof
          .iter()
          .map(|p| Commitment::<G2>::decompress(&p.comm_T))
          .collect::<Result<Vec<_>, NovaError>>()?,
      ),
      Some(ProofWitness::<G2>::from(nimfs_proof)),
    );

    let pcd_circuit = PCDUnitPrimaryCircuit::<'_, G2, G1, _, ARITY, R>::new(
      &pp.primary_circuit_params,
      &pp.secondary_circuit_params,
      Some(pcd_circuit_input),
      pcd_step_circuit,
      pp.ro_consts_circuit_primary.clone(),
      pp.te_consts_circuit_primary.clone(),
    );

    if ENABLE_SANITY_CHECK {
      // println!("=================================================test PCD circuit satisfiability=================================================");
      let mut test_cs = TestConstraintSystem::new();
      let _ = pcd_circuit.clone().synthesize(&mut test_cs)?;
      assert!(test_cs.is_satisfied());
      println!(
        "number of total primary constraints: {}",
        test_cs.num_constraints()
      );

      let mut test_cs = TestConstraintSystem::new();
      let z = (0..R)
        .map(|i| {
          (0..ARITY)
            .map(|j| {
              AllocatedNum::alloc(test_cs.namespace(|| format!("{i}-{j}")), || {
                Ok(G1::Scalar::from(1))
              })
            })
            .collect::<Result<Vec<_>, SynthesisError>>()
        })
        .collect::<Result<Vec<Vec<AllocatedNum<G1::Scalar>>>, SynthesisError>>()
        .unwrap();
      let _ = pcd_circuit
        .step_circuit
        .clone()
        .synthesize(&mut test_cs, &z.iter().map(|z| &z[..]).collect::<Vec<_>>())?;
      assert!(test_cs.is_satisfied());
      println!(
        "number of function constraints: {}",
        test_cs.num_constraints()
      );
    }

    // println!("=================================================proving PCD circuit=================================================");
    let mut cs_primary = SatisfyingAssignment::<G1>::new();
    let zi_primary = pcd_circuit.clone()
      .synthesize(&mut cs_primary)?
      .iter()
      .map(|v| v.get_value().unwrap())
      .collect::<Vec<_>>();

    let (cccs, cccs_witness) =
      cs_primary.cccs_and_witness(pp.primary_circuit_params.ccs.clone(), &pp.ck_primary)?;

    let (lcccs, lcccs_witness) = if IS_GENESIS {
      (
        LCCCS::default_for_pcd(pp.primary_circuit_params.ccs.clone()),
        CCSWitness::default_for_pcd(&pp.primary_circuit_params.ccs),
      )
    } else {
      (lcccs, lcccs_witness)
    };

    let (relaxed_r1cs_instance, relaxed_r1cs_witness) = if IS_GENESIS {
      (
        RelaxedR1CSInstance::<G2>::default(
          &pp.ck_secondary,
          &pp.secondary_circuit_params.r1cs_shape,
        ),
        RelaxedR1CSWitness::<G2>::default(&pp.secondary_circuit_params.r1cs_shape),
      )
    } else {
      (relaxed_r1cs_instance, relaxed_r1cs_witness)
    };

    Ok((
      lcccs,
      cccs,
      relaxed_r1cs_instance,
      lcccs_witness,
      cccs_witness,
      relaxed_r1cs_witness,
      zi_primary,
    ))
  }

  #[allow(clippy::too_many_arguments)]
  pub fn verify<SC: PCDStepCircuit<<G2 as Group>::Base, ARITY, R>>(
    &self,
    pp: &PCDPublicParams<G1, G2, SC, ARITY, R>,
    zi_primary: &[G1::Scalar],
    lcccs: &LCCCS<G1>,
    w_lcccs: &CCSWitness<G1>,
    cccs: &CCCS<G1>,
    w_cccs: &CCSWitness<G1>,
    U: &RelaxedR1CSInstance<G2>,
    W: &RelaxedR1CSWitness<G2>,
  ) -> Result<Vec<G1::Scalar>, NovaError> {
    println!("================================PCD verify===================================");
    if U.X.len() != pp.secondary_circuit_params.io_num
      || lcccs.x.len() != ARITY
      || cccs.x.len() != ARITY
    {
      return Err(NovaError::InvalidInputLength);
    }

    let mut hasher = <G2 as Group>::RO::new(
      pp.ro_consts_primary.clone(),
      NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * ARITY,
    );
    hasher.absorb(pp.primary_circuit_params.digest);
    for x in &self.z0 {
      hasher.absorb(*x);
    }
    for e in zi_primary {
      hasher.absorb(*e);
    }
    lcccs.absorb_in_ro::<G2>(&mut hasher);
    U.absorb_in_ro(&mut hasher);

    if hasher.squeeze(NUM_HASH_BITS) != scalar_as_base::<G1>(cccs.x[0]) {
      return Err(NovaError::InvalidInput);
    }

    let (res_U, (res_lcccs, res_cccs)) = rayon::join(
      || {
        pp.secondary_circuit_params
          .r1cs_shape
          .is_sat_relaxed(&pp.ck_secondary, U, W)
      },
      || {
        rayon::join(
          || lcccs.check_relation(&pp.ck_primary, w_lcccs),
          || cccs.check_relation(&pp.ck_primary, w_cccs),
        )
      },
    );
    res_U.map_err(|_| NovaError::ProofVerifyError).unwrap();
    res_lcccs.map_err(|_| NovaError::ProofVerifyError).unwrap();
    res_cccs.map_err(|_| NovaError::ProofVerifyError).unwrap();
    Ok(zi_primary.to_vec())
  }
}

#[cfg(test)]
mod test {
  use crate::compress_snark::PCDPublicParams;
  use crate::errors::NovaError;
  use crate::nifs::r1cs::{RelaxedR1CSInstance, RelaxedR1CSWitness};
  use crate::pcd_node::PCDNode;
  // use crate::traits::circuit::TrivialTestCircuit;
  use crate::multi_hash_circuit::MultiHashCircuit;
  use crate::traits::Group;
  use ff::Field;
  use rand_core::OsRng;
  use std::time::Instant;

  fn test_pcd_with<G1, G2, const R: usize, const IO_NUM: usize>() -> Result<(), NovaError>
  where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
  {
    let z0 = vec![G1::Scalar::ZERO; IO_NUM];
    let test_circuit = MultiHashCircuit::<<G2 as Group>::Base, IO_NUM, R>::new();
    // let test_circuit = TrivialTestCircuit::<<G2 as Group>::Base>::default();
    let pp = PCDPublicParams::<G1, G2, _, IO_NUM, R>::setup(&test_circuit);

    let rng = OsRng;
    let z: Vec<<G1 as Group>::Scalar> = vec![G1::Scalar::ZERO; pp.primary_circuit_params.ccs.n];
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
    let start_initial = Instant::now();
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
      .map_err(|_| NovaError::SynthesisError)?;
    let duration_initial = start_initial.elapsed();
    println!(
      "Time elapsed in proving initial node:{:?}",
      duration_initial
    );

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
      z0,
      Some(node_input_zi),
      Some(node_input_relaxed_r1cs_instance),
      Some(node_input_lcccs_witness),
      Some(node_input_cccs_witness),
      Some(node_input_relaxed_r1cs_witness),
    );

    println!("=================================================Proving intermediate node=================================================");
    let start_intermed = Instant::now();
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
    let duration_intermed = start_intermed.elapsed();
    println!(
      "Time elapsed in proving intermediate node:{:?}",
      duration_intermed
    );

    // add proof size

    let start_vry = Instant::now();
    let res = node_intermed
      .verify(
        &pp,
        &node_zi,
        &node_lcccs,
        &node_lcccs_witness,
        &node_cccs,
        &node_cccs_witness,
        &node_relaxed_r1cs_instance,
        &node_relaxed_r1cs_witness,
      );
    let duration_vry = start_vry.elapsed();
    println!("Time elapsed in verifying:{:?}", duration_vry);
    assert!(res.is_ok());
    Ok(())
  }

  #[ignore]
  #[test]
  fn test_pcd() {
    type G1 = pasta_curves::pallas::Point;
    type G2 = pasta_curves::vesta::Point;
    const R: usize = 3; // arity in PCD. R=1,2,3,4
    const ARITY: usize = 1;
    test_pcd_with::<G1, G2, R, ARITY>().unwrap();
  }
}
