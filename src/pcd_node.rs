use bellpepper_core::ConstraintSystem;
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::Commitment;
use crate::bellpepper::r1cs::NovaWitness;
use crate::constants::{ NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use crate::errors::NovaError;
use crate::gadgets::utils::scalar_as_base;
use crate::nifs::NIFS;
use crate::nimfs::ccs::cccs::{CCCS, CCSWitness};
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::multifolding::{NIMFS, ProofWitness};
use crate::nimfs::pcd_aux_circuit::{NovaAuxiliaryInputs, NovaAuxiliaryParams, NovaAuxiliarySecondCircuit};
use crate::nimfs::pcd_circuit::{PCDUnitInputs, PCDUnitPrimaryCircuit};
use crate::pcd_compressed_snark::{PCDPublicParams};
use crate::r1cs::{RelaxedR1CSInstance, RelaxedR1CSWitness};
use crate::traits::{AbsorbInROTrait, Group, ROTrait, TranscriptEngineTrait};
use crate::traits::circuit::PCDStepCircuit;
use crate::traits::commitment::{ CommitmentTrait};

#[derive(Clone)]
pub struct PCDNode<G1, G2, const ARITY: usize, const R: usize>
    where
        G1: Group<Base=<G2 as Group>::Scalar>,
        G2: Group<Base=<G1 as Group>::Scalar>,
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
        G1: Group<Base=<G2 as Group>::Scalar>,
        G2: Group<Base=<G1 as Group>::Scalar>,
{
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

    pub fn prove_step<SC: PCDStepCircuit<<G2 as Group>::Base, ARITY, R>>(
        &self,
        pp: &PCDPublicParams<G1, G2, SC, ARITY, R>,
        pcd_step_circuit: &SC
    ) -> Result<
        (
            LCCCS<G1>, CCCS<G1>, RelaxedR1CSInstance<G2>,
            CCSWitness<G1>, CCSWitness<G1>, RelaxedR1CSWitness<G2>,
            Vec<G1::Scalar>
        ), NovaError
    > {
        let mut transcript_p = <G1 as Group>::TE::new(Default::default(), b"multifolding");
        transcript_p.squeeze(b"init").unwrap();

        // First, handling PCD auxiliary secondary circuit
        let (nimfs_proof, lcccs, lcccs_witness) =
            NIMFS::prove(
                &mut transcript_p,
                &self.lcccs,
                &self.cccs,
                self.w_lcccs.as_ref().unwrap(),
                self.w_cccs.as_ref().unwrap(),
            );
        println!("Finish NIMFS prove");
        let pp_aux = NovaAuxiliaryParams::<G2>::new(pp.secondary_circuit_params.r1cs_shape.clone(), ARITY);
        let rho = scalar_as_base::<G1>(transcript_p.get_last_state());
        let aux_circuit_input = NovaAuxiliaryInputs::<G1>::new(
            Some(pp_aux.digest),
            Some(self.lcccs.to_vec()),
            Some(self.cccs.to_vec()),
            Some(rho),
            R,
        );

        let aux_circuit = NovaAuxiliarySecondCircuit::<G1>::new(aux_circuit_input);
        let mut cs_secondary = SatisfyingAssignment::<G2>::new();
        let _ = aux_circuit.synthesize(&mut cs_secondary)?;
        let (aux_r1cs_instance, aux_r1cs_witness) = cs_secondary.r1cs_instance_and_witness(
            &pp.secondary_circuit_params.r1cs_shape,
            &pp.ck_secondary
        )?;

        // Then, handling the PCD primary circuit
        let (nifs_proof, (relaxed_r1cs_instance, relaxed_r1cs_witness)) =
            NIFS::prove_with_multi_relaxed(
                &pp.ck_secondary,
                &pp.ro_consts_secondary,
                &pp.secondary_circuit_params.digest,
                &pp.secondary_circuit_params.r1cs_shape,
                self.relaxed_r1cs_instance.as_ref().unwrap(),
                self.w_relaxed_r1cs.as_ref().unwrap(),
                &aux_r1cs_instance,
                &aux_r1cs_witness,
            )?;
        println!("Finish NIFS prove_with_multi_relaxed");

        let pcd_circuit_input = PCDUnitInputs::<G2>::new(
            scalar_as_base::<G1>(pp.primary_circuit_params.digest),
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
                    .collect::<Result<Vec<_>, NovaError>>()?
            ),
            Some(ProofWitness::<G2>::from(nimfs_proof)),
        );

        let pcd_circuit = PCDUnitPrimaryCircuit::<'_, G2, G1, _, ARITY, R>::new(
            &pp.primary_circuit_params,
            Some(pcd_circuit_input),
            pcd_step_circuit,
            pp.ro_consts_circuit_primary.clone(),
            pp.te_consts_circuit_primary.clone(),
        );

        let mut cs_primary = SatisfyingAssignment::<G1>::new();
        let zi_primary = pcd_circuit.synthesize(&mut cs_primary)?
            .iter()
            .map(|v| v.get_value().ok_or(NovaError::SynthesisError))
            .collect::<Result<Vec<<G1 as Group>::Scalar>, NovaError>>()?;
        let (cccs, cccs_witness) = cs_primary.cccs_and_witness(
            pp.primary_circuit_params.ccs.clone(),
            &pp.ck_primary
        )?;
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
        if U.X.len() != 16  && lcccs.x.len() != 1 && cccs.x.len() != 1 {
            return Err(NovaError::ProofVerifyError);
        }

        let mut hasher = <G2 as Group>::RO::new(
            pp.ro_consts_secondary.clone(),
            NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * ARITY,
        );
        hasher.absorb(pp.primary_circuit_params.digest);
        for e in zi_primary {
            hasher.absorb(*e);
        }
        U.absorb_in_ro(&mut hasher);
        lcccs.absorb_in_ro::<G2>(&mut hasher);
        let hash_U = hasher.squeeze(NUM_HASH_BITS);

        if hash_U != scalar_as_base::<G1>(cccs.x[0]) {
            return Err(NovaError::ProofVerifyError);
        }

        let (res_U, (res_lcccs, res_cccs)) = rayon::join(
            || {
                pp.secondary_circuit_params.r1cs_shape
                    .is_sat_relaxed(&pp.ck_secondary, U, W)
            },
            || {
                rayon::join(
                    || lcccs.check_relation(&pp.ck_primary, w_lcccs),
                    || cccs.check_relation(&pp.ck_primary, w_cccs),
                )
            },
        );
        res_U.map_err(|_| NovaError::ProofVerifyError)?;
        res_lcccs.map_err(|_| NovaError::ProofVerifyError)?;
        res_cccs.map_err(|_| NovaError::ProofVerifyError)?;
        Ok(zi_primary.to_vec())
    }
}

#[cfg(test)]
mod test {
    use ff::Field;
    use rand_core::OsRng;
    use crate::errors::NovaError;
    // use crate::nimfs::ccs::cccs::{CCCS, CCSWitness};
    // use crate::nimfs::ccs::lcccs::LCCCS;
    use crate::pcd_compressed_snark::{PCDCompressedSNARK, PCDPublicParams, PCDRecursiveSNARK};
    use crate::pcd_node::PCDNode;
    use crate::provider::ipa_pc::EvaluationEngine;
    use crate::provider::pedersen::CommitmentKeyExtTrait;
    use crate::r1cs::{RelaxedR1CSInstance, RelaxedR1CSWitness};
    use crate::spartan::lcccs::LCCCSSNARK;
    use crate::spartan::ppsnark::RelaxedR1CSSNARK;
    use crate::traits::circuit::TrivialTestCircuit;
    use crate::traits::commitment::CommitmentEngineTrait;
    use crate::traits::evaluation::EvaluationEngineTrait;
    use crate::traits::Group;

    fn test_pcd_with<G1, G2, const R: usize, const IO_NUM: usize>() -> Result<(), NovaError>
        where
            G1: Group<Base = <G2 as Group>::Scalar>,
            G2: Group<Base = <G1 as Group>::Scalar>,
    {
        println!("Start pcd_test");
        let z0 = vec![<G1 as Group>::Scalar::ZERO; IO_NUM];
        let test_circuit = TrivialTestCircuit::<<G2 as Group>::Base>::default();
        let pp = PCDPublicParams::<G1, G2, _, IO_NUM, R>::setup(&test_circuit);

        let rng = OsRng;
        let z = vec![G1::Scalar::ONE; pp.primary_circuit_params.ccs.n];
        let (default_cccs, default_w_cccs) = pp.primary_circuit_params.ccs.to_cccs(rng, &pp.ck_primary, &z);
        let (default_lcccs, default_w_lcccs) = pp.primary_circuit_params.ccs.to_lcccs(rng, &pp.ck_primary, &z);
        let default_relaxed_r1cs_instance = RelaxedR1CSInstance::<G2>::default_for_pcd(pp.secondary_circuit_params.r1cs_shape.num_io.clone());
        let default_relaxed_r1cs_witness = RelaxedR1CSWitness::<G2>::default(&pp.secondary_circuit_params.r1cs_shape);
        println!("Finished pp setup");
        let node_1 = PCDNode::<G1, G2, IO_NUM, R>::new(
            vec![default_lcccs.clone(),default_lcccs.clone()],
            vec![default_cccs.clone(),default_cccs.clone()],
            z0.clone(),
            None,
            Some(vec![default_relaxed_r1cs_instance.clone(), default_relaxed_r1cs_instance.clone()]),
            Some(vec![default_w_lcccs.clone(), default_w_lcccs.clone()]),
            Some(vec![default_w_cccs.clone(), default_w_cccs.clone()]),
            Some(vec![default_relaxed_r1cs_witness.clone(), default_relaxed_r1cs_witness.clone()]),
        );

        println!("Finished node_1 new");
        let (
            node_1_lcccs, node_1_cccs, node_1_relaxed_r1cs_instance,
            node_1_lcccs_witness, node_1_cccs_witness, node_1_relaxed_r1cs_witness,
            node_1_zi
        ) = node_1.prove_step(&pp, &test_circuit).map_err(|_| NovaError::SynthesisError)?;

        println!("Finished node_1 prove_step");
        let node_2 = node_1.clone();
        let (
            node_2_lcccs, node_2_cccs, node_2_relaxed_r1cs_instance,
            node_2_lcccs_witness, node_2_cccs_witness, node_2_folded_relaxed_r1cs_witness,
            node_2_zi
        ) = node_2.prove_step(&pp, &test_circuit).map_err(|_| NovaError::SynthesisError)?;

        let node_3_input_lcccs = vec![node_1_lcccs, node_2_lcccs];
        let node_3_input_cccs = vec![node_1_cccs, node_2_cccs];
        let node_3_zi = vec![node_1_zi, node_2_zi];
        let node_3_relaxed_r1cs_instance = vec![node_1_relaxed_r1cs_instance, node_2_relaxed_r1cs_instance];
        let node_3_lcccs_witness = vec![node_1_lcccs_witness, node_2_lcccs_witness];
        let node_3_cccs_witness = vec![node_1_cccs_witness, node_2_cccs_witness];
        let node_3_relaxed_r1cs_witness = vec![node_1_relaxed_r1cs_witness, node_2_folded_relaxed_r1cs_witness];

        let node_3 = PCDNode::<G1, G2, IO_NUM, R>::new(
            node_3_input_lcccs,
            node_3_input_cccs,
            z0,
            Some(node_3_zi),
            Some(node_3_relaxed_r1cs_instance),
            Some(node_3_lcccs_witness),
            Some(node_3_cccs_witness),
            Some(node_3_relaxed_r1cs_witness),
        );

        let (
            node_3_lcccs, node_3_cccs, node_3_relaxed_r1cs_instance,
            node_3_lcccs_witness, node_3_cccs_witness, node_3_relaxed_r1cs_witness,
            node_3_zi
        ) = node_3.prove_step(&pp, &test_circuit).map_err(|_| NovaError::SynthesisError)?;


        let res = node_3.verify(
            &pp,
            &node_3_zi,
            &node_3_lcccs,
            &node_3_lcccs_witness,
            &node_3_cccs,
            &node_3_cccs_witness,
            &node_3_relaxed_r1cs_instance,
            &node_3_relaxed_r1cs_witness,
        );

        assert!(res.is_ok());
        Ok(())
    }

    #[test]
    fn test_pcd(){
        type G1 = pasta_curves::pallas::Point;
        type G2 = pasta_curves::vesta::Point;
        const ARITY: usize = 1;
        const R: usize = 2;
        test_pcd_with::<G1, G2, R, ARITY>().unwrap();
    }

    fn test_pcd_with_compressed_verify_with<
        G1, G2,
        const R: usize, const IO_NUM: usize,
        EE1: EvaluationEngineTrait<G1>,
        EE2: EvaluationEngineTrait<G2>,
    >() -> Result<(), NovaError>
        where
            G1: Group<Base=<G2 as Group>::Scalar>,
            G2: Group<Base=<G1 as Group>::Scalar>,
            <G1::CE as CommitmentEngineTrait<G1>>::CommitmentKey: CommitmentKeyExtTrait<G1>,
            <G2::CE as CommitmentEngineTrait<G2>>::CommitmentKey: CommitmentKeyExtTrait<G2>,
    {
        println!("Start pcd_test");
        let z0 = vec![<G1 as Group>::Scalar::ZERO; IO_NUM];
        let test_circuit = TrivialTestCircuit::<<G2 as Group>::Base>::default();
        let pp = PCDPublicParams::<G1, G2, _, IO_NUM, R>::setup(&test_circuit);
        println!("Finished pp setup");

        let rng = OsRng;
        let z = vec![G1::Scalar::ONE; pp.primary_circuit_params.ccs.n];
        let (default_cccs, default_w_cccs) = pp.primary_circuit_params.ccs.to_cccs(rng, &pp.ck_primary, &z);
        let (default_lcccs, default_w_lcccs) = pp.primary_circuit_params.ccs.to_lcccs(rng, &pp.ck_primary, &z);
        let default_relaxed_r1cs_instance = RelaxedR1CSInstance::<G2>::default_for_pcd(pp.secondary_circuit_params.r1cs_shape.num_io.clone());
        let default_relaxed_r1cs_witness = RelaxedR1CSWitness::<G2>::default(&pp.secondary_circuit_params.r1cs_shape);

        let node_1 = PCDNode::<G1, G2, IO_NUM, R>::new(
            vec![default_lcccs.clone(),default_lcccs.clone()],
            vec![default_cccs.clone(),default_cccs.clone()],
            z0.clone(),
            None,
            Some(vec![default_relaxed_r1cs_instance.clone(), default_relaxed_r1cs_instance.clone()]),
            Some(vec![default_w_lcccs.clone(), default_w_lcccs.clone()]),
            Some(vec![default_w_cccs.clone(), default_w_cccs.clone()]),
            Some(vec![default_relaxed_r1cs_witness.clone(), default_relaxed_r1cs_witness.clone()]),
        );
        println!("Finished node_1 new");
        let (
            node_1_lcccs, node_1_cccs, node_1_relaxed_r1cs_instance,
            node_1_lcccs_witness, node_1_cccs_witness, node_1_relaxed_r1cs_witness,
            node_1_zi
        ) = node_1.prove_step(&pp, &test_circuit).map_err(|_| NovaError::SynthesisError)?;

        println!("Finished node_1 prove_step");
        let node_2 = node_1.clone();
        let (
            node_2_lcccs, node_2_cccs, node_2_relaxed_r1cs_instance,
            node_2_lcccs_witness, node_2_cccs_witness, node_2_folded_relaxed_r1cs_witness,
            node_2_zi
        ) = node_2.prove_step(&pp, &test_circuit).map_err(|_| NovaError::SynthesisError)?;

        let node_3_input_lcccs = vec![node_1_lcccs, node_2_lcccs];
        let node_3_input_cccs = vec![node_1_cccs, node_2_cccs];
        let node_3_zi = vec![node_1_zi, node_2_zi];
        let node_3_relaxed_r1cs_instance = vec![node_1_relaxed_r1cs_instance, node_2_relaxed_r1cs_instance];
        let node_3_lcccs_witness = vec![node_1_lcccs_witness, node_2_lcccs_witness];
        let node_3_cccs_witness = vec![node_1_cccs_witness, node_2_cccs_witness];
        let node_3_relaxed_r1cs_witness = vec![node_1_relaxed_r1cs_witness, node_2_folded_relaxed_r1cs_witness];

        let node_3 = PCDNode::<G1, G2, IO_NUM, R>::new(
            node_3_input_lcccs,
            node_3_input_cccs,
            z0.clone(),
            Some(node_3_zi),
            Some(node_3_relaxed_r1cs_instance),
            Some(node_3_lcccs_witness),
            Some(node_3_cccs_witness),
            Some(node_3_relaxed_r1cs_witness),
        );

        let (
            node_3_lcccs, node_3_cccs, node_3_relaxed_r1cs_instance,
            node_3_lcccs_witness, node_3_cccs_witness, node_3_folded_relaxed_r1cs_witness,
            node_3_zi
        ) = node_3.prove_step(&pp, &test_circuit).map_err(|_| NovaError::SynthesisError)?;


        let recursive_snark = PCDRecursiveSNARK::<G1, G2, _, IO_NUM, R>::new(
            node_3_cccs_witness,
            node_3_cccs,
            node_3_lcccs_witness,
            node_3_lcccs,
            node_3_folded_relaxed_r1cs_witness,
            node_3_relaxed_r1cs_instance,
            node_3_zi,
        );

        let (compressed_pk, compressed_vk) = PCDCompressedSNARK::<
            G1, G2,
            _,
            LCCCSSNARK<G1, EE1>,
            RelaxedR1CSSNARK<G2, EE2>,
            IO_NUM, R
        >::setup(&pp)?;

        let compress_snark = PCDCompressedSNARK::<
            G1,
            G2,
            _,
            LCCCSSNARK<G1, EE1>,
            RelaxedR1CSSNARK<G2, EE2>,
            IO_NUM, R
        >::prove(
            &pp,
            &compressed_pk,
            &recursive_snark,
        )?;

        let res = compress_snark.verify(
            &compressed_vk,
            z0.clone(),
        );
        assert!(res.is_ok());
        Ok(())
    }

    #[test]
    fn test_pcd_with_compressed_verify() {
        type G1 = pasta_curves::pallas::Point;
        type G2 = pasta_curves::vesta::Point;
        const ARITY: usize = 1;
        const R: usize = 2;
        test_pcd_with_compressed_verify_with::<
            G1, G2,
            R, ARITY,
            EvaluationEngine<G1>,
            EvaluationEngine<G2>,
        >().unwrap();
    }
}