use bellpepper_core::ConstraintSystem;
use crate::bellpepper::shape_cs::ShapeCS;
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::{Commitment, CommitmentKey};
use crate::bellpepper::r1cs::{NovaShape, NovaWitness};
use crate::constants::{ NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use crate::errors::NovaError;
use crate::gadgets::utils::scalar_as_base;
use crate::nifs::NIFS;
use crate::nimfs::ccs::cccs::{CCCS, CCSWitness};
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::multifolding::{NIMFS, ProofWitness};
use crate::nimfs::pcd_aux_circuit::{NovaAuxiliaryInputs, NovaAuxiliaryParams, NovaAuxiliarySecondCircuit};
use crate::nimfs::pcd_circuit::{PCDUnitInputs, PCDUnitPrimaryCircuit};
use crate::pcd_compressed_snark::PCDPublicParams;
use crate::r1cs::{RelaxedR1CSInstance, RelaxedR1CSWitness};
use crate::traits::{AbsorbInROTrait, Group, ROConstants, ROTrait, TranscriptEngineTrait};
use crate::traits::circuit::{StepCircuit, TrivialTestCircuit};
use crate::traits::commitment::CommitmentTrait;



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
        Self{
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

    pub fn prove_step<SC: StepCircuit<<G2 as Group>::Base>>(&self, pp: &PCDPublicParams<G1, G2, SC, ARITY, R>) -> Result<
        (
            LCCCS<G1>, CCCS<G1>, RelaxedR1CSInstance<G2>,
            CCSWitness<G1>, CCSWitness<G1>, RelaxedR1CSWitness<G2>,
            Vec<G1::Scalar>, CommitmentKey<G1>
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
        let pp_aux = NovaAuxiliaryParams::<G2>::new(pp.augmented_circuit_params_secondary.r1cs_shape.clone() , ARITY);
        let rho = scalar_as_base::<G1>(transcript_p.get_last_state());
        let aux_circuit_input = NovaAuxiliaryInputs::<G1>::new(
            Some(pp_aux.digest),
            Some(self.lcccs.to_vec()),
            Some(self.cccs.to_vec()),
            Some(rho),
            R,
        );

        let aux_circuit = NovaAuxiliarySecondCircuit::<G1>::new(
            aux_circuit_input,
        );
        let mut cs_secondary = SatisfyingAssignment::<G2>::new();
        let _ = aux_circuit.clone().synthesize(&mut cs_secondary);

        // TODO: move these codes into setup
        let (aux_r1cs_shape, aux_commit_key) = {
            let mut cs_aux_helper: ShapeCS<G2> = ShapeCS::new();
            let _ = aux_circuit.clone().synthesize(&mut cs_aux_helper);
            cs_aux_helper.r1cs_shape()
        };

        let (aux_r1cs_instance, aux_r1cs_witness) = cs_secondary.r1cs_instance_and_witness(&aux_r1cs_shape, &aux_commit_key)?;

        // Then, handling the PCD primary circuit
        let (nifs_proof, (relaxed_r1cs_instance, relaxed_r1cs_witness) ) =
            NIFS::prove_with_multi_relaxed(
                &aux_commit_key,
                &pp.ro_consts_secondary,
                &pp_aux.digest,
                &aux_r1cs_shape,
                self.relaxed_r1cs_instance.as_ref().unwrap(),
                self.w_relaxed_r1cs.as_ref().unwrap(),
                &aux_r1cs_instance,
                &aux_r1cs_witness,
            )?;
        println!("Finish NIFS prove_with_multi_relaxed");
        let pcd_circuit_input= PCDUnitInputs::<G2>::new(
            scalar_as_base::<G1>(pp.augmented_circuit_params_primary.digest),
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

        // TODO: move test_circuit into a field SC: StepCircuit of Self
        let test_circuit = TrivialTestCircuit::<<G2 as Group>::Base>::default();
        let pcd_circuit = PCDUnitPrimaryCircuit::<
            '_,
            G2,
            G1,
            TrivialTestCircuit<<G2 as Group>::Base>, ARITY, R,
        >::new(
            &pp.augmented_circuit_params_primary,
            Some(pcd_circuit_input),
            &test_circuit,
            pp.ro_consts_circuit_primary.clone(),
            pp.te_consts_circuit_primary.clone(),
        );

        let mut cs_primary = SatisfyingAssignment::<G1>::new();
        let zi_primary = pcd_circuit.clone().synthesize(&mut cs_primary)
            .unwrap()
            .iter()
            .map(|v| v.get_value().ok_or(NovaError::SynthesisError))
            .collect::<Result<Vec<<G1 as Group>::Scalar>, NovaError>>()?;

        // TODO: move these codes into setup
        let (r1cs_shape_pcd, ck_pcd) = {
            let mut cs_helper: ShapeCS<G1> = ShapeCS::new();
            let _ = pcd_circuit.synthesize(&mut cs_helper);
            cs_helper.r1cs_shape()
        };

        let (cccs, cccs_witness) = cs_primary.cccs_and_witness(&r1cs_shape_pcd, &ck_pcd)?;
        Ok((
            lcccs,
            cccs,
            relaxed_r1cs_instance,
            lcccs_witness,
            cccs_witness,
            relaxed_r1cs_witness,
            zi_primary,
            ck_pcd,
        ))
    }

    pub fn verify<SC: StepCircuit<<G2 as Group>::Base>>(
        &self,
        lcccs: &LCCCS<G1>,
        U: &RelaxedR1CSInstance<G2>,
        W: &RelaxedR1CSWitness<G2>,
        zi_primary: &[G1::Scalar],
        ck: &CommitmentKey<G1>,
        u: &CCCS<G1>,
        w_cccs: &CCSWitness<G1>,
        w_lcccs: &CCSWitness<G1>,
        pp: &PCDPublicParams<G1, G2, SC, ARITY, R>,
    ) -> Result<Vec<G1::Scalar>, NovaError> {
        if U.X.len() != 2
        {
            return Err(NovaError::ProofVerifyError);
        }

        let ro_consts: ROConstants<G2> = Default::default();

        let mut hasher1 = <G2 as Group>::RO::new(
            ro_consts.clone(),
            NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * ARITY,
        );
        hasher1.absorb(pp.augmented_circuit_params_primary.digest);
        for e in zi_primary {
            hasher1.absorb(*e);
        }

        U.absorb_in_ro(&mut hasher1);

        let mut hasher2 = <G2 as Group>::RO::new(
            ro_consts.clone(),
            NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * ARITY,
        );
        hasher2.absorb(pp.augmented_circuit_params_primary.digest);
        for e in zi_primary {
            hasher2.absorb(*e);
        }

        lcccs.absorb_in_ro::<G2>(&mut hasher2);
        let hash_U = hasher1.squeeze(NUM_HASH_BITS);
        let hash_lcccs = hasher2.squeeze(NUM_HASH_BITS);
        if hash_U != scalar_as_base::<G1>(u.x[0]) || hash_lcccs != scalar_as_base::<G1>(u.x[0])
        {
            return Err(NovaError::ProofVerifyError);
        }
        let (res_U, (res_lcccs, res_cccs)) = rayon::join(
            || {
                pp.augmented_circuit_params_secondary.r1cs_shape
                    .is_sat_relaxed(&pp.ck_secondary, U, W)
            },
            || {
                rayon::join(
                    || {
                        lcccs.check_relation(ck, w_lcccs)
                    },
                    || {
                        u.check_relation(ck, w_cccs)
                    },
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
    use crate::errors::NovaError;
    use crate::nimfs::ccs::cccs::{CCCS, CCSWitness};
    use crate::nimfs::ccs::lcccs::LCCCS;
    use crate::pcd_compressed_snark::PCDPublicParams;
    use crate::pcd_node::PCDNode;
    use crate::r1cs::RelaxedR1CSInstance;
    use crate::traits::circuit::TrivialTestCircuit;
    use crate::traits::Group;

    fn test_pcd_with<G1, G2, const R: usize, const IO_NUM: usize>() -> Result<(), NovaError>
        where
            G1: Group<Base = <G2 as Group>::Scalar>,
            G2: Group<Base = <G1 as Group>::Scalar>,
    {
        println!("Start pcd_test");
        let z0 = vec![<G1 as Group>::Scalar::ZERO; IO_NUM];
        let pp = PCDPublicParams::<
            G1,
            G2,
            TrivialTestCircuit<<G1 as Group>::Scalar>,
            IO_NUM,
            R,
        >::setup();

        println!("Finished pp setup");
        let node_1 = PCDNode::<
            G1,
            G2,
            IO_NUM,
            R>::new(
            vec![LCCCS::<G1>::default_for_pcd(pp.augmented_circuit_params_primary.ccs.clone()),LCCCS::<G1>::default_for_pcd(pp.augmented_circuit_params_primary.ccs.clone())],
            vec![CCCS::<G1>::default_for_pcd(pp.augmented_circuit_params_primary.ccs.clone()),CCCS::<G1>::default_for_pcd(pp.augmented_circuit_params_primary.ccs.clone())],
            z0.clone(),
            None,
            Some(vec![RelaxedR1CSInstance::<G2>::default_for_pcd(), RelaxedR1CSInstance::<G2>::default_for_pcd()]),
            Some(vec![CCSWitness::<G1>::default_for_pcd(&pp.augmented_circuit_params_primary.ccs), CCSWitness::<G1>::default_for_pcd(&pp.augmented_circuit_params_primary.ccs)]),
            Some(vec![CCSWitness::<G1>::default_for_pcd(&pp.augmented_circuit_params_primary.ccs), CCSWitness::<G1>::default_for_pcd(&pp.augmented_circuit_params_primary.ccs)]),
            None,
        );

        println!("Finished node_1 new");
        let (
            node_1_lcccs, node_1_cccs, node_1_relaxed_r1cs_instance,
            node_1_lcccs_witness, node_1_cccs_witness, node_1_relaxed_r1cs_witness,
            node_1_zi, _
        ) = node_1.prove_step(&pp).map_err(|_| NovaError::SynthesisError)?;

        println!("Finished node_1 prove_step");
        let node_2 = node_1.clone();
        let (
            node_2_lcccs, node_2_cccs, node_2_relaxed_r1cs_instance,
            node_2_lcccs_witness, node_2_cccs_witness, node_2_folded_relaxed_r1cs_witness,
            node_2_zi, _
        ) = node_2.prove_step(&pp).map_err(|_| NovaError::SynthesisError)?;

        let node_3_input_lcccs = vec![node_1_lcccs, node_2_lcccs];
        let node_3_input_cccs = vec![node_1_cccs, node_2_cccs];
        let node_3_zi = vec![node_1_zi, node_2_zi];
        let node_3_relaxed_r1cs_instance = vec![node_1_relaxed_r1cs_instance, node_2_relaxed_r1cs_instance];
        let node_3_lcccs_witness = vec![node_1_lcccs_witness, node_2_lcccs_witness];
        let node_3_cccs_witness = vec![node_1_cccs_witness, node_2_cccs_witness];
        let node_3_relaxed_r1cs_witness = vec![node_1_relaxed_r1cs_witness, node_2_folded_relaxed_r1cs_witness];

        let node_3 = PCDNode::<
            G1,
            G2,
            IO_NUM,
            R>::new(
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
            node_3_lcccs_witness, node_3_cccs_witness, node_3_folded_relaxed_r1cs_witness,
            node_3_zi, node_3_ck
        ) = node_3.prove_step(&pp).map_err(|_| NovaError::SynthesisError)?;

        let res = node_3.verify(
            &node_3_lcccs,
            &node_3_relaxed_r1cs_instance,
            &node_3_folded_relaxed_r1cs_witness,
            &node_3_zi,
            &node_3_ck,
            &node_3_cccs,
            &node_3_cccs_witness,
            &node_3_lcccs_witness,
            &pp,
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
}