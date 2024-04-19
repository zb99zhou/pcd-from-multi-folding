use std::marker::PhantomData;
use ff::Field;

use serde::{Deserialize, Serialize};
use crate::bellpepper::r1cs::NovaShape;
use crate::bellpepper::shape_cs::ShapeCS;

use crate::CommitmentKey;
use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use crate::errors::NovaError;
use crate::gadgets::utils::scalar_as_base;
use crate::nimfs::ccs::cccs::{CCCS, CCSWitness};
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::multifolding::{MultiFolding, NIMFS, Proof};
use crate::nimfs::pcd_aux_circuit::{NovaAuxiliaryInputs, NovaAuxiliaryParams, NovaAuxiliarySecondCircuit};
use crate::nimfs::pcd_circuit::{PCDUnitInputs, PCDUnitParams, PCDUnitPrimaryCircuit};
use crate::r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness};
use crate::traits::{Group, ROConstants, ROConstantsCircuit, ROTrait, TEConstantsCircuit, TranscriptEngineTrait};
use crate::traits::circuit::{StepCircuit, TrivialTestCircuit};
use crate::traits::snark::{LinearCommittedCCSTrait, RelaxedR1CSSNARKTrait};

pub struct PCDPublicParams<G1, G2, SC, const ARITY: usize, const R: usize>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        SC: StepCircuit<G1::Scalar>,
{
    // F_arity_primary: usize,
    // F_arity_secondary: usize,
    // ccs_primary: CCS<G1>,
    pub(crate) r1cs_shape_primary: R1CSShape<G1>,
    pub(crate) ro_consts_primary: ROConstants<G1>,
    pub(crate) ro_consts_secondary: ROConstants<G2>,
    pub(crate) ro_consts_circuit_primary: ROConstantsCircuit<G2>,
    pub(crate) ro_consts_circuit_secondary: ROConstantsCircuit<G1>,
    pub(crate) te_consts_circuit_primary: TEConstantsCircuit<G2>,
    pub(crate) te_consts_circuit_secondary: TEConstantsCircuit<G1>,
    pub(crate) ck_primary: CommitmentKey<G1>,
    pub(crate) ck_secondary: CommitmentKey<G2>,
    pub(crate) augmented_circuit_params_primary: PCDUnitParams<G1, ARITY, R>,
    pub(crate) augmented_circuit_params_secondary: NovaAuxiliaryParams<G2>,
    // digest: G1::Scalar, // digest of everything else with this field set to G1::Scalar::ZERO
    pub(crate) _p_c: PhantomData<SC>,
    // _p_c1: PhantomData<C1>,
    // _p_c2: PhantomData<C2>,
}

impl<G1, G2, SC, const ARITY: usize, const R: usize> PCDPublicParams<G1, G2, SC, ARITY, R>
where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
    SC: StepCircuit<G1::Scalar>,
{
    pub fn setup() -> Self {
        let ro_consts_primary: ROConstants<G1> = Default::default();
        let ro_consts_secondary: ROConstants<G2> = Default::default();
        let ro_consts_circuit_primary: ROConstantsCircuit<G2> = Default::default();
        let ro_consts_circuit_secondary: ROConstantsCircuit<G1> = Default::default();
        let te_consts_circuit_primary: TEConstantsCircuit<G2> = Default::default();
        let te_consts_circuit_secondary: TEConstantsCircuit<G1> = Default::default();

        let aux_circuit_setup_input = NovaAuxiliaryInputs::<G1>::new(None, None, None, None, R);
        let aux_circuit_setup = NovaAuxiliarySecondCircuit::<G1>::new(aux_circuit_setup_input);
        let mut cs_aux_helper: ShapeCS<G2> = ShapeCS::new();
        let _ = aux_circuit_setup.synthesize(&mut cs_aux_helper);
        let (aux_r1cs_shape, ck_secondary) = cs_aux_helper.r1cs_shape();
        println!("Created aux_r1cs_shape");
        let circuit_params_primary_for_setup: PCDUnitParams<G1, ARITY, R> = PCDUnitParams::default_for_pcd(BN_LIMB_WIDTH, BN_N_LIMBS);
        let augmented_circuit_params_secondary: NovaAuxiliaryParams<G2> = NovaAuxiliaryParams::new(aux_r1cs_shape, ARITY);

        println!("Created 2nd pp");
        let pcd_circuit_setup_input = PCDUnitInputs::<G2>::new(
            scalar_as_base::<G1>(circuit_params_primary_for_setup.digest),
            vec![G2::Base::ZERO; ARITY],
            None, None, None, None, None, None, None, None,
        );
        let test_circuit = TrivialTestCircuit::<<G2 as Group>::Base>::default();
        let pcd_circuit_setup = PCDUnitPrimaryCircuit::<
            '_,
            G2,
            G1,
            TrivialTestCircuit<<G2 as Group>::Base>, ARITY, R,
        >::new(
            &circuit_params_primary_for_setup,
            Some(pcd_circuit_setup_input),
            &test_circuit,
            ro_consts_circuit_primary.clone(),
            te_consts_circuit_primary.clone(),
        );
        let mut cs_pcd_helper: ShapeCS<G1> = ShapeCS::new();
        let _ = pcd_circuit_setup.synthesize(&mut cs_pcd_helper);
        let (r1cs_shape_primary, ck_primary) = cs_pcd_helper.r1cs_shape();
        println!("num_vars:{}, num_cons:{}", r1cs_shape_primary.num_vars, r1cs_shape_primary.num_cons);
        let ccs_primary = CCS::<G1>::from(r1cs_shape_primary.clone());
        let augmented_circuit_params_primary = PCDUnitParams::<G1, ARITY, R>::new(BN_LIMB_WIDTH, BN_N_LIMBS, ccs_primary);
        let _p_c = PhantomData::<SC>::default();

        Self{
            r1cs_shape_primary,
            ro_consts_primary,
            ro_consts_secondary,
            ro_consts_circuit_primary,
            ro_consts_circuit_secondary,
            te_consts_circuit_primary,
            te_consts_circuit_secondary,
            ck_primary,
            ck_secondary,
            augmented_circuit_params_primary,
            augmented_circuit_params_secondary,
            _p_c,
        }

    }
}
pub struct PCDRecursiveSNARK<G1, G2, SC>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        SC: StepCircuit<G1::Scalar>,
{
    r_w_primary: CCSWitness<G1>,
    r_u_primary: CCCS<G1>,
    r_W_primary: CCSWitness<G1>,
    r_U_primary: LCCCS<G1>,
    r_W_secondary: RelaxedR1CSWitness<G2>,
    r_U_secondary: RelaxedR1CSInstance<G2>,
    i: usize,
    zi_primary: Vec<G1::Scalar>,
    _p_c: PhantomData<SC>,
    // _p_c2: PhantomData<C2>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PCDProverKey<G1, G2, SC, S1, S2>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        SC: StepCircuit<G1::Scalar>,
        // C2: StepCircuit<G2::Scalar>,
        S1: LinearCommittedCCSTrait<G1>,
        S2: RelaxedR1CSSNARKTrait<G2>,
{
    pk_primary: S1::ProverKey,
    pk_secondary: S2::ProverKey,
    _p_c: PhantomData<SC>,
    // _p_c2: PhantomData<C2>,
}

/// A type that holds the verifier key for `CompressedSNARK`
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PCDVerifierKey<G1, G2, SC, S1, S2, const ARITY: usize>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        SC: StepCircuit<G1::Scalar>,
        S1: LinearCommittedCCSTrait<G1>,
        S2: RelaxedR1CSSNARKTrait<G2>,
{
    // F_arity_primary: usize,
    // F_arity_secondary: usize,
    ro_consts_primary: ROConstants<G1>,
    ro_consts_secondary: ROConstants<G2>,
    digest: G1::Scalar,
    vk_primary: S1::VerifierKey,
    vk_secondary: S2::VerifierKey,
    _p_c: PhantomData<SC>,
    // _p_c2: PhantomData<C2>,
}

/// A SNARK that proves the knowledge of a valid `RecursiveSNARK`
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PCDCompressedSNARK<G1, G2, SC, S1, S2>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        SC: StepCircuit<G1::Scalar>,
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
    // _p_c2: PhantomData<C2>,
}

impl<G1, G2, SC, S1, S2> PCDCompressedSNARK<G1, G2, SC, S1, S2>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        SC: StepCircuit<G1::Scalar>,
        S1: LinearCommittedCCSTrait<G1>,
        S2: RelaxedR1CSSNARKTrait<G2>,
{
    /// Creates prover and verifier keys for `CompressedSNARK`
    pub fn setup<const ARITY: usize, const R: usize>(
        pp: &PCDPublicParams<G1, G2, SC, ARITY, R>,
    ) -> Result<
        (
            PCDProverKey<G1, G2, SC, S1, S2>,
            PCDVerifierKey<G1, G2, SC, S1, S2, ARITY>,
        ),
        NovaError,
    > {
        let (pk_primary, vk_primary) = S1::setup(&pp.ck_primary, &pp.augmented_circuit_params_primary.ccs)?;
        let (pk_secondary, vk_secondary) = S2::setup(&pp.ck_secondary, &pp.augmented_circuit_params_secondary.r1cs_shape)?;

        let pk = PCDProverKey {
            pk_primary,
            pk_secondary,
            _p_c: Default::default(),
        };

        let vk = PCDVerifierKey {
            ro_consts_primary: pp.ro_consts_primary.clone(),
            ro_consts_secondary: pp.ro_consts_secondary.clone(),
            digest: pp.augmented_circuit_params_primary.digest,
            vk_primary,
            vk_secondary,
            _p_c: Default::default(),
        };

        Ok((pk, vk))
    }

    const TRANSCRIPT_INIT_STR:&'static [u8; 4] = b"init";

    /// Create a new `CompressedSNARK`
    pub fn prove<const ARITY: usize, const R: usize>(
        pp: &PCDPublicParams<G1, G2, SC, ARITY, R>,
        pk: &PCDProverKey<G1, G2, SC, S1, S2>,
        recursive_snark: &PCDRecursiveSNARK<G1, G2, SC>,
    ) -> Result<Self, NovaError> {
        // Prover's transcript
        let mut transcript_p = G1::TE::new(Default::default(), b"multifolding");
        transcript_p.squeeze(Self::TRANSCRIPT_INIT_STR).unwrap();

        // fold the primary circuit's instance
        let res_primary = MultiFolding::prove(
            &mut transcript_p,
            &vec![recursive_snark.r_U_primary.clone()],
            &vec![recursive_snark.r_u_primary.clone()],
            &vec![recursive_snark.r_W_primary.clone()],
            &vec![recursive_snark.r_w_primary.clone()]
        );
        let (nimfs_proof, f_U_primary, f_W_primary) = res_primary;
        let (f_W_snark_primary, r_W_snark_secondary) = rayon::join(
            || {
                S1::prove(
                    &pp.ck_primary,
                    &pk.pk_primary,
                    &f_U_primary,
                    &f_W_primary,
                )
            },
            || {
                S2::prove(
                    &pp.ck_secondary,
                    &pk.pk_secondary,
                    &recursive_snark.r_U_secondary,
                    &recursive_snark.r_W_secondary,
                )
            },
        );

        Ok(Self {
            r_u_primary: recursive_snark.r_u_primary.clone(),
            r_U_primary: recursive_snark.r_U_primary.clone(),
            nimfs_proof,
            f_W_snark_primary: f_W_snark_primary?,

            r_U_secondary: recursive_snark.r_U_secondary.clone(),
            r_W_snark_secondary: r_W_snark_secondary?,

            zn_primary: recursive_snark.zi_primary.clone(),

            _p_c: Default::default(),
        })

    }

    /// Verify the correctness of the `CompressedSNARK`
    pub fn verify<const ARITY: usize>(
        &self,
        vk: &PCDVerifierKey<G1, G2, SC, S1, S2, ARITY>,
        z0_primary: Vec<G1::Scalar>,
    ) -> Result<Vec<G1::Scalar>, NovaError> {
        // check if the instances have two public outputs
        if self.r_u_primary.x.len() != 1
            || self.r_U_primary.x.len() != 1
            || self.r_U_secondary.X.len() != 1
        {
            return Err(NovaError::ProofVerifyError);
        }

        // check if the output hashes in R1CS instances point to the right running instances
        let hash_primary = {
            let mut hasher = <G2 as Group>::RO::new(
                vk.ro_consts_secondary.clone(),
                NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * ARITY,
            );
            hasher.absorb(vk.digest);
            for e in z0_primary {
                hasher.absorb(e);
            }
            for e in &self.zn_primary {
                hasher.absorb(*e);
            }
            self.r_U_primary.absorb_in_ro::<G2>(&mut hasher);

            hasher.squeeze(NUM_HASH_BITS)
        };

        if scalar_as_base::<G2>(hash_primary) != self.r_u_primary.x[0] {
            return Err(NovaError::ProofVerifyError);
        }

        // Prover's transcript
        let mut transcript_p = G1::TE::new(Default::default(), b"multifolding");
        transcript_p.squeeze(Self::TRANSCRIPT_INIT_STR).unwrap();

        // fold the running instance and last instance to get a folded instance
        let f_U_primary = NIMFS::verify(
            &mut transcript_p,
            &[self.r_U_primary.clone()],
            &[self.r_u_primary.clone()],
            self.nimfs_proof.clone(),
        );

        // check the satisfiability of the folded instances using SNARKs proving the knowledge of their satisfying witnesses
        let (res_primary, res_secondary) = rayon::join(
            || {
                self
                    .f_W_snark_primary
                    .verify(&vk.vk_primary, &f_U_primary)
            },
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

}