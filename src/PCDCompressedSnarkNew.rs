use std::marker::PhantomData;
use serde::{Deserialize, Serialize};
use crate::errors::NovaError;
use crate::r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness};
use crate::traits::circuit::StepCircuit;
use crate::traits::{Group, ROConstants, ROConstantsCircuit, TranscriptEngineTrait};
use crate::traits::snark::{RelaxedR1CSSNARKTrait, LinearCommittedCCSTrait};
use crate::nimfs::ccs::cccs::{CCSWitness, CCCS};
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::circuit::NovaAugmentedCircuitParams;
use crate::CommitmentKey;
use crate::nimfs::ccs::ccs::CCS;
use crate::nimfs::multifolding::{MultiFolding, Proof};
pub struct PCDPublicParams<G1, G2, C1, C2>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        C1: StepCircuit<G1::Scalar>,
        C2: StepCircuit<G2::Scalar>,
{
    F_arity_primary: usize,
    F_arity_secondary: usize,
    ccs_primary: CCS<G1>,
    r1cs_shape_secondary: R1CSShape<G2>,
    ro_consts_primary: ROConstants<G1>,
    ro_consts_secondary: ROConstants<G2>,
    ro_consts_circuit_primary: ROConstantsCircuit<G2>,
    ro_consts_circuit_secondary: ROConstantsCircuit<G1>,
    ck_primary: CommitmentKey<G1>,
    ck_secondary: CommitmentKey<G2>,
    augmented_circuit_params_primary: NovaAugmentedCircuitParams,
    augmented_circuit_params_secondary: NovaAugmentedCircuitParams,
    digest: G1::Scalar, // digest of everything else with this field set to G1::Scalar::ZERO
_p_c1: PhantomData<C1>,
    _p_c2: PhantomData<C2>,
}
pub struct PCDRecursiveSNARK<G1, G2, C1, C2>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        C1: StepCircuit<G1::Scalar>,
        C2: StepCircuit<G2::Scalar>,
{
    r_w_primary: CCSWitness<G1>,
    r_u_primary: CCCS<G1>,
    r_W_primary: CCSWitness<G1>,
    r_U_primary: LCCCS<G1>,
    r_W_secondary: RelaxedR1CSWitness<G2>,
    r_U_secondary: RelaxedR1CSInstance<G2>,
    i: usize,
    zi_primary: Vec<G1::Scalar>,
    zi_secondary: Vec<G2::Scalar>,
    _p_c1: PhantomData<C1>,
    _p_c2: PhantomData<C2>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PCDProverKey<G1, G2, C1, C2, S1, S2>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        C1: StepCircuit<G1::Scalar>,
        C2: StepCircuit<G2::Scalar>,
        S1: LinearCommittedCCSTrait<G1>,
        S2: RelaxedR1CSSNARKTrait<G2>,
{
    pk_primary: S1::ProverKey,
    pk_secondary: S2::ProverKey,
    _p_c1: PhantomData<C1>,
    _p_c2: PhantomData<C2>,
}

/// A type that holds the verifier key for `CompressedSNARK`
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PCDVerifierKey<G1, G2, C1, C2, S1, S2>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        C1: StepCircuit<G1::Scalar>,
        C2: StepCircuit<G2::Scalar>,
        S1: LinearCommittedCCSTrait<G1>,
        S2: RelaxedR1CSSNARKTrait<G2>,
{
    F_arity_primary: usize,
    F_arity_secondary: usize,
    ro_consts_primary: ROConstants<G1>,
    ro_consts_secondary: ROConstants<G2>,
    digest: G1::Scalar,
    vk_primary: S1::VerifierKey,
    vk_secondary: S2::VerifierKey,
    _p_c1: PhantomData<C1>,
    _p_c2: PhantomData<C2>,
}

/// A SNARK that proves the knowledge of a valid `RecursiveSNARK`
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PCDCompressedSNARK<G1, G2, C1, C2, S1, S2>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        C1: StepCircuit<G1::Scalar>,
        C2: StepCircuit<G2::Scalar>,
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
    zn_secondary: Vec<G2::Scalar>,

    _p_c1: PhantomData<C1>,
    _p_c2: PhantomData<C2>,
}

impl<G1, G2, C1, C2, S1, S2> PCDCompressedSNARK<G1, G2, C1, C2, S1, S2>
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
        C1: StepCircuit<G1::Scalar>,
        C2: StepCircuit<G2::Scalar>,
        S1: LinearCommittedCCSTrait<G1>,
        S2: RelaxedR1CSSNARKTrait<G2>,
{
    /// Creates prover and verifier keys for `CompressedSNARK`
    pub fn setup(
        pp: &PCDPublicParams<G1, G2, C1, C2>,
    ) -> Result<
        (
            PCDProverKey<G1, G2, C1, C2, S1, S2>,
            PCDVerifierKey<G1, G2, C1, C2, S1, S2>,
        ),
        NovaError,
    > {
        let (pk_primary, vk_primary) = S1::setup(&pp.ck_primary, &pp.ccs_primary)?;
        let (pk_secondary, vk_secondary) = S2::setup(&pp.ck_secondary, &pp.r1cs_shape_secondary)?;

        let pk = PCDProverKey {
            pk_primary,
            pk_secondary,
            _p_c1: Default::default(),
            _p_c2: Default::default(),
        };

        let vk = PCDVerifierKey {
            F_arity_primary: pp.F_arity_primary,
            F_arity_secondary: pp.F_arity_secondary,
            ro_consts_primary: pp.ro_consts_primary.clone(),
            ro_consts_secondary: pp.ro_consts_secondary.clone(),
            digest: pp.digest,
            vk_primary,
            vk_secondary,
            _p_c1: Default::default(),
            _p_c2: Default::default(),
        };

        Ok((pk, vk))
    }

    /// Create a new `CompressedSNARK`
    pub fn prove(
        pp: &PCDPublicParams<G1, G2, C1, C2>,
        pk: &PCDProverKey<G1, G2, C1, C2, S1, S2>,
        recursive_snark: &PCDRecursiveSNARK<G1, G2, C1, C2>,
    ) -> Result<Self, NovaError> {
        // Prover's transcript
        let mut transcript_p = <G1>::TE::new(Default::default(), b"multifolding");
        transcript_p.squeeze(b"init").unwrap();
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
            zn_secondary: recursive_snark.zi_secondary.clone(),

            _p_c1: Default::default(),
            _p_c2: Default::default(),
        })

    }



}