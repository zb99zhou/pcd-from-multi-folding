#![warn(missing_debug_implementations)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

// use std::marker::PhantomData;
// use bellpepper_core::ConstraintSystem;
// use ff::Field;
// use serde::{Deserialize, Serialize};
// use crate::bellpepper::r1cs::{NovaShape, NovaWitness};
// use crate::bellpepper::shape_cs::ShapeCS;
// use crate::bellpepper::solver::SatisfyingAssignment;
// use crate::{CommitmentKey, compute_digest};
// use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
// use crate::errors::NovaError;
// use crate::gadgets::utils::scalar_as_base;
// use crate::nimfs::ccs::cccs::{CCCS, Witness};
// use crate::nimfs::ccs::lcccs::LCCCS;
// use crate::nimfs::multifolding::NIMFS;
// use crate::nimfs::pcd_circuit::{PCDUnitCircuit, PCDUnitInputs, PCDUnitParams};
// use crate::nimfs::pcd_proof::PCDProof;
// use crate::r1cs::R1CSShape;
// use crate::traits::circuit::StepCircuit;
// use crate::traits::{Group, ROConstants, ROConstantsCircuit, ROTrait};

pub mod ccs;
pub mod multifolding;
pub mod pcd_aux_circuit;
pub mod pcd_circuit;
pub mod pcd_proof;

pub mod espresso;
pub mod util;
//
// /// A type that holds public parameters of Nova
// #[derive(Serialize, Deserialize)]
// #[serde(bound = "")]
// pub struct PublicParams<G1, G2, C1, C2>
//     where
//         G1: Group<Base = <G2 as Group>::Scalar>,
//         G2: Group<Base = <G1 as Group>::Scalar>,
//         C1: StepCircuit<G1::Scalar>,
//         C2: StepCircuit<G2::Scalar>,
// {
//     F_arity_primary: usize,
//     F_arity_secondary: usize,
//     ro_consts_primary: ROConstants<G1>,
//     ro_consts_circuit_primary: ROConstantsCircuit<G2>,
//     ck_primary: CommitmentKey<G1>,
//     r1cs_shape_primary: R1CSShape<G1>,
//     ro_consts_secondary: ROConstants<G2>,
//     ro_consts_circuit_secondary: ROConstantsCircuit<G1>,
//     ck_secondary: CommitmentKey<G2>,
//     r1cs_shape_secondary: R1CSShape<G2>,
//     augmented_circuit_params_primary: PCDUnitParams,
//     augmented_circuit_params_secondary: PCDUnitParams,
//     digest: G1::Scalar, // digest of everything else with this field set to G1::Scalar::ZERO
//     _p_c1: PhantomData<C1>,
//     _p_c2: PhantomData<C2>,
// }
//
// impl<G1, G2, C1, C2> PublicParams<G1, G2, C1, C2>
//     where
//         G1: Group<Base = <G2 as Group>::Scalar>,
//         G2: Group<Base = <G1 as Group>::Scalar>,
//         C1: StepCircuit<G1::Scalar>,
//         C2: StepCircuit<G2::Scalar>,
// {
//     /// Create a new `PublicParams`
//     pub fn setup(c_primary: &C1, c_secondary: &C2, mu: usize, nu: usize) -> Self {
//         let pcd_circuit_params_primary =
//             PCDUnitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true, mu, nu);
//         let pcd_circuit_params_secondary = PCDUnitParams{ is_primary_circuit: false, ..pcd_circuit_params_primary };
//
//         let ro_consts_primary: ROConstants<G1> = ROConstants::<G1>::default();
//         let ro_consts_secondary: ROConstants<G2> = ROConstants::<G2>::default();
//
//         // ro_consts_circuit_primary are parameterized by G2 because the type alias uses G2::Base = G1::Scalar
//         let ro_consts_circuit_primary: ROConstantsCircuit<G2> = ROConstantsCircuit::<G2>::default();
//         let ro_consts_circuit_secondary: ROConstantsCircuit<G1> = ROConstantsCircuit::<G1>::default();
//
//         let F_arity_primary = c_primary.arity();
//         let F_arity_secondary = c_secondary.arity();
//
//         // Initialize ck for the primary
//         let circuit_primary: PCDUnitCircuit<'_, G2, C1> = PCDUnitCircuit::new(
//             &pcd_circuit_params_primary,
//             None,
//             c_primary,
//             ro_consts_circuit_primary.clone(),
//         );
//         let mut cs: ShapeCS<G1> = ShapeCS::new();
//         let _ = circuit_primary.synthesize(&mut cs);
//         let (r1cs_shape_primary, ck_primary) = cs.r1cs_shape();
//
//         // Initialize ck for the secondary
//         let circuit_secondary: PCDUnitCircuit<'_, G1, C2> = PCDUnitCircuit::new(
//             &pcd_circuit_params_secondary,
//             None,
//             c_secondary,
//             ro_consts_circuit_secondary.clone(),
//         );
//         let mut cs: ShapeCS<G2> = ShapeCS::new();
//         let _ = circuit_secondary.synthesize(&mut cs);
//         let (r1cs_shape_secondary, ck_secondary) = cs.r1cs_shape();
//
//         let mut pp = Self {
//             F_arity_primary,
//             F_arity_secondary,
//             ro_consts_primary,
//             ro_consts_secondary,
//             ck_primary,
//             ck_secondary,
//             ro_consts_circuit_primary,
//             ro_consts_circuit_secondary,
//             r1cs_shape_primary,
//             r1cs_shape_secondary,
//             augmented_circuit_params_primary: pcd_circuit_params_primary,
//             augmented_circuit_params_secondary: pcd_circuit_params_secondary,
//             digest: G1::Scalar::ZERO,
//             _p_c1: Default::default(),
//             _p_c2: Default::default(),
//         };
//
//         // set the digest in pp
//         pp.digest = compute_digest::<G1, PublicParams<G1, G2, C1, C2>>(&pp);
//
//         pp
//     }
//
//     /// Returns the number of constraints in the primary and secondary circuits
//     pub const fn num_constraints(&self) -> (usize, usize) {
//         (
//             self.r1cs_shape_primary.num_cons,
//             self.r1cs_shape_secondary.num_cons,
//         )
//     }
//
//     /// Returns the number of variables in the primary and secondary circuits
//     pub const fn num_variables(&self) -> (usize, usize) {
//         (
//             self.r1cs_shape_primary.num_vars,
//             self.r1cs_shape_secondary.num_vars,
//         )
//     }
// }
//
// /// A SNARK that proves the correct execution of an incremental computation
// #[derive(Clone, Debug, Serialize, Deserialize)]
// #[serde(bound = "")]
// pub struct PCDUnit<G1, G2, C1, C2>
//     where
//         G1: Group<Base = <G2 as Group>::Scalar>,
//         G2: Group<Base = <G1 as Group>::Scalar>,
//         C1: StepCircuit<G1::Scalar>,
//         C2: StepCircuit<G2::Scalar>,
// {
//     r_W_secondary: Vec<Witness<G2>>,
//     r_U_secondary: Vec<LCCCS<G2>>,
//     r_W_primary: Vec<Witness<G1>>,
//     r_U_primary: Vec<LCCCS<G1>>,
//     l_w_secondary: Vec<Witness<G2>>,
//     l_u_secondary: Vec<CCCS<G2>>,
//
//     zi_primary: Vec<G1::Scalar>,
//     zi_secondary: Vec<G2::Scalar>,
//     _p_c1: PhantomData<C1>,
//     _p_c2: PhantomData<C2>,
// }
//
//
// impl<G1, G2, C1, C2> PCDUnit<G1, G2, C1, C2>
//     where
//         G1: Group<Base = <G2 as Group>::Scalar>,
//         G2: Group<Base = <G1 as Group>::Scalar>,
//         C1: StepCircuit<G1::Scalar>,
//         C2: StepCircuit<G2::Scalar>,
// {
//     /// Create new instance of recursive SNARK
//     pub fn new(
//         pp: &PublicParams<G1, G2, C1, C2>,
//         c_primary: &C1,
//         c_secondary: &C2,
//         z0_primary: Vec<G1::Scalar>,
//         z0_secondary: Vec<G2::Scalar>,
//     ) -> Self {
//         // base case for the primary
//         let mut cs_primary: SatisfyingAssignment<G1> = SatisfyingAssignment::new();
//         let inputs_primary: PCDUnitInputs<G2> = PCDUnitInputs::new(
//             scalar_as_base::<G1>(pp.digest),
//             G1::Scalar::ZERO,
//             Some(z0_primary),
//             None,
//             None,
//         );
//
//         let circuit_primary: PCDUnitCircuit<'_, G2, C1> = PCDUnitCircuit::new(
//             &pp.augmented_circuit_params_primary,
//             Some(inputs_primary),
//             c_primary,
//             pp.ro_consts_circuit_primary.clone(),
//         );
//         let zi_primary = circuit_primary
//             .synthesize(&mut cs_primary)
//             .map_err(|_| NovaError::SynthesisError)
//             .expect("Nova error synthesis");
//         let (u_primary, w_primary) = cs_primary
//             .cccs_and_witness(&pp.r1cs_shape_primary, &pp.ck_primary)
//             .map_err(|_e| NovaError::UnSat)
//             .expect("Nova error unsat");
//
//         // base case for the secondary
//         let mut cs_secondary: SatisfyingAssignment<G2> = SatisfyingAssignment::new();
//         let inputs_secondary: PCDUnitInputs<G1> = PCDUnitInputs::new(
//             pp.digest,
//             G2::Scalar::ZERO,
//             Some(z0_secondary),
//             None,
//             None,
//         );
//         let circuit_secondary: PCDUnitCircuit<'_, G1, C2> = PCDUnitCircuit::new(
//             &pp.augmented_circuit_params_secondary,
//             Some(inputs_secondary),
//             c_secondary,
//             pp.ro_consts_circuit_secondary.clone(),
//         );
//         let zi_secondary = circuit_secondary
//             .synthesize(&mut cs_secondary)
//             .map_err(|_| NovaError::SynthesisError)
//             .expect("Nova error synthesis");
//         let (u_secondary, w_secondary) = cs_secondary
//             .cccs_and_witness(&pp.r1cs_shape_secondary, &pp.ck_secondary)
//             .map_err(|_e| NovaError::UnSat)
//             .expect("Nova error unsat");
//
//         // IVC proof for the primary circuit
//         let l_w_primary = w_primary;
//         let l_u_primary = u_primary;
//         let r_W_primary = Witness::new(&pp.r1cs_shape_primary, &l_w_primary.w)?;
//         let r_U_primary =
//             LCCCS::from_r1cs_instance(&pp.ck_primary, &pp.r1cs_shape_primary, &l_u_primary);
//
//         // IVC proof of the secondary circuit
//         let l_w_secondary = w_secondary;
//         let l_u_secondary = u_secondary;
//         let r_W_secondary = Witness::<G2>::default(&pp.r1cs_shape_secondary);
//         let r_U_secondary =
//             LCCCS::<G2>::default(&pp.ck_secondary, &pp.r1cs_shape_secondary);
//
//         if zi_primary.len() != pp.F_arity_primary || zi_secondary.len() != pp.F_arity_secondary {
//             panic!("Invalid step length");
//         }
//
//         let zi_primary = zi_primary
//             .iter()
//             .map(|v| v.get_value().ok_or(NovaError::SynthesisError))
//             .collect::<Result<Vec<<G1 as Group>::Scalar>, NovaError>>()
//             .expect("Nova error synthesis");
//
//         let zi_secondary = zi_secondary
//             .iter()
//             .map(|v| v.get_value().ok_or(NovaError::SynthesisError))
//             .collect::<Result<Vec<<G2 as Group>::Scalar>, NovaError>>()
//             .expect("Nova error synthesis");
//
//         Self {
//             r_W_primary,
//             r_U_primary,
//             r_W_secondary,
//             r_U_secondary,
//             l_w_secondary,
//             l_u_secondary,
//             zi_primary,
//             zi_secondary,
//             _p_c1: Default::default(),
//             _p_c2: Default::default(),
//         }
//     }
//
//     pub fn prove(
//         &mut self,
//         pp: &PublicParams<G1, G2, C1, C2>,
//         c_primary: &C1,
//         c_secondary: &C2,
//         z0_primary: Vec<G1::Scalar>,
//         z0_secondary: Vec<G2::Scalar>,
//     ) -> Result<PCDProof<G1, G2>, NovaError> {
//         if z0_primary.len() != pp.F_arity_primary || z0_secondary.len() != pp.F_arity_secondary {
//             return Err(NovaError::InvalidInitialInputLength);
//         }
//
//         // Frist step was already done in the constructor
//         if self.i == 0 {
//             self.i = 1;
//             return Ok(());
//         }
//
//         // primary logic
//         // fold the secondary circuit's instance
//         let (nifs_secondary, (r_U_secondary, r_W_secondary)) = NIMFS::prove(
//             &pp.ck_secondary,
//             &self.r_U_secondary,
//             &self.r_W_secondary,
//             &self.l_u_secondary,
//             &self.l_w_secondary,
//         )
//             .expect("Unable to fold secondary");
//         let mut cs_primary: SatisfyingAssignment<G1> = SatisfyingAssignment::new();
//         let inputs_primary: PCDUnitInputs<G2> = PCDUnitInputs::new(
//             scalar_as_base::<G1>(pp.digest),
//             z0_primary,
//             Some(self.zi_primary.clone()),
//             Some(self.r_U_secondary.clone()),
//             Some(self.l_u_secondary.clone()),
//         );
//         let circuit_primary: PCDUnitCircuit<'_, G2, C1> = PCDUnitCircuit::new(
//             &pp.augmented_circuit_params_primary,
//             Some(inputs_primary),
//             c_primary,
//             pp.ro_consts_circuit_primary.clone(),
//         );
//         let zi_primary = circuit_primary
//             .synthesize(&mut cs_primary)
//             .map_err(|_| NovaError::SynthesisError)?;
//         let (l_u_primary, l_w_primary) = cs_primary
//             .cccs_and_witness(&pp.r1cs_shape_primary, &pp.ck_primary)
//             .map_err(|_e| NovaError::UnSat)
//             .expect("Nova error unsat");
//
//         // second logic
//         // fold the primary circuit's instance
//         let (nifs_primary, (r_U_primary, r_W_primary)) = NIMFS::prove(
//             &pp.ck_primary,
//             &self.r_U_primary,
//             &l_u_primary,
//             &self.r_W_primary,
//             &l_w_primary,
//         )
//             .expect("Unable to fold primary");
//         let mut cs_secondary: SatisfyingAssignment<G2> = SatisfyingAssignment::new();
//         let inputs_secondary: PCDUnitInputs<G1> = PCDUnitInputs::new(
//             pp.digest,
//             z0_secondary,
//             Some(self.zi_secondary.clone()),
//             Some(self.r_U_primary.clone()),
//             Some(vec![l_u_primary]),
//         );
//         let circuit_secondary: PCDUnitCircuit<'_, G1, C2> = PCDUnitCircuit::new(
//             &pp.augmented_circuit_params_secondary,
//             Some(inputs_secondary),
//             c_secondary,
//             pp.ro_consts_circuit_secondary.clone(),
//         );
//         let zi_secondary = circuit_secondary
//             .synthesize(&mut cs_secondary)
//             .map_err(|_| NovaError::SynthesisError)?;
//         let (l_u_secondary, l_w_secondary) = cs_secondary
//             .cccs_and_witness(&pp.r1cs_shape_secondary, &pp.ck_secondary)
//             .map_err(|_e| NovaError::UnSat)?;
//
//         // update the running instances and witnesses
//         let zi_primary = zi_primary
//             .iter()
//             .map(|v| v.get_value().ok_or(NovaError::SynthesisError))
//             .collect::<Result<Vec<<G1 as Group>::Scalar>, NovaError>>()?;
//         let zi_secondary = zi_secondary
//             .iter()
//             .map(|v| v.get_value().ok_or(NovaError::SynthesisError))
//             .collect::<Result<Vec<<G2 as Group>::Scalar>, NovaError>>()?;
//
//         Ok(PCDProof{
//             r_W_secondary,
//             r_U_secondary,
//             r_W_primary,
//             r_U_primary,
//             l_w_secondary,
//             l_u_secondary,
//             zi_primary,
//             zi_secondary,
//         })
//     }
//
//     /// Verify the correctness of the `RecursiveSNARK`
//     pub fn verify(
//         &self,
//         pp: &PublicParams<G1, G2, C1, C2>,
//         num_steps: usize,
//         z0_primary: &[G1::Scalar],
//         z0_secondary: &[G2::Scalar],
//     ) -> Result<(Vec<G1::Scalar>, Vec<G2::Scalar>), NovaError> {
//         // number of steps cannot be zero
//         if num_steps == 0 {
//             return Err(NovaError::ProofVerifyError);
//         }
//
//         // check if the provided proof has executed num_steps
//         if self.i != num_steps {
//             return Err(NovaError::ProofVerifyError);
//         }
//
//         // check if the (relaxed) R1CS instances have two public outputs
//         if self.l_u_secondary.X.len() != 2
//             || self.r_U_primary.X.len() != 2
//             || self.r_U_secondary.X.len() != 2
//         {
//             return Err(NovaError::ProofVerifyError);
//         }
//
//         // check if the output hashes in R1CS instances point to the right running instances
//         let (hash_primary, hash_secondary) = {
//             let mut hasher = <G2 as Group>::RO::new(
//                 pp.ro_consts_secondary.clone(),
//                 NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_primary,
//             );
//             hasher.absorb(pp.digest);
//             hasher.absorb(G1::Scalar::from(num_steps as u64));
//             for e in z0_primary {
//                 hasher.absorb(*e);
//             }
//             for e in &self.zi_primary {
//                 hasher.absorb(*e);
//             }
//             self.r_U_secondary.absorb_in_ro(&mut hasher);
//
//             let mut hasher2 = <G1 as Group>::RO::new(
//                 pp.ro_consts_primary.clone(),
//                 NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_secondary,
//             );
//             hasher2.absorb(scalar_as_base::<G1>(pp.digest));
//             hasher2.absorb(G2::Scalar::from(num_steps as u64));
//             for e in z0_secondary {
//                 hasher2.absorb(*e);
//             }
//             for e in &self.zi_secondary {
//                 hasher2.absorb(*e);
//             }
//             self.r_U_primary.absorb_in_ro(&mut hasher2);
//
//             (
//                 hasher.squeeze(NUM_HASH_BITS),
//                 hasher2.squeeze(NUM_HASH_BITS),
//             )
//         };
//
//         if hash_primary != self.l_u_secondary.X[0]
//             || hash_secondary != scalar_as_base::<G2>(self.l_u_secondary.X[1])
//         {
//             return Err(NovaError::ProofVerifyError);
//         }
//
//         // check the satisfiability of the provided instances
//         let (res_r_primary, (res_r_secondary, res_l_secondary)) = rayon::join(
//             || {
//                 pp.r1cs_shape_primary
//                     .is_sat_relaxed(&pp.ck_primary, &self.r_U_primary, &self.r_W_primary)
//             },
//             || {
//                 rayon::join(
//                     || {
//                         pp.r1cs_shape_secondary.is_sat_relaxed(
//                             &pp.ck_secondary,
//                             &self.r_U_secondary,
//                             &self.r_W_secondary,
//                         )
//                     },
//                     || {
//                         pp.r1cs_shape_secondary.is_sat(
//                             &pp.ck_secondary,
//                             &self.l_u_secondary,
//                             &self.l_w_secondary,
//                         )
//                     },
//                 )
//             },
//         );
//
//         // check the returned res objects
//         res_r_primary?;
//         res_r_secondary?;
//         res_l_secondary?;
//
//         Ok((self.zi_primary.clone(), self.zi_secondary.clone()))
//     }
// }
