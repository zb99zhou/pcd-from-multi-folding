use crate::Commitment;
use ff::Field;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::nimfs::ccs::cccs::CCSWitness;
use crate::nimfs::ccs::ccs::{CCSError, CCS};

use crate::compress_snark::math::Math;
use crate::nimfs::espresso::virtual_polynomial::VirtualPolynomial;
use crate::nimfs::util::mle::vec_to_mle;
use crate::traits::commitment::{CommitmentEngineTrait, CommitmentTrait};
use crate::traits::{AbsorbInROTrait, Group, ROTrait, TranscriptReprTrait};

/// Linearized Committed CCS instance
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
#[serde(bound = "")]
#[allow(clippy::upper_case_acronyms)]
pub struct LCCCS<C: Group> {
  // Underlying CCS structure
  pub ccs: CCS<C>,

  // Commitment to witness
  pub C: Commitment<C>,
  // Relaxation factor of z for folded LCCCS
  pub u: C::Scalar,
  // Public input/output
  pub x: Vec<C::Scalar>,
  // Random evaluation point for the v_i
  pub r_x: Vec<C::Scalar>,
  // Vector of v_i
  pub v: Vec<C::Scalar>,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
#[serde(bound = "")]
#[allow(clippy::upper_case_acronyms)]
pub struct LCCCSForBase<C: Group> {
  // Commitment to witness
  pub C: (C::Scalar, C::Scalar, bool),
  // Relaxation factor of z for folded LCCCS
  pub u: C::Base,
  // Public input/output
  pub x: Vec<C::Base>,
  // Random evaluation point for the v_i
  pub r_x: Vec<C::Base>,
  // Vector of v_i
  pub v: Vec<C::Base>,
}

impl<G1, G2> From<LCCCS<G1>> for LCCCSForBase<G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  fn from(value: LCCCS<G1>) -> Self {
    Self {
      C: value.C.to_coordinates(),
      u: value.u,
      x: value.x,
      r_x: value.r_x,
      v: value.v,
    }
  }
}

impl<G: Group> LCCCS<G> {
  pub fn default_for_pcd(ccs: CCS<G>) -> Self {
    Self {
      C: Commitment::<G>::default(),
      u: G::Scalar::ZERO,
      x: vec![G::Scalar::ZERO],
      r_x: vec![G::Scalar::ZERO; ccs.s],
      v: vec![G::Scalar::ZERO; 3],
      ccs,
    }
  }
}

impl<C: Group> TranscriptReprTrait<C> for LCCCS<C> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    [
      self.C.to_transcript_bytes(),
      self.u.to_transcript_bytes(),
      self.x.as_slice().to_transcript_bytes(),
      self.r_x.as_slice().to_transcript_bytes(),
      self.v.as_slice().to_transcript_bytes(),
    ]
    .concat()
  }

  fn to_transcript_scalars(&self) -> Vec<C::Scalar> {
    [
      self.C.to_transcript_scalars(),
      self.u.to_transcript_scalars(),
      self.x.as_slice().to_transcript_scalars(),
      self.r_x.as_slice().to_transcript_scalars(),
      self.v.as_slice().to_transcript_scalars(),
    ]
    .concat()
  }
}

impl<C: Group> LCCCS<C> {
  /// Compute all L_j(x) polynomials
  pub fn compute_Ls(&self, z: &[C::Scalar]) -> Vec<VirtualPolynomial<C::Scalar>> {
    let mut vec_L_j_x = Vec::with_capacity(self.ccs.t);
    for M_j in self.ccs.M.iter() {
      let Mz = M_j.multiply_vec(z);
      let sum_Mz = vec_to_mle(Mz.len().log_2(), &Mz);
      let sum_Mz_virtual = VirtualPolynomial::new_from_mle(&Arc::new(sum_Mz), C::Scalar::ONE);
      let L_j_x = sum_Mz_virtual.build_f_hat(&self.r_x).unwrap();
      vec_L_j_x.push(L_j_x);
    }

    vec_L_j_x
  }

  /// Perform the check of the LCCCS instance described at section 4.2
  pub fn check_relation(
    &self,
    ck: &<<C as Group>::CE as CommitmentEngineTrait<C>>::CommitmentKey,
    w: &CCSWitness<C>,
  ) -> Result<(), CCSError> {
    // check that C is the commitment of w. Notice that this is not verifying a Pedersen
    // opening, but checking that the Commmitment comes from committing to the witness.
    assert_eq!(self.C, C::CE::commit(ck, &w.w));

    // check LCCS relation
    let z: Vec<C::Scalar> = [w.w.to_vec(), vec![self.u], self.x.clone()].concat();
    let computed_v = self.ccs.compute_v_j(&z, &self.r_x);
    assert_eq!(computed_v, self.v);
    Ok(())
  }
}

impl<G1> LCCCS<G1>
where
  G1: Group,
{
  pub fn absorb_in_ro<G2: Group<Base = <G1 as Group>::Scalar>>(&self, ro: &mut G2::RO) {
    self.C.absorb_in_g2_ro::<G2>(ro);
    ro.absorb(self.u);

    for x in &self.x {
      ro.absorb(*x);
    }
    for v in self.v.iter() {
      ro.absorb(*v);
    }

    for r in self.r_x.iter() {
      ro.absorb(*r);
    }
  }
}

#[cfg(test)]
pub mod test {
  use rand_core::OsRng;

  use crate::nimfs::ccs::ccs::test::{get_test_ccs, get_test_z};
  use crate::nimfs::util::hypercube::BooleanHypercube;
  use crate::provider::bn256_grumpkin::bn256;

  #[test]
  /// Test linearized CCCS v_j against the L_j(x)
  fn test_lcccs_v_j() {
    let ccs = get_test_ccs::<bn256::Point>();
    let z = get_test_z(3);
    ccs.check_relation(&z.clone()).unwrap();

    let ck = ccs.commitment_key();
    let (lcccs, _) = ccs.to_lcccs(OsRng, &ck, &z);
    // with our test vector comming from R1CS, v should have length 3
    assert_eq!(lcccs.v.len(), 3);

    let vec_L_j_x = lcccs.compute_Ls(&z);
    assert_eq!(vec_L_j_x.len(), lcccs.v.len());

    for (v_i, L_j_x) in lcccs.v.into_iter().zip(vec_L_j_x) {
      let sum_L_j_x = BooleanHypercube::new(ccs.s)
        .map(|y| L_j_x.evaluate(&y).unwrap())
        .fold(bn256::Scalar::zero(), |acc, result| acc + result);
      assert_eq!(v_i, sum_L_j_x);
    }
  }

  /// Given a bad z, check that the v_j should not match with the L_j(x)
  #[test]
  fn test_bad_v_j() {
    let ccs = get_test_ccs::<bn256::Point>();
    let z = get_test_z(3);
    ccs.check_relation(&z.clone()).unwrap();

    // Mutate z so that the relation does not hold
    let mut bad_z = z.clone();
    bad_z[3] = bn256::Scalar::zero();
    assert!(ccs.check_relation(&bad_z.clone()).is_err());

    let ck = ccs.commitment_key();
    // Compute v_j with the right z
    let (lcccs, _) = ccs.to_lcccs(OsRng, &ck, &z);
    // with our test vector comming from R1CS, v should have length 3
    assert_eq!(lcccs.v.len(), 3);

    // Bad compute L_j(x) with the bad z
    let vec_L_j_x = lcccs.compute_Ls(&bad_z);
    assert_eq!(vec_L_j_x.len(), lcccs.v.len());

    // Make sure that the LCCCS is not satisfied given these L_j(x)
    // i.e. summing L_j(x) over the hypercube should not give v_j for all j
    let mut satisfied = true;
    for (v_i, L_j_x) in lcccs.v.into_iter().zip(vec_L_j_x) {
      let sum_L_j_x = BooleanHypercube::new(ccs.s)
        .map(|y| L_j_x.evaluate(&y).unwrap())
        .fold(bn256::Scalar::zero(), |acc, result| acc + result);
      if v_i != sum_L_j_x {
        satisfied = false;
      }
    }

    assert!(!satisfied);
  }
}
