use std::sync::Arc;
use ff::{Field, PrimeField};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use crate::Commitment;

use crate::nimfs::ccs::cccs::CCSWitness;
use crate::nimfs::ccs::ccs::{CCSError, CCS};

use crate::nimfs::espresso::virtual_polynomial::VirtualPolynomial;
use crate::nimfs::util::mle::vec_to_mle;
use crate::spartan::math::Math;
use crate::traits::commitment::{CommitmentEngineTrait, CommitmentTrait};
use crate::traits::{AbsorbInROTrait, Group, ROTrait, TranscriptReprTrait};

/// Linearized Committed CCS instance
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
#[serde(bound = "")]
#[allow(clippy::upper_case_acronyms)]
pub struct LCCCS<C: Group> {
    // Underlying CCS structure
    pub ccs: CCS<C>,

    // TODO: Further improve the abstractions here. We should not need so many public fields

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
        let r_x_str: [&str; 17] = [
            "39cc5b1930812dc5eb2cdbc646e2aca2c36bb3d5f2ab1580b2ba9eaa3b2c5b5c",
            "216e84b939f654a8b09cb4388dd9b3ef6c3a12e374e7ca16df5aac4ffd4a055f",
            "15a34c90dd10255b7b438820d1d8be037c63adf847b7612d4dd4e7d04fc9a93d",
            "20831a34b34459213c3228e01929552f3b82bcef701677c6a27a612995657d2f",
            "39abaf9d74628ca439360850251ab75355bd979d1df0e6b0af9e9513fc3d7f08",
            "2f0340c1c19e8f2206f182898574e380f4fa1807a06139580db4f927fb5ae352",
            "369a0f61ed980ee50904750692a0a9c39a4d8a0df00c223997a931ebd37a73f8",
            "3410ab28a375ed0bbd11a42acce970f30a80be126d612660458cc6b219c4ec35",
            "1fe2474fe3c5ba0f4119629818bd2feb1a0b6348116e716a8557fa81099399ee",
            "170e83fd7d3ccecf9d1e9e250e1c353e8dd3553c0a16916f9dddef7a1bbd1f44",
            "2758fdca830c57b54aad951bf0e663522375968a4f9fe2a1e44b1afd9bc40732",
            "1c40b9762b82200e03d41023195539a92a59e47f69e0c886c994f451b07a2ba4",
            "1d344fee00fbb17111e587bb2127f0641c4ef254d63fa600796ad6ff3c58403b",
            "368f9eaa1754fc51f571eb85fbc983236e4be4b90080e94c14db7b2f794d0a1a",
            "37ff779bffeb9b6f115ccbff9a0e93df8fad1a6ad3ac33fc67e8a22da9d7c20c",
            "1c8852e4fde28c7ce5cddc3fddb019dbfe3d6242df8e62e64e17559817b3dc3b",
            "0a63ba620ee1db1282d2dcbec1fe4b32a43469b9d74588de2d02334080b999d1",
        ];

        let mut r_x  = Vec::<G::Scalar>::new();
        for rx in r_x_str {
            let decimal = BigUint::parse_bytes(rx.as_bytes(), 16).unwrap();
            r_x.push(G::Scalar::from_str_vartime(&decimal.to_string()).unwrap());
        }

        let v_str: [&str; 3] = [
            "01e32ef81003deb8cf31c2d4890f0ecd0d4c296ebf51b271229f8dca646c7fa5",
            "12c78d51983fb97d285986fdc866bc18c41a35655b73b8693f00a529360056bd",
            "3b0be5716ba461bc0c4a12f238786c3c816755a0ae8d95ba7cdedf502332ff75",
        ];

        let mut v = Vec::<G::Scalar>::new();
        for v1 in v_str {
            let decimal = BigUint::parse_bytes(v1.as_bytes(), 16).unwrap();
            v.push(G::Scalar::from_str_vartime(&decimal.to_string()).unwrap());
        }
         Self {
            C: Commitment::<G>::default(),
            u: G::Scalar::ONE,
            x: vec![G::Scalar::ZERO],
            r_x,
            v,
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
}

impl<C: Group> LCCCS<C> {
    /// Compute all L_j(x) polynomials
    pub fn compute_Ls(&self, z: &Vec<C::Scalar>) -> Vec<VirtualPolynomial<C::Scalar>> {
        let mut vec_L_j_x = Vec::with_capacity(self.ccs.t);
        for M_j in self.ccs.M.iter() {
            let Mz = M_j.multiply_vec(z);
            let sum_Mz = vec_to_mle(Mz.len().log_2(), &Mz);
            let sum_Mz_virtual =
                VirtualPolynomial::new_from_mle(&Arc::new(sum_Mz.clone()), C::Scalar::ONE);
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

        // check CCS relation
        let z: Vec<C::Scalar> = [w.w.to_vec(),vec![self.u], self.x.clone()].concat();
        let computed_v = self.ccs.compute_v_j(&z, &self.r_x);
        assert_eq!(computed_v, self.v);
        Ok(())
    }
}

impl<G1> LCCCS<G1>
where
    G1: Group,
{
    pub fn absorb_in_ro<G2: Group<Base = <G1 as Group>::Scalar>>(
        &self,
        ro: &mut G2::RO,
    ) {
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
    fn test_lcccs_v_j() -> () {
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
                .into_iter()
                .map(|y| L_j_x.evaluate(&y).unwrap())
                .fold(bn256::Scalar::zero(), |acc, result| acc + result);
            assert_eq!(v_i, sum_L_j_x);
        }
    }

    /// Given a bad z, check that the v_j should not match with the L_j(x)
    #[test]
    fn test_bad_v_j() -> () {
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
                .into_iter()
                .map(|y| L_j_x.evaluate(&y).unwrap())
                .fold(bn256::Scalar::zero(), |acc, result| acc + result);
            if v_i != sum_L_j_x {
                satisfied = false;
            }
        }

        assert_eq!(satisfied, false);
    }
}
