use std::sync::Arc;
use ff::{Field, PrimeField};
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
        let r_x_str: [&str; 16] = [
            "123099097812162924252574344975106523238194576887769348556133193553988715163",
            "11878155068933055855312424733128512397613400312288183916124113580707242320063",
            "2267722080938451033780054253087042665725616562614405633406347840968279627225",
            "3063753072503960862044867802283246711194951703706115318190024353382787130314",
            "7553189234872085222544981791798744641767683705978800464101652357368434003856",
            "4524669830493917136649682499844643802765698600180308516153000579970915972561",
            "19563294952183620956608650809458123224689996119994554673300657079214511020133",
            "14430512527801278252700229949687551144457338634070952660178593276051625368060",
            "21287154070142845842726489099589329858589245328469526905050369907899369469371",
            "2669737580077745634268723563456414459861412472230466449705655169710154219993",
            "28026337028736864231864245008915240245032605523389536787064205764312108793368",
            "21078224377386554496491747869854810944210877165726078025537776887895999807647",
            "6115196982769614063713488458804511566010181831476907123011305255229099255610",
            "9290240867128456535318774037441176979119094564235777528330239632398315102170",
            "21880678862954084384131999977334312747306413328820305284210356060976805353704",
            "6869893432526726205738711268587617385295655184265967576308027745971141086996",
        ];

        let mut r_x  = Vec::<G::Scalar>::new();
        for rx in r_x_str {
            r_x.push(G::Scalar::from_str_vartime(rx).unwrap());
        }

        let v_str: [&str; 3] = [
            "21859528063586540854410367835509869025165279196780495520647131653360260467066",
            "11362276090930735933958919899320318668221342439153808504686055742486843831784",
            "814121523763012577558542474346865927798520462225996448593364948903561276011",
        ];

        let mut v = Vec::<G::Scalar>::new();
        for v1 in v_str {
            v.push(G::Scalar::from_str_vartime(v1).unwrap());
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
