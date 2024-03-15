use std::ops::Add;
use std::sync::Arc;
use ff::Field;
use crate::{CE, Commitment, CommitmentKey};
use crate::errors::NovaError;

use crate::nimfs::ccs::ccs::{CCSError, CCS};
use crate::nimfs::ccs::util::compute_sum_Mz;

use crate::nimfs::espresso::virtual_polynomial::VirtualPolynomial;
use crate::nimfs::util::hypercube::BooleanHypercube;
use crate::nimfs::util::mle::matrix_to_mle;
use crate::nimfs::util::mle::vec_to_mle;
use crate::r1cs::R1CSShape;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::Group;

/// Witness for the LCCCS & CCCS, containing the w vector, and the r_w used as randomness in the Pedersen commitment.
#[derive(Debug, Clone)]
pub struct Witness<C: Group> {
    pub w: Vec<C::Scalar>,
    pub r_w: C::Scalar, // randomness used in the Pedersen commitment of w
}

impl<C: Group> Witness<C> {
    pub fn new(S: &R1CSShape<C>, W: &[C::Scalar]) -> Result<Self, NovaError> {
        if S.num_vars != W.len() {
            Err(NovaError::InvalidWitnessLength)
        } else {
            Ok(Self { w: W.to_owned(), r_w: Default::default() })
        }
    }

    pub fn commit(&self, ck: &CommitmentKey<C>) -> Commitment<C> {
        CE::<C>::commit(ck, &self.w)
    }
}

/// Committed CCS instance
#[derive(Debug, Clone)]
#[allow(clippy::upper_case_acronyms)]
pub struct CCCS<C: Group> {
    // Underlying CCS structure
    pub ccs: CCS<C>,

    // Commitment to witness
    pub C: Commitment<C>,
    // Public input/output
    pub x: Vec<C::Scalar>,
}

impl<C: Group> CCCS<C> {
    pub fn new(shape: &R1CSShape<C>, comm_C: Commitment<C>, X: &[C::Scalar]) -> Self {
        Self{
            ccs: shape.to_cccs(),
            C: comm_C,
            x: X.to_vec(),
        }
    }

    /// Computes q(x) = \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_q(&self, z: &Vec<C::Scalar>) -> VirtualPolynomial<C::Scalar> {
        let z_mle = vec_to_mle(self.ccs.s_prime, z);
        let mut q = VirtualPolynomial::<C::Scalar>::new(self.ccs.s);

        for i in 0..self.ccs.q {
            let mut prod: VirtualPolynomial<C::Scalar> =
                VirtualPolynomial::<C::Scalar>::new(self.ccs.s);
            for j in self.ccs.S[i].clone() {
                let M_j = matrix_to_mle(self.ccs.M[j].clone());

                let sum_Mz = compute_sum_Mz(M_j, &z_mle, self.ccs.s_prime);

                // Fold this sum into the running product
                if prod.products.is_empty() {
                    // If this is the first time we are adding something to this virtual polynomial, we need to
                    // explicitly add the products using add_mle_list()
                    // XXX is this true? improve API
                    prod.add_mle_list([Arc::new(sum_Mz)], C::Scalar::ONE)
                        .unwrap();
                } else {
                    prod.mul_by_mle(Arc::new(sum_Mz), C::Scalar::ONE)
                        .unwrap();
                }
            }
            // Multiply by the product by the coefficient c_i
            prod.scalar_mul(&self.ccs.c[i]);
            // Add it to the running sum
            q = q.add(&prod);
        }
        q
    }

    /// Computes Q(x) = eq(beta, x) * q(x)
    ///               = eq(beta, x) * \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_Q(
        &self,
        z: &Vec<C::Scalar>,
        beta: &[C::Scalar],
    ) -> VirtualPolynomial<C::Scalar> {
        let q = self.compute_q(z);
        q.build_f_hat(beta).unwrap()
    }

    /// Perform the check of the CCCS instance described at section 4.1
    pub fn check_relation(
        &self,
        ck: &CommitmentKey<C>,
        w: &Witness<C>,
    ) -> Result<(), CCSError> {
        // check that C is the commitment of w. Notice that this is not verifying a Pedersen
        // opening, but checking that the Commmitment comes from committing to the witness.
        assert_eq!(self.C, C::CE::commit(&ck, &w.w));

        // check CCCS relation
        let z: Vec<C::Scalar> =
            [vec![C::Scalar::ONE], self.x.clone(), w.w.to_vec()].concat();

        // A CCCS relation is satisfied if the q(x) multivariate polynomial evaluates to zero in the hypercube
        let q_x = self.compute_q(&z);
        for x in BooleanHypercube::new(self.ccs.s) {
            if bool::from(!q_x.evaluate(&x).unwrap().is_zero()) {
                return Err(CCSError::NotSatisfied);
            }
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod test {
    use rand_core::OsRng;
    use super::*;
    use crate::nimfs::ccs::ccs::test::{get_test_ccs, get_test_z};
    use crate::provider::bn256_grumpkin::bn256;

    /// Do some sanity checks on q(x). It's a multivariable polynomial and it should evaluate to zero inside the
    /// hypercube, but to not-zero outside the hypercube.
    #[test]
    fn test_compute_q() -> () {
        let ccs = get_test_ccs::<bn256::Point>();
        let z = get_test_z(3);

        let ck = ccs.commitment_key();
        let (cccs, _) = ccs.to_cccs(OsRng, &ck, &z);
        let q = cccs.compute_q(&z);

        // Evaluate inside the hypercube
        for x in BooleanHypercube::new(ccs.s).into_iter() {
            assert_eq!(bn256::Scalar::zero(), q.evaluate(&x).unwrap());
        }

        // Evaluate outside the hypercube
        let beta: Vec<bn256::Scalar> = (0..ccs.s).map(|_| bn256::Scalar::random(OsRng)).collect();
        assert_ne!(bn256::Scalar::zero(), q.evaluate(&beta).unwrap());
    }

    /// Perform some sanity checks on Q(x).
    #[test]
    fn test_compute_Q() -> () {
        let ccs = get_test_ccs::<bn256::Point>();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();

        let ck = ccs.commitment_key();
        let (cccs, _) = ccs.to_cccs(&mut OsRng, &ck, &z);

        let beta: Vec<bn256::Scalar> = (0..ccs.s).map(|_| bn256::Scalar::random(OsRng)).collect();

        // Compute Q(x) = eq(beta, x) * q(x).
        let Q = cccs.compute_Q(&z, &beta);

        // Let's consider the multilinear polynomial G(x) = \sum_{y \in {0, 1}^s} eq(x, y) q(y)
        // which interpolates the multivariate polynomial q(x) inside the hypercube.
        //
        // Observe that summing Q(x) inside the hypercube, directly computes G(\beta).
        //
        // Now, G(x) is multilinear and agrees with q(x) inside the hypercube. Since q(x) vanishes inside the
        // hypercube, this means that G(x) also vanishes in the hypercube. Since G(x) is multilinear and vanishes
        // inside the hypercube, this makes it the zero polynomial.
        //
        // Hence, evaluating G(x) at a random beta should give zero.

        // Now sum Q(x) evaluations in the hypercube and expect it to be 0
        let r = BooleanHypercube::new(ccs.s)
            .into_iter()
            .map(|x| Q.evaluate(&x).unwrap())
            .fold(bn256::Scalar::zero(), |acc, result| acc + result);
        assert_eq!(r, bn256::Scalar::zero());
    }

    /// The polynomial G(x) (see above) interpolates q(x) inside the hypercube.
    /// Summing Q(x) over the hypercube is equivalent to evaluating G(x) at some point.
    /// This test makes sure that G(x) agrees with q(x) inside the hypercube, but not outside
    #[test]
    fn test_Q_against_q() -> () {
        let ccs = get_test_ccs::<bn256::Point>();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();

        let ck = ccs.commitment_key();
        let (cccs, _) = ccs.to_cccs(&mut OsRng, &ck, &z);

        // Now test that if we create Q(x) with eq(d,y) where d is inside the hypercube, \sum Q(x) should be G(d) which
        // should be equal to q(d), since G(x) interpolates q(x) inside the hypercube
        let q = cccs.compute_q(&z);
        for d in BooleanHypercube::new(ccs.s) {
            let Q_at_d = cccs.compute_Q(&z, &d);

            // Get G(d) by summing over Q_d(x) over the hypercube
            let G_at_d = BooleanHypercube::new(ccs.s)
                .into_iter()
                .map(|x| Q_at_d.evaluate(&x).unwrap())
                .fold(bn256::Scalar::zero(), |acc, result| acc + result);
            assert_eq!(G_at_d, q.evaluate(&d).unwrap());
        }

        // Now test that they should disagree outside of the hypercube
        let r: Vec<bn256::Scalar> = (0..ccs.s).map(|_| bn256::Scalar::random(&mut OsRng)).collect();
        let Q_at_r = cccs.compute_Q(&z, &r);

        // Get G(d) by summing over Q_d(x) over the hypercube
        let G_at_r = BooleanHypercube::new(ccs.s)
            .into_iter()
            .map(|x| Q_at_r.evaluate(&x).unwrap())
            .fold(bn256::Scalar::zero(), |acc, result| acc + result);
        assert_ne!(G_at_r, q.evaluate(&r).unwrap());
    }
}
