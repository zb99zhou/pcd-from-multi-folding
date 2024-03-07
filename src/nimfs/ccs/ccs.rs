use std::ops::Neg;
use ff::{Field, PrimeField};
use rand_core::RngCore;
// XXX use thiserror everywhere? espresso doesnt use it...
use thiserror::Error;
use crate::CommitmentKey;
use crate::nimfs::ccs::cccs::{CCCS, Witness};
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::nimfs::ccs::util::compute_all_sum_Mz_evals;
use crate::nimfs::util::vec::{hadamard, Matrix};

use crate::nimfs::util::vec::*;
use crate::r1cs::R1CSShape;
use crate::spartan::math::Math;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::Group;

#[derive(Error, Debug)]
pub enum CCSError {
    #[error("Relation not satisfied")]
    NotSatisfied,
}

/// A CCS structure
#[derive(Debug, Clone, Eq, PartialEq)]
#[allow(clippy::upper_case_acronyms)]
pub struct CCS<G: Group> {
    // m: number of columns in M_i (such that M_i \in F^{m, n})
    pub m: usize,
    // n = |z|, number of rows in M_i
    pub n: usize,
    // l = |io|, size of public input/output
    pub l: usize,
    // t = |M|, number of matrices
    pub t: usize,
    // q = |c| = |S|, number of multisets
    pub q: usize,
    // d: max degree in each variable
    pub d: usize,
    // s = log(m), dimension of x
    pub s: usize,
    // s_prime = log(n), dimension of y
    pub s_prime: usize,

    // Vector of matrices
    pub M: Vec<Matrix<G::Scalar>>,
    // Vector of multisets
    pub S: Vec<Vec<usize>>,
    // Vector of coefficients
    pub c: Vec<G::Scalar>,
}

impl<G: Group> From<R1CSShape<G>> for CCS<G> {
    fn from(value: R1CSShape<G>) -> Self {
        let mut A = vec![vec![G::Scalar::default(); value.num_vars]; value.num_cons];
        let mut B = A.clone();
        let mut C = A.clone();
        matrix_type_convert(&mut A, value.A);
        matrix_type_convert(&mut B, value.B);
        matrix_type_convert(&mut C, value.C);
        CCS::from_r1cs(A, B, C, value.num_io)
    }
}

fn matrix_type_convert<F: PrimeField>(target_matrix: &mut [Vec<F>], absorbed_matrix: Vec<(usize, usize, F)>) {
    absorbed_matrix
        .into_iter()
        .for_each(|(row, col, coff)| target_matrix[row][col] = coff );
}

impl<G: Group> CCS<G> {
    /// Converts the R1CS structure to the CCS structure
    fn from_plonk_gate(
        _q_l: Vec<G::Scalar>,
        _q_r: Vec<G::Scalar>,
        _q_m: Vec<G::Scalar>,
        _q_c: Vec<G::Scalar>,
        _q_o: Vec<G::Scalar>,
    ) -> CCS<G> {
        todo!()
    }

    /// Converts the R1CS structure to the CCS structure
    fn from_r1cs(
        A: Vec<Vec<G::Scalar>>,
        B: Vec<Vec<G::Scalar>>,
        C: Vec<Vec<G::Scalar>>,
        io_len: usize,
    ) -> CCS<G> {
        let m = A.len();
        let n = A[0].len();
        CCS {
            m,
            n,
            l: io_len,
            s: m.log_2(),
            s_prime: n.log_2(),
            t: 3,
            q: 2,
            d: 2,

            S: vec![vec![0, 1], vec![2]],
            c: vec![G::Scalar::ONE, G::Scalar::ONE.neg()],
            M: vec![A, B, C],
        }
    }

    /// Samples public parameters for the specified number of constraints and variables in an R1CS
    pub fn commitment_key(&self) -> CommitmentKey<G> {
        G::CE::setup(b"ck", self.n - self.l - 1)
    }

    /// Compute v_j values of the linearized committed CCS form
    /// Given `r`, compute:  \sum_{y \in {0,1}^s'} M_j(r, y) * z(y)
    fn compute_v_j(&self, z: &[G::Scalar], r: &[G::Scalar]) -> Vec<G::Scalar> {
        compute_all_sum_Mz_evals(&self.M, &z.to_vec(), r, self.s_prime)
    }

    pub fn to_cccs(
        &self,
        rng: impl RngCore,
        ck: &<<G as Group>::CE as CommitmentEngineTrait<G>>::CommitmentKey,
        z: &[G::Scalar],
    ) -> (CCCS<G>, Witness<G>) {
        let w: Vec<G::Scalar> = z[(1 + self.l)..].to_vec();
        let r_w = G::Scalar::random(rng);
        let C = G::CE::commit(ck, &w);

        (
            CCCS::<G> {
                ccs: self.clone(),
                C,
                x: z[1..(1 + self.l)].to_vec(),
            },
            Witness::<G> { w, r_w },
        )
    }

    pub fn to_lcccs(
        &self,
        rng: impl RngCore + Clone,
        ck: &<<G as Group>::CE as CommitmentEngineTrait<G>>::CommitmentKey,
        z: &[G::Scalar],
    ) -> (LCCCS<G>, Witness<G>) {
        let w: Vec<G::Scalar> = z[(1 + self.l)..].to_vec();
        let r_w = G::Scalar::random(rng.clone());
        let C = G::CE::commit(ck, &w);

        let r_x: Vec<G::Scalar> = (0..self.s).map(|_| G::Scalar::random(rng.clone())).collect();
        let v = self.compute_v_j(z, &r_x);

        (
            LCCCS::<G> {
                ccs: self.clone(),
                C,
                u: G::Scalar::ONE,
                x: z[1..(1 + self.l)].to_vec(),
                r_x,
                v,
            },
            Witness::<G> { w, r_w },
        )
    }

    /// Check that a CCS structure is satisfied by a z vector.
    /// This works with matrices. It doesn't do any polynomial stuff
    /// Only for testing
    pub fn check_relation(&self, z: &[G::Scalar]) -> Result<(), CCSError> {
        let mut result = vec![G::Scalar::default(); self.m];

        for i in 0..self.q {
            // XXX This can be done more neatly with a .fold() or .reduce()

            // Extract the needed M_j matrices out of S_i
            let vec_M_j: Vec<&Matrix<G::Scalar>> =
                self.S[i].iter().map(|j| &self.M[*j]).collect();

            // Complete the hadamard chain
            let mut hadamard_result = vec![G::Scalar::ONE; self.m];
            for M_j in vec_M_j.into_iter() {
                hadamard_result = hadamard(&hadamard_result, &mat_vec_mul(M_j, z));
            }

            // Multiply by the coefficient of this step
            let c_M_j_z = vec_scalar_mul(&hadamard_result, &self.c[i]);

            // Add it to the final vector
            result = vec_add(&result, &c_M_j_z);
        }

        // Make sure the final vector is all zeroes
        for e in result {
            if !bool::from(e.is_zero()) {
                return Err(CCSError::NotSatisfied);
            }
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use ff::PrimeField;

    /// Return a CCS circuit that implements the Vitalik `x^3 + x + 5 == 35` (from
    /// https://www.vitalik.ca/general/2016/12/10/qap.html )
    #[cfg(test)]
    pub fn get_test_ccs<C: Group>() -> CCS<C> {
        let A = to_F_matrix(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ]);
        let B = to_F_matrix(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 1, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
        ]);
        let C = to_F_matrix(vec![
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 0, 0, 0, 1, 0],
            vec![0, 0, 0, 0, 0, 1],
            vec![0, 0, 1, 0, 0, 0],
        ]);
        CCS::from_r1cs(A, B, C, 1)
    }

    /// Computes the z vector for the given input for Vitalik's equation.
    #[cfg(test)]
    pub fn get_test_z<F: PrimeField>(input: usize) -> Vec<F> {
        // z = (1, io, w)
        to_F_vec(vec![
            1,
            input,
            input * input * input + input + 5, // x^3 + x + 5
            input * input,                     // x^2
            input * input * input,             // x^2 * x
            input * input * input + input,     // x^3 + x
        ])
    }

    /// Test that a basic CCS relation can be satisfied
    #[test]
    fn test_ccs_relation() -> () {
        use crate::provider::bn256_grumpkin::{bn256};
        let ccs = get_test_ccs::<bn256::Point>();
        let z = get_test_z(3);

        ccs.check_relation(&z).unwrap();
    }
}
