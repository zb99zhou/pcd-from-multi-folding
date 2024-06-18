/// Some basic MLE utilities
use crate::compress_snark::math::Math;
use crate::compress_snark::polys::multilinear::MultiLinearPolynomial;
use crate::nimfs::util::spare_matrix::SparseMatrix;
use ff::PrimeField;

use super::vec::Matrix;

/// Pad matrix so that its columns and rows are powers of two
fn pad_matrix<F: PrimeField>(matrix: &Matrix<F>) -> Matrix<F> {
  // Find the desired dimensions after padding
  let rows = matrix.len();
  let cols = matrix[0].len();
  let padded_rows = rows.next_power_of_two();
  let padded_cols = cols.next_power_of_two();

  // Create a new padded matrix
  // XXX inefficient. take a mutable matrix as input instead?
  let mut padded_matrix = vec![vec![F::default(); padded_cols]; padded_rows];

  // Copy values from the input matrix to the padded matrix
  for (i, row) in matrix.iter().enumerate() {
    for (j, &value) in row.iter().enumerate() {
      padded_matrix[i][j] = value;
    }
  }

  padded_matrix
}

// XXX shouldn't consume the matrix
pub fn matrix_to_mle<F: PrimeField>(matrix: &SparseMatrix<F>) -> MultiLinearPolynomial<F> {
  let n_vars = matrix.cols.log_2() + matrix.rows.log_2(); // n_vars = s + s'

  // TODO(optimize): init with flatten M
  let mut M_evals =
    vec![vec![F::default(); matrix.cols.next_power_of_two()]; matrix.rows.next_power_of_two()];
  matrix
    .iter()
    .for_each(|(row, col, val)| M_evals[row][col] = val);

  vec_to_mle(n_vars, &M_evals.into_iter().flatten().collect::<Vec<_>>())
}

pub fn vec_to_mle<F: PrimeField>(n_vars: usize, v: &[F]) -> MultiLinearPolynomial<F> {
  // Pad to 2^n_vars
  let mut v_padded = v.to_vec();
  v_padded.resize(1 << n_vars, F::default());
  MultiLinearPolynomial {
    Z: v_padded,
    num_vars: n_vars,
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::nimfs::{
    ccs::ccs::test::get_test_z,
    util::{hypercube::BooleanHypercube, vec::to_F_matrix},
  };
  use halo2curves::bn256::Fr;

  fn test_matrix() -> Vec<Vec<Fr>> {
    to_F_matrix::<Fr>(vec![
      vec![2, 3, 4, 4],
      vec![4, 11, 14, 14],
      vec![2, 8, 17, 17],
      vec![420, 4, 2, 0],
    ])
  }

  #[test]
  fn test_matrix_to_mle() {
    let A = test_matrix();

    let A_mle = matrix_to_mle(&(&A).into());
    assert_eq!(A_mle.Z.len(), 16); // 4x4 matrix, thus 2bit x 2bit, thus 2^4=16 evals

    let A = to_F_matrix::<Fr>(vec![
      vec![2, 3, 4, 4, 1],
      vec![4, 11, 14, 14, 2],
      vec![2, 8, 17, 17, 3],
      vec![420, 4, 2, 0, 4],
      vec![420, 4, 2, 0, 5],
    ]);
    let A_mle = matrix_to_mle(&(&A).into());
    assert_eq!(A_mle.Z.len(), 64); // 5x5 matrix, thus 3bit x 3bit, thus 2^6=64 evals

    // check that the A_mle evaluated over the boolean hypercube equals the matrix A_i_j values
    let bhc = BooleanHypercube::new(A_mle.num_vars);
    let A_padded = pad_matrix(&A);
    for (i, A_i) in A_padded.iter().enumerate() {
      for (j, _) in A_i.iter().enumerate() {
        let mut s_i_j = bhc.at_i(i * A_i.len() + j);
        s_i_j.reverse();
        assert_eq!(A_mle.evaluate(&s_i_j), A_padded[i][j]);
      }
    }
  }

  #[test]
  fn test_vec_to_mle() {
    let z = get_test_z::<Fr>(3);
    let n_vars = 3;
    let z_mle = vec_to_mle(n_vars, &z);

    // check that the z_mle evaluated over the boolean hypercube equals the vec z_i values
    let bhc = BooleanHypercube::new(z_mle.num_vars);
    for (i, z) in z.iter().enumerate() {
      let mut s_i = bhc.at_i(i);
      s_i.reverse();
      assert_eq!(z_mle.evaluate(&s_i), *z);
    }
    // for the rest of elements of the boolean hypercube, expect it to evaluate to zero
    for i in (z.len())..(1 << z_mle.num_vars) {
      let mut s_i = bhc.at_i(i);
      s_i.reverse();
      assert_eq!(z_mle.evaluate(&s_i), Fr::zero());
    }
  }
}
