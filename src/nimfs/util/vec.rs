use ff::PrimeField;

use crate::nimfs::util::spare_matrix::SparseMatrix;
use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::ParallelIterator;

/// A sparse representation of constraint matrices.
pub type Matrix<F> = Vec<Vec<F>>;

/// Hadamard product between two vectors
pub fn hadamard<F: PrimeField>(a: &Vec<F>, b: &Vec<F>) -> Vec<F> {
  a.par_iter().zip(b).map(|(a, b)| *a * b).collect()
}

// Multiply matrix by vector
pub fn mat_vec_mul<F: PrimeField>(mat: &SparseMatrix<F>, vec: &[F]) -> Vec<F> {
  // matrices are lists of rows
  // rows are (value, idx) pairs
  let mut result = vec![F::default(); mat.rows];
  for (r, c, mat_val) in mat.iter() {
    assert!(c < vec.len());
    result[r] += mat_val * vec[c];
  }
  result
}

// Multiply vector by scalar
pub fn vec_scalar_mul<F: PrimeField>(vec: &[F], c: &F) -> Vec<F> {
  let mut result = vec![F::default(); vec.len()];
  for (i, a) in vec.iter().enumerate() {
    result[i] = *a * c;
  }
  result
}

// Add two vectors
pub fn vec_add<F: PrimeField>(vec_a: &[F], vec_b: &[F]) -> Vec<F> {
  assert_eq!(vec_a.len(), vec_b.len());

  let mut result = vec![F::default(); vec_a.len()];
  for i in 0..vec_a.len() {
    result[i] = vec_a[i] + vec_b[i];
  }
  result
}

pub fn to_F_matrix<F: PrimeField>(M: Vec<Vec<usize>>) -> Vec<Vec<F>> {
  let mut R: Vec<Vec<F>> = vec![Vec::new(); M.len()];
  for i in 0..M.len() {
    R[i] = vec![F::default(); M[i].len()];
    for j in 0..M[i].len() {
      R[i][j] = F::from(M[i][j] as u64);
    }
  }
  R
}

pub fn to_F_vec<F: PrimeField>(z: Vec<usize>) -> Vec<F> {
  let mut r: Vec<F> = vec![F::default(); z.len()];
  for i in 0..z.len() {
    r[i] = F::from(z[i] as u64);
  }
  r
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::provider::bn256_grumpkin::bn256;

  #[test]
  fn test_hadamard() -> () {
    let A = vec![
      bn256::Scalar::from(1u64),
      bn256::Scalar::from(2u64),
      bn256::Scalar::from(3u64),
      bn256::Scalar::from(4u64),
      bn256::Scalar::from(5u64),
      bn256::Scalar::from(6u64),
    ];

    let B = vec![
      bn256::Scalar::from(6u64),
      bn256::Scalar::from(5u64),
      bn256::Scalar::from(4u64),
      bn256::Scalar::from(3u64),
      bn256::Scalar::from(2u64),
      bn256::Scalar::from(1u64),
    ];

    let C = hadamard(&A, &B);
    assert_eq!(
      C,
      vec![
        bn256::Scalar::from(6u64),
        bn256::Scalar::from(10u64),
        bn256::Scalar::from(12u64),
        bn256::Scalar::from(12u64),
        bn256::Scalar::from(10u64),
        bn256::Scalar::from(6u64)
      ]
    );
  }

  #[test]
  fn test_mat_vec_mul() -> () {
    let A = vec![
      vec![
        bn256::Scalar::from(2u64),
        bn256::Scalar::from(3u64),
        bn256::Scalar::from(4u64),
      ],
      vec![
        bn256::Scalar::from(4u64),
        bn256::Scalar::from(11u64),
        bn256::Scalar::from(14u64),
      ],
      vec![
        bn256::Scalar::from(2u64),
        bn256::Scalar::from(8u64),
        bn256::Scalar::from(17u64),
      ],
    ];
    let v = vec![
      bn256::Scalar::from(19u64),
      bn256::Scalar::from(55u64),
      bn256::Scalar::from(50u64),
    ];

    let result = mat_vec_mul(&(&A).into(), &v);
    assert_eq!(
      result,
      vec![
        bn256::Scalar::from(403u64),
        bn256::Scalar::from(1381u64),
        bn256::Scalar::from(1328u64)
      ]
    );

    assert_eq!(
      vec_scalar_mul(&result, &bn256::Scalar::from(2u64)),
      vec![
        bn256::Scalar::from(806u64),
        bn256::Scalar::from(2762u64),
        bn256::Scalar::from(2656u64)
      ]
    );
  }
}
