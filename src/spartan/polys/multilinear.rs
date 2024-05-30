//! Main components:
//! - `MultilinearPolynomial`: Dense representation of multilinear polynomials, represented by evaluations over all possible binary inputs.
//! - `SparsePolynomial`: Efficient representation of sparse multilinear polynomials, storing only non-zero evaluations.

use std::ops::{Add, Index};

use ff::PrimeField;
use rayon::prelude::{
  IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator,
  IntoParallelRefMutIterator, ParallelIterator,
};
use serde::{Deserialize, Serialize};

use crate::spartan::{math::Math, polys::eq::EqPolynomial};

/// A multilinear extension of a polynomial $Z(\cdot)$, denote it as $\tilde{Z}(x_1, ..., x_m)$
/// where the degree of each variable is at most one.
///
/// This is the dense representation of a multilinear poynomial.
/// Let it be $\mathbb{G}(\cdot): \mathbb{F}^m \rightarrow \mathbb{F}$, it can be represented uniquely by the list of
/// evaluations of $\mathbb{G}(\cdot)$ over the Boolean hypercube $\{0, 1\}^m$.
///
/// For example, a 3 variables multilinear polynomial can be represented by evaluation
/// at points $[0, 2^3-1]$.
///
/// The implementation follows
/// $$
/// \tilde{Z}(x_1, ..., x_m) = \sum_{e\in {0,1}^m}Z(e) \cdot \prod_{i=1}^m(x_i \cdot e_i + (1-x_i) \cdot (1-e_i))
/// $$
///
/// Vector $Z$ indicates $Z(e)$ where $e$ ranges from $0$ to $2^m-1$.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MultiLinearPolynomial<Scalar: PrimeField> {
  pub(crate) num_vars: usize, // the number of variables in the multilinear polynomial
  pub(crate) Z: Vec<Scalar>,  // evaluations of the polynomial in all the 2^num_vars Boolean inputs
}

impl<Scalar: PrimeField> MultiLinearPolynomial<Scalar> {
  /// Creates a new `MultilinearPolynomial` from the given evaluations.
  ///
  /// The number of evaluations must be a power of two.
  pub fn new(mut Z: Vec<Scalar>) -> Self {
    let num_var = Z.len().next_power_of_two();
    Z.resize(num_var, Scalar::ZERO);
    MultiLinearPolynomial {
      num_vars: usize::try_from(Z.len().ilog2()).unwrap(),
      Z,
    }
  }

  /// Returns the number of variables in the multilinear polynomial
  pub const fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  /// Returns the total number of evaluations.
  pub fn len(&self) -> usize {
    self.Z.len()
  }

  /// Checks if the multilinear polynomial is empty.
  ///
  /// This method returns true if the polynomial has no evaluations, and false otherwise.
  pub fn is_empty(&self) -> bool {
    self.Z.is_empty()
  }

  /// Bounds the polynomial's top variable using the given scalar.
  ///
  /// This operation modifies the polynomial in-place.
  pub fn bound_poly_var_top(&mut self, r: &Scalar) {
    let n = self.len() / 2;

    let (left, right) = self.Z.split_at_mut(n);

    left
      .par_iter_mut()
      .zip(right.par_iter())
      .for_each(|(a, b)| {
        *a += *r * (*b - *a);
      });

    self.Z.resize(n, Scalar::ZERO);
    self.num_vars -= 1;
  }

  /// Evaluates the polynomial at the given point.
  /// Returns Z(r) in O(n) time.
  pub fn evaluate(&self, r: &[Scalar]) -> Scalar {
    // r must have a value for each variable
    assert_eq!(r.len(), self.get_num_vars());
    let chis = EqPolynomial::new(r.to_vec()).evals();
    assert_eq!(chis.len(), self.Z.len());

    (0..chis.len())
      .into_par_iter()
      .map(|i| chis[i] * self.Z[i])
      .sum()
  }

  /// Evaluates the polynomial with the given evaluations and point.
  pub fn evaluate_with(Z: &[Scalar], r: &[Scalar]) -> Scalar {
    EqPolynomial::new(r.to_vec())
      .evals()
      .into_par_iter()
      .zip(Z.into_par_iter())
      .map(|(a, b)| a * b)
      .sum()
  }

  /// Multiplies the polynomial by a scalar.
  pub fn scalar_mul(&self, scalar: &Scalar) -> Self {
    let mut new_poly = self.clone();
    for z in &mut new_poly.Z {
      *z *= scalar;
    }
    new_poly
  }

  // pub fn fix_variables(&self, partial_point: &[Scalar]) -> Self {
  //   assert!(
  //     partial_point.len() <= self.num_vars,
  //     "invalid size of partial point"
  //   );
  //   let mut poly = self.Z.to_vec();
  //   let nv = self.num_vars;
  //   let dim = partial_point.len();
  //   // Evaluate single variable of partial point from right to left
  //   for i in (1..dim + 1).rev() {
  //     let r = partial_point[i - 1];
  //     for b in 0..(1 << (nv - (dim - i + 1))) {
  //       let left = poly[b << 1];
  //       let right = poly[(b << 1) + 1];
  //       poly[b] = left + r * (right - left);
  //     }
  //   }
  //   Self { num_vars: nv - dim, Z: poly[..(1 << (nv - dim))].to_vec() }
  // }

  pub fn fix_variables(&self, partial_point: &[Scalar]) -> Self {
    assert!(
      partial_point.len() <= self.num_vars,
      "invalid size of partial point"
    );
    let mut poly = self.Z.to_vec();
    let nv = self.num_vars;
    let dim = partial_point.len();
    // println!("nv = {:?}, dim = {:?}", nv, dim);
    // println!("poly_len = {:?}", poly.len());
    // Evaluate single variable of partial point from left to right
    for i in 1..dim + 1 {
      // println!("i = {:?}", i);
      let r = partial_point[i - 1];
      for b in 0..(1 << (nv - i)) {
        // println!("b = {:?}", b);
        let left = poly[b];
        let right = poly[b + (1 << (nv - i))];
        poly[b] = left + r * (right - left); // (1-r) * left + r * right
      }
    }
    Self {
      num_vars: nv - dim,
      Z: poly[..(1 << (nv - dim))].to_vec(),
    }
  }
}

impl<Scalar: PrimeField> Index<usize> for MultiLinearPolynomial<Scalar> {
  type Output = Scalar;

  #[inline(always)]
  fn index(&self, _index: usize) -> &Scalar {
    &(self.Z[_index])
  }
}

/// Sparse multilinear polynomial, which means the $Z(\cdot)$ is zero at most points.
/// So we do not have to store every evaluations of $Z(\cdot)$, only store the non-zero points.
///
/// For example, the evaluations are [0, 0, 0, 1, 0, 1, 0, 2].
/// The sparse polynomial only store the non-zero values, [(3, 1), (5, 1), (7, 2)].
/// In the tuple, the first is index, the second is value.
pub(crate) struct SparsePolynomial<Scalar: PrimeField> {
  pub(crate) num_vars: usize,
  Z: Vec<(usize, Scalar)>,
}

impl<Scalar: PrimeField> SparsePolynomial<Scalar> {
  pub fn new(num_vars: usize, Z: Vec<(usize, Scalar)>) -> Self {
    SparsePolynomial { num_vars, Z }
  }

  /// Computes the $\tilde{eq}$ extension polynomial.
  /// return 1 when a == r, otherwise return 0.
  fn compute_chi(a: &[bool], r: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), r.len());
    let mut chi_i = Scalar::ONE;
    for j in 0..r.len() {
      if a[j] {
        chi_i *= r[j];
      } else {
        chi_i *= Scalar::ONE - r[j];
      }
    }
    chi_i
  }

  // Takes O(n log n)
  pub fn evaluate(&self, r: &[Scalar]) -> Scalar {
    assert_eq!(self.num_vars, r.len());

    (0..self.Z.len())
      .into_par_iter()
      .map(|i| {
        let bits = (self.Z[i].0).get_bits(r.len());
        SparsePolynomial::compute_chi(&bits, r) * self.Z[i].1
      })
      .sum()
  }
}

/// Adds another multilinear polynomial to `self`.
/// Assumes the two polynomials have the same number of variables.
impl<Scalar: PrimeField> Add for MultiLinearPolynomial<Scalar> {
  type Output = Result<Self, &'static str>;

  fn add(self, other: Self) -> Self::Output {
    if self.get_num_vars() != other.get_num_vars() {
      return Err("The two polynomials must have the same number of variables");
    }

    let sum: Vec<Scalar> = self
      .Z
      .iter()
      .zip(other.Z.iter())
      .map(|(a, b)| *a + *b)
      .collect();

    Ok(MultiLinearPolynomial::new(sum))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use pasta_curves::Fp;

  fn make_mlp<F: PrimeField>(len: usize, value: F) -> MultiLinearPolynomial<F> {
    MultiLinearPolynomial {
      num_vars: len.count_ones() as usize,
      Z: vec![value; len],
    }
  }

  fn test_multilinear_polynomial_with<F: PrimeField>() {
    // Let the polynomial has 3 variables, p(x_1, x_2, x_3) = (x_1 + x_2) * x_3
    // Evaluations of the polynomial at boolean cube are [0, 0, 0, 1, 0, 1, 0, 2].

    let TWO = F::from(2);

    let Z = vec![
      F::ZERO,
      F::ZERO,
      F::ZERO,
      F::ONE,
      F::ZERO,
      F::ONE,
      F::ZERO,
      TWO,
    ];
    let m_poly = MultiLinearPolynomial::<F>::new(Z.clone());
    assert_eq!(m_poly.get_num_vars(), 3);

    let x = vec![F::ONE, F::ONE, F::ONE];
    assert_eq!(m_poly.evaluate(x.as_slice()), TWO);

    let y = MultiLinearPolynomial::<F>::evaluate_with(Z.as_slice(), x.as_slice());
    assert_eq!(y, TWO);

    let mle = m_poly.fix_variables(x.as_slice());
    assert_eq!(mle[0], TWO);

    let z = vec![F::ONE, F::ZERO];
    let m_partial = m_poly.fix_variables(z.as_slice());
    println!("m_partial = {:?}", m_partial);

    let test = vec![F::from(2), F::from(3), F::from(4)];
    assert_eq!(
      m_poly.evaluate(test.as_slice()),
      m_poly.fix_variables(test.as_slice()).Z[0]
    );
  }

  fn test_sparse_polynomial_with<F: PrimeField>() {
    // Let the polynomial have 3 variables, p(x_1, x_2, x_3) = (x_1 + x_2) * x_3
    // Evaluations of the polynomial at boolean cube are [0, 0, 0, 1, 0, 1, 0, 2].

    let TWO = F::from(2);
    let Z = vec![(3, F::ONE), (5, F::ONE), (7, TWO)];
    let m_poly = SparsePolynomial::<F>::new(3, Z);

    let x = vec![F::ONE, F::ONE, F::ONE];
    assert_eq!(m_poly.evaluate(x.as_slice()), TWO);

    let x = vec![F::ONE, F::ZERO, F::ONE];
    assert_eq!(m_poly.evaluate(x.as_slice()), F::ONE);
  }

  #[test]
  fn test_multilinear_polynomial() {
    test_multilinear_polynomial_with::<Fp>();
  }

  #[test]
  fn test_sparse_polynomial() {
    test_sparse_polynomial_with::<Fp>();
  }

  fn test_mlp_add_with<F: PrimeField>() {
    let mlp1 = make_mlp(4, F::from(3));
    let mlp2 = make_mlp(4, F::from(7));

    let mlp3 = mlp1.add(mlp2).unwrap();

    assert_eq!(mlp3.Z, vec![F::from(10); 4]);
  }

  fn test_mlp_scalar_mul_with<F: PrimeField>() {
    let mlp = make_mlp(4, F::from(3));

    let mlp2 = mlp.scalar_mul(&F::from(2));

    assert_eq!(mlp2.Z, vec![F::from(6); 4]);
  }

  #[test]
  fn test_mlp_add() {
    test_mlp_add_with::<Fp>();
  }

  #[test]
  fn test_mlp_scalar_mul() {
    test_mlp_scalar_mul_with::<Fp>();
  }

  fn test_evaluation_with<F: PrimeField>() {
    let num_evals = 4;
    let mut evals: Vec<F> = Vec::with_capacity(num_evals);
    for _ in 0..num_evals {
      evals.push(F::from_u128(8));
    }
    let dense_poly: MultiLinearPolynomial<F> = MultiLinearPolynomial::new(evals.clone());

    // Evaluate at 3:
    // (0, 0) = 1
    // (0, 1) = 1
    // (1, 0) = 1
    // (1, 1) = 1
    // g(x_0,x_1) => c_0*(1 - x_0)(1 - x_1) + c_1*(1-x_0)(x_1) + c_2*(x_0)(1-x_1) + c_3*(x_0)(x_1)
    // g(3, 4) = 8*(1 - 3)(1 - 4) + 8*(1-3)(4) + 8*(3)(1-4) + 8*(3)(4) = 48 + -64 + -72 + 96  = 8
    // g(5, 10) = 8*(1 - 5)(1 - 10) + 8*(1 - 5)(10) + 8*(5)(1-10) + 8*(5)(10) = 96 + -16 + -72 + 96  = 8
    assert_eq!(
      dense_poly.evaluate(vec![F::from(3), F::from(4)].as_slice()),
      F::from(8)
    );
  }

  #[test]
  fn test_evaluation() {
    test_evaluation_with::<Fp>();
  }
}
