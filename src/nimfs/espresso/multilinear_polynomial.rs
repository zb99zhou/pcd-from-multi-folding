// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

use crate::spartan::polys::multilinear::MultiLinearPolynomial;
use ff::PrimeField;
use rayon::prelude::{IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator};

pub fn fix_variables<F: PrimeField>(
  poly: &MultiLinearPolynomial<F>,
  partial_point: &[F],
) -> MultiLinearPolynomial<F> {
  assert!(
    partial_point.len() <= poly.num_vars,
    "invalid size of partial point"
  );
  let nv = poly.num_vars;
  let mut poly = poly.Z.to_vec();
  let dim = partial_point.len();
  // evaluate single variable of partial point from left to right
  for (i, point) in partial_point.iter().enumerate().take(dim) {
    poly = fix_one_variable_helper(&poly, nv - i, point);
  }

  MultiLinearPolynomial {
    num_vars: nv - dim,
    Z: poly[..(1 << (nv - dim))].to_vec(),
  }
}

fn fix_one_variable_helper<F: PrimeField>(data: &[F], nv: usize, point: &F) -> Vec<F> {
  let mut res = vec![F::default(); 1 << (nv - 1)];

  // // evaluate single variable of partial point from left to right
  // #[cfg(not(feature = "parallel"))]
  // for i in 0..(1 << (nv - 1)) {
  //     res[i] = data[i] + (data[(i << 1) + 1] - data[i << 1]) * point;
  // }

  res.par_iter_mut().enumerate().for_each(|(i, x)| {
    *x = data[i << 1] + (data[(i << 1) + 1] - data[i << 1]) * point;
  });

  res
}
//
// pub fn evaluate_no_par<F: PrimeField>(poly: &MultiLinearPolynomial<F>, point: &[F]) -> F {
//     assert_eq!(poly.num_vars, point.len());
//     fix_variables_no_par(poly, point).Z[0]
// }
//
// fn fix_variables_no_par<F: PrimeField>(
//     poly: &MultiLinearPolynomial<F>,
//     partial_point: &[F],
// ) -> MultiLinearPolynomial<F> {
//     assert!(
//         partial_point.len() <= poly.num_vars,
//         "invalid size of partial point"
//     );
//     let nv = poly.num_vars;
//     let mut poly = poly.Z.to_vec();
//     let dim = partial_point.len();
//     // evaluate single variable of partial point from left to right
//     for i in 1..dim + 1 {
//         let r = partial_point[i - 1];
//         for b in 0..(1 << (nv - i)) {
//             poly[b] = poly[b << 1] + (poly[(b << 1) + 1] - poly[b << 1]) * r;
//         }
//     }
//     MultiLinearPolynomial::new(poly[..(1 << (nv - dim))].to_vec())
// }

/// Given multilinear polynomial `p(x)` and s `s`, compute `s*p(x)`
pub fn scalar_mul<F: PrimeField>(
  poly: &MultiLinearPolynomial<F>,
  s: &F,
) -> MultiLinearPolynomial<F> {
  MultiLinearPolynomial {
    Z: poly.Z.iter().map(|e| *e * s).collect(),
    num_vars: poly.num_vars,
  }
}

/// Test-only methods used in virtual_polynomial.rs
#[cfg(test)]
pub mod testing_code {
  use super::*;
  use ff::PrimeField;
  use rand_core::RngCore;
  use std::sync::Arc;

  pub fn fix_last_variables<F: PrimeField>(
    poly: &MultiLinearPolynomial<F>,
    partial_point: &[F],
  ) -> MultiLinearPolynomial<F> {
    assert!(
      partial_point.len() <= poly.num_vars,
      "invalid size of partial point"
    );
    let nv = poly.num_vars;
    let mut poly = poly.Z.to_vec();
    let dim = partial_point.len();
    // evaluate single variable of partial point from left to right
    for (i, point) in partial_point.iter().rev().enumerate().take(dim) {
      poly = fix_last_variable_helper(&poly, nv - i, point);
    }

    MultiLinearPolynomial::<F>::new(poly[..(1 << (nv - dim))].to_vec())
  }

  fn fix_last_variable_helper<F: PrimeField>(data: &[F], nv: usize, point: &F) -> Vec<F> {
    let half_len = 1 << (nv - 1);
    let mut res = vec![F::default(); half_len];

    // evaluate single variable of partial point from left to right
    // #[cfg(not(feature = "parallel"))]
    // for b in 0..half_len {
    //     res[b] = data[b] + (data[b + half_len] - data[b]) * point;
    // }
    //
    // #[cfg(feature = "parallel")]
    res.par_iter_mut().enumerate().for_each(|(i, x)| {
      *x = data[i] + (data[i + half_len] - data[i]) * point;
    });

    res
  }

  /// Sample a random list of multilinear polynomials.
  /// Returns
  /// - the list of polynomials,
  /// - its sum of polynomial evaluations over the boolean hypercube.
  #[cfg(test)]
  pub fn random_mle_list<F: PrimeField, R: RngCore>(
    nv: usize,
    degree: usize,
    rng: &mut R,
  ) -> (Vec<Arc<MultiLinearPolynomial<F>>>, F) {
    let mut multiplicands = Vec::with_capacity(degree);
    for _ in 0..degree {
      multiplicands.push(Vec::with_capacity(1 << nv))
    }
    let mut sum = F::default();

    for _ in 0..(1 << nv) {
      let mut product = F::ONE;

      for e in multiplicands.iter_mut() {
        let val = F::random(&mut *rng);
        e.push(val);
        product *= val;
      }
      sum += product;
    }

    let list = multiplicands
      .into_iter()
      .map(|x| Arc::new(MultiLinearPolynomial::new(x)))
      .collect();

    (list, sum)
  }
  //
  // // Build a randomize list of mle-s whose sum is zero.
  // #[cfg(test)]
  // pub fn random_zero_mle_list<F: PrimeField, R: RngCore>(
  //     nv: usize,
  //     degree: usize,
  //     rng: &mut R,
  // ) -> Vec<Arc<MultiLinearPolynomial<F>>> {
  //
  //     let mut multiplicands = Vec::with_capacity(degree);
  //     for _ in 0..degree {
  //         multiplicands.push(Vec::with_capacity(1 << nv))
  //     }
  //     for _ in 0..(1 << nv) {
  //         multiplicands[0].push(F::default());
  //         for e in multiplicands.iter_mut().skip(1) {
  //             e.push(F::random(&mut *rng));
  //         }
  //     }
  //
  //     let list = multiplicands
  //         .into_iter()
  //         .map(|x| Arc::new(MultiLinearPolynomial::new(x.clone())))
  //         .collect();
  //
  //     list
  // }
}
