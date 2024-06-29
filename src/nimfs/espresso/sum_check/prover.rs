// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

//! Prover subroutines for a SumCheck protocol.

use super::SumCheckProver;
use ff::PrimeField;
use rayon::prelude::{IndexedParallelIterator, IntoParallelRefMutIterator};
use std::sync::Arc;

use super::structs::{IOPProverMessage, IOPProverState};

use crate::errors::NovaError;
use crate::nimfs::espresso::batch_inversion;
use crate::nimfs::espresso::virtual_polynomial::VirtualPolynomial;
use crate::traits::Group;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

impl<C: Group> SumCheckProver<C::Scalar> for IOPProverState<C> {
  type VirtualPolynomial = VirtualPolynomial<C::Scalar>;
  type ProverMessage = IOPProverMessage<C>;

  /// Initialize the prover state to argue for the sum of the input polynomial
  /// over {0,1}^`num_vars`.
  fn prover_init(polynomial: &Self::VirtualPolynomial) -> Result<Self, NovaError> {
    if polynomial.aux_info.num_variables == 0 {
      return Err(NovaError::InvalidSumCheckParameters(
        "Attempt to prove a constant.".to_string(),
      ));
    }

    Ok(Self {
      challenges: Vec::with_capacity(polynomial.aux_info.num_variables),
      round: 0,
      poly: polynomial.clone(),
      extrapolation_aux: (1..polynomial.aux_info.max_degree)
        .map(|degree| {
          let points = (0..1 + degree as u64)
            .map(C::Scalar::from)
            .collect::<Vec<_>>();
          let weights = barycentric_weights(&points);
          (points, weights)
        })
        .collect(),
    })
  }

  /// Receive message from verifier, generate prover message, and proceed to
  /// next round.
  ///
  /// Main algorithm used is from section 3.2 of [XZZPS19](https://eprint.iacr.org/2019/317.pdf#subsection.3.2).
  fn prove_round_and_update_state(
    &mut self,
    challenge: &Option<C::Scalar>,
  ) -> Result<Self::ProverMessage, NovaError> {
    if self.round >= self.poly.aux_info.num_variables {
      return Err(NovaError::InvalidSumCheckProver(
        "Prover is not active".to_string(),
      ));
    }

    // Step 1:
    // fix argument and evaluate f(x) over x_m = r; where r is the challenge
    // for the current round, and m is the round number, indexed from 1
    //
    // i.e.:
    // at round m <= n, for each mle g(x_1, ... x_n) within the flattened_mle
    // which has already been evaluated to
    //
    //    g(r_1, ..., r_{m-1}, x_m ... x_n)
    //
    // eval g over r_m, and mutate g to g(r_1, ... r_m,, x_{m+1}... x_n)
    if let Some(chal) = challenge {
      if self.round == 0 {
        return Err(NovaError::InvalidSumCheckProver(
          "first round should be prover first.".to_string(),
        ));
      }
      self.challenges.push(*chal);

      let r = self.challenges[self.round - 1];
      // #[cfg(feature = "parallel")]
      self
        .poly
        .flattened_ml_extensions
        .par_iter_mut()
        .for_each(|mle| *mle = Arc::new(mle.fix_variables(&[r])));

      // #[cfg(not(feature = "parallel"))]
      // flattened_ml_extensions
      //     .iter_mut()
      //     .for_each(|mle| *mle = fix_variables(mle, &[r]));
    } else if self.round > 0 {
      return Err(NovaError::InvalidSumCheckProver(
        "verifier message is empty".to_string(),
      ));
    }

    self.round += 1;

    let i = self.round;
    let nv = self.poly.aux_info.num_variables;
    let degree = self.poly.aux_info.max_degree; // the degree of univariate polynomial sent by prover at this round

    let zeros = || (vec![C::Scalar::default(); degree + 1], vec![C::Scalar::default(); degree + 1]);

    // generate sum
    let fold_result = (0..1 << (nv - i)).into_par_iter().with_min_len(1 << 10).fold(
      zeros,
      |(mut products_sum, mut product), b| {
        // In effect, this fold is essentially doing simply:
        // for b in 0..1 << (nv - i) {
        for (coefficient, products) in &self.poly.products {
          product.fill(*coefficient);
          for &jth_product in products {
            let table = &self.poly.flattened_ml_extensions[jth_product];
            let mut start = table[b];
            let step = table[b + (1 << (self.poly.aux_info.num_variables - self.round))] - start;
            for p in product.iter_mut() {
              *p *= start;
              start += step;
            }
          }
          for t in 0..degree + 1 {
            products_sum[t] += product[t];
          }
        }
        (products_sum, product)
      },
    );

    // When rayon is used, the `fold` operation results in an iterator of `Vec<F>` rather than a single `Vec<F>`.
    // In this case, we simply need to sum them.
    let products_sum = fold_result.map(|scratch| scratch.0).reduce(
      || vec![C::Scalar::default(); degree + 1],
      |mut overall_products_sum, sublist_sum| {
        overall_products_sum
            .iter_mut()
            .zip(sublist_sum.iter())
            .for_each(|(f, s)| *f += s);
        overall_products_sum
      },
    );
    Ok(IOPProverMessage {
      evaluations: products_sum,
    })
  }
}

fn barycentric_weights<F: PrimeField>(points: &[F]) -> Vec<F> {
  let mut weights = points
    .iter()
    .enumerate()
    .map(|(j, point_j)| {
      points
        .iter()
        .enumerate()
        .filter(|&(i, _point_i)| (i != j))
        .map(|(_i, point_i)| *point_j - point_i)
        .reduce(|acc, value| acc * value)
        .unwrap_or(F::ONE)
    })
    .collect::<Vec<_>>();
  batch_inversion(&mut weights);
  weights
}

fn extrapolate<F: PrimeField>(points: &[F], weights: &[F], evals: &[F], at: &F) -> F {
  let (coeffs, sum_inv) = {
    let mut coeffs = points.iter().map(|point| *at - point).collect::<Vec<_>>();
    batch_inversion(&mut coeffs);
    coeffs.iter_mut().zip(weights).for_each(|(coeff, weight)| {
      *coeff *= *weight;
    });
    let sum_inv = coeffs.iter().copied().sum::<F>();
    let sum_inv = sum_inv.invert().unwrap_or_else(F::default);
    (coeffs, sum_inv)
  };
  coeffs
    .iter()
    .zip(evals)
    .map(|(coeff, eval)| *coeff * eval)
    .sum::<F>()
    * sum_inv
}
