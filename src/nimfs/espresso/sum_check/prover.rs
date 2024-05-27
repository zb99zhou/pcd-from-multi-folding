// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

//! Prover subroutines for a SumCheck protocol.

use super::SumCheckProver;
use rayon::prelude::IntoParallelRefIterator;
use std::sync::Arc;
use ff::PrimeField;

use super::structs::{IOPProverMessage, IOPProverState};

// #[cfg(feature = "parallel")]
use rayon::iter::{IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator};
use crate::errors::NovaError;
use crate::nimfs::espresso::batch_inversion;
use crate::nimfs::espresso::virtual_polynomial::VirtualPolynomial;
use crate::spartan::polys::multilinear::MultiLinearPolynomial;
use crate::traits::Group;

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
                    let points = (0..1 + degree as u64).map(C::Scalar::from).collect::<Vec<_>>();
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
        let mut flattened_ml_extensions: Vec<MultiLinearPolynomial<C::Scalar>> = self
            .poly
            .flattened_ml_extensions
            .par_iter()
            .map(|x| x.as_ref().clone())
            .collect();

        if let Some(chal) = challenge {
            if self.round == 0 {
                return Err(NovaError::InvalidSumCheckProver(
                    "first round should be prover first.".to_string(),
                ));
            }
            self.challenges.push(*chal);

            let r = self.challenges[self.round - 1];
            // #[cfg(feature = "parallel")]
            flattened_ml_extensions
                .par_iter_mut()
                .for_each(|mle| *mle = mle.fix_variables(&[r]));
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

        let products_list = self.poly.products.clone();
        let mut products_sum = vec![C::Scalar::default(); self.poly.aux_info.max_degree + 1];

        // Step 2: generate sum for the partial evaluated polynomial:
        // f(r_1, ... r_m,, x_{m+1}... x_n)

        products_list.iter().for_each(|(coefficient, products)| {
            let mut sum = (0..1 << (self.poly.aux_info.num_variables - self.round))
                .into_par_iter()
                .fold(
                    || {
                        (
                            vec![(C::Scalar::default(), C::Scalar::default()); products.len()],
                            vec![C::Scalar::default(); products.len() + 1],
                        )
                    },
                    |(mut buf, mut acc), b| {
                        buf.iter_mut()
                            .zip(products.iter())
                            .for_each(|((eval, step), f)| {
                                let table = &flattened_ml_extensions[*f];
                                *eval = table[b << 1];
                                *step = table[(b << 1) + 1] - table[b << 1];
                            });
                        acc[0] += buf.iter().map(|(eval, _)| eval).product::<C::Scalar>();
                        acc[1..].iter_mut().for_each(|acc| {
                            buf.iter_mut().for_each(|(eval, step)| *eval += step as &_);
                            *acc += buf.iter().map(|(eval, _)| eval).product::<C::Scalar>();
                        });
                        (buf, acc)
                    },
                )
                .map(|(_, partial)| partial)
                .reduce(
                    || vec![C::Scalar::default(); products.len() + 1],
                    |mut sum, partial| {
                        sum.iter_mut()
                            .zip(partial.iter())
                            .for_each(|(sum, partial)| *sum += partial);
                        sum
                    },
                );
            sum.iter_mut().for_each(|sum| *sum *= coefficient);
            let extraploation = (0..self.poly.aux_info.max_degree - products.len())
                .into_par_iter()
                .map(|i| {
                    let (points, weights) = &self.extrapolation_aux[products.len() - 1];
                    let at = C::Scalar::from((products.len() + 1 + i) as u64);
                    extrapolate(points, weights, &sum, &at)
                })
                .collect::<Vec<_>>();
            products_sum
                .iter_mut()
                .zip(sum.iter().chain(extraploation.iter()))
                .for_each(|(products_sum, sum)| *products_sum += sum);
        });

        // update prover's state to the partial evaluated polynomial
        self.poly.flattened_ml_extensions = flattened_ml_extensions
            .into_par_iter()
            .map(|x| Arc::new(x))
            .collect();

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
                .filter_map(|(i, point_i)| (i != j).then(|| *point_j - point_i))
                .reduce(|acc, value| acc * value)
                .unwrap_or_else(|| F::ONE)
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
