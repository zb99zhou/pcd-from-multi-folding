// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

//! This module defines structs that are shared by all sub protocols.

use crate::nimfs::espresso::virtual_polynomial::VirtualPolynomial;
use crate::traits::{Group, TranscriptReprTrait};
use serde::{Deserialize, Serialize};

/// An IOP proof is a collections of
/// - messages from prover to verifier at each round through the interactive
///   protocol.
/// - a point that is generated by the transcript for evaluation
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct IOPProof<C: Group> {
  pub point: Vec<C::Scalar>,
  pub proofs: Vec<IOPProverMessage<C>>,
}

/// A message from the prover to the verifier at a given round
/// is a list of evaluations.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct IOPProverMessage<C: Group> {
  pub(crate) evaluations: Vec<C::Scalar>,
}

impl<C: Group> TranscriptReprTrait<C> for IOPProverMessage<C> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    self
      .evaluations
      .iter()
      .flat_map(|eval| eval.to_transcript_bytes())
      .collect()
  }

  fn to_transcript_scalars(&self) -> Vec<C::Scalar> {
    self.evaluations.clone()
  }
}

/// Prover State of a PolyIOP.
#[derive(Debug)]
pub struct IOPProverState<C: Group> {
  /// sampled randomness given by the verifier
  pub challenges: Vec<C::Scalar>,
  /// the current round number
  pub(crate) round: usize,
  /// pointer to the virtual polynomial
  pub(crate) poly: VirtualPolynomial<C::Scalar>,
  /// points with precomputed barycentric weights for extrapolating smaller
  /// degree uni-polys to `max_degree + 1` evaluations.
  pub(crate) extrapolation_aux: Vec<(Vec<C::Scalar>, Vec<C::Scalar>)>,
}

/// Prover State of a PolyIOP
#[derive(Debug)]
pub struct IOPVerifierState<C: Group> {
  pub(crate) round: usize,
  pub(crate) num_vars: usize,
  pub(crate) max_degree: usize,
  pub(crate) finished: bool,
  /// a list storing the univariate polynomial in evaluation form sent by the
  /// prover at each round
  pub(crate) polynomials_received: Vec<Vec<C::Scalar>>,
  /// a list storing the randomness sampled by the verifier at each round
  pub(crate) challenges: Vec<C::Scalar>,
}
