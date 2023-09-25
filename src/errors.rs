//! This module defines errors returned by the library.
use core::fmt::Debug;
use thiserror::Error;
use crate::nimfs::espresso::errors::ArithErrors;

/// Errors returned by Nova
#[derive(Clone, Debug, Eq, PartialEq, Error)]
pub enum NovaError {
  /// returned if the supplied row or col in (row,col,val) tuple is out of range
  #[error("InvalidIndex")]
  InvalidIndex,
  /// returned if the supplied input is not even-sized
  #[error("OddInputLength")]
  OddInputLength,
  /// returned if the supplied input is not of the right length
  #[error("InvalidInputLength")]
  InvalidInputLength,
  /// returned if the supplied witness is not of the right length
  #[error("InvalidWitnessLength")]
  InvalidWitnessLength,
  /// returned if the supplied witness is not a satisfying witness to a given shape and instance
  #[error("UnSat")]
  UnSat,
  /// returned when the supplied compressed commitment cannot be decompressed
  #[error("DecompressionError")]
  DecompressionError,
  /// returned if proof verification fails
  #[error("ProofVerifyError")]
  ProofVerifyError,
  /// returned if the provided number of steps is zero
  #[error("InvalidNumSteps")]
  InvalidNumSteps,
  /// returned when an invalid inner product argument is provided
  #[error("InvalidIPA")]
  InvalidIPA,
  /// returned when an invalid sum-check proof is provided
  #[error("InvalidSumcheckProof")]
  InvalidSumcheckProof,
  /// returned when the initial input to an incremental computation differs from a previously declared arity
  #[error("InvalidInitialInputLength")]
  InvalidInitialInputLength,
  /// returned when the step execution produces an output whose length differs from a previously declared arity
  #[error("InvalidStepOutputLength")]
  InvalidStepOutputLength,
  /// returned when the transcript engine encounters an overflow of the round number
  #[error("InternalTranscriptError")]
  InternalTranscriptError,
  /// returned when the multiset check fails
  #[error("InvalidMultisetProof")]
  InvalidMultisetProof,
  /// returned when the product proof check fails
  #[error("InvalidProductProof")]
  InvalidProductProof,
  /// returned when the consistency with public IO and assignment used fails
  #[error("IncorrectWitness")]
  IncorrectWitness,
  /// return when error during synthesis
  #[error("SynthesisError")]
  SynthesisError,
  /// Invalid Prover: {0}
  #[error("InvalidSumCheckProver")]
  InvalidSumCheckProver(String),
  /// Invalid Verifier: {0}
  #[error("InvalidSumCheckVerifier")]
  InvalidSumCheckVerifier(String),
  /// Invalid Proof: {0}
  #[error("InvalidSumCheckProof")]
  InvalidSumCheckProof(String),
  /// Invalid parameters: {0}
  #[error("InvalidSumCheckParameters")]
  InvalidSumCheckParameters(String),
  /// Should not arrive to this point
  #[error("ShouldNotArrive")]
  ShouldNotArrive,
  /// Arithmetic Error: {0}
  #[error("ArithmeticErrors")]
  ArithmeticErrors(ArithErrors),
}

impl From<ArithErrors> for NovaError {
  fn from(e: ArithErrors) -> Self {
    Self::ArithmeticErrors(e)
  }
}