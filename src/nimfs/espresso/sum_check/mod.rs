// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

//! This module implements the sum check protocol.

use ff::PrimeField;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::errors::NovaError;
use crate::nimfs::espresso::virtual_polynomial::{VPAuxInfo, VirtualPolynomial};
use crate::spartan::polys::multilinear::MultiLinearPolynomial;
use crate::traits::{Group, TranscriptEngineTrait};
use structs::{IOPProof, IOPProverState, IOPVerifierState};

mod prover;
pub mod structs;
pub mod verifier;

/// Trait for doing sum check protocols.
pub trait SumCheck<C: Group> {
  type VirtualPolynomial;
  type VPAuxInfo;
  type MultilinearExtension;

  type SumCheckProof: Clone + Debug + PartialEq;
  type Transcript: TranscriptEngineTrait<C>;
  type SumCheckSubClaim: Clone + Debug + Default + PartialEq;

  /// Extract sum from the proof
  fn extract_sum(proof: &Self::SumCheckProof) -> C::Scalar;

  /// Initialize the system with a transcript
  ///
  /// This function is optional -- in the case where a SumCheck is
  /// an building block for a more complex protocol, the transcript
  /// may be initialized by this complex protocol, and passed to the
  /// SumCheck prover/verifier.
  // fn init_transcript() -> Self::Transcript;

  /// Generate proof of the sum of polynomial over {0,1}^`num_vars`
  ///
  /// The polynomial is represented in the form of a VirtualPolynomial.
  fn prove(
    poly: &Self::VirtualPolynomial,
    transcript: &mut Self::Transcript,
  ) -> Result<Self::SumCheckProof, NovaError>;

  /// Verify the claimed sum using the proof
  fn verify(
    sum: C::Scalar,
    proof: &Self::SumCheckProof,
    aux_info: &Self::VPAuxInfo,
    transcript: &mut Self::Transcript,
  ) -> Result<Self::SumCheckSubClaim, NovaError>;
}

/// Trait for sum check protocol prover side APIs.
pub trait SumCheckProver<F: PrimeField>
where
  Self: Sized,
{
  type VirtualPolynomial;
  type ProverMessage;

  /// Initialize the prover state to argue for the sum of the input polynomial
  /// over {0,1}^`num_vars`.
  fn prover_init(polynomial: &Self::VirtualPolynomial) -> Result<Self, NovaError>;

  /// Receive message from verifier, generate prover message, and proceed to
  /// next round.
  ///
  /// Main algorithm used is from section 3.2 of [XZZPS19](https://eprint.iacr.org/2019/317.pdf#subsection.3.2).
  fn prove_round_and_update_state(
    &mut self,
    challenge: &Option<F>,
  ) -> Result<Self::ProverMessage, NovaError>;
}

/// Trait for sum check protocol verifier side APIs.
pub trait SumCheckVerifier<F: PrimeField> {
  type VPAuxInfo;
  type ProverMessage;
  type Challenge;
  type Transcript;
  type SumCheckSubClaim;

  /// Initialize the verifier's state.
  fn verifier_init(index_info: &Self::VPAuxInfo) -> Self;

  /// Run verifier for the current round, given a prover message.
  ///
  /// Note that `verify_round_and_update_state` only samples and stores
  /// challenges; and update the verifier's state accordingly. The actual
  /// verifications are deferred (in batch) to `check_and_generate_subclaim`
  /// at the last step.
  fn verify_round_and_update_state(
    &mut self,
    prover_msg: &Self::ProverMessage,
    transcript: &mut Self::Transcript,
  ) -> Result<Self::Challenge, NovaError>;

  /// This function verifies the deferred checks in the interactive version of
  /// the protocol; and generate the subclaim. Returns an error if the
  /// proof failed to verify.
  ///
  /// If the asserted sum is correct, then the multilinear polynomial
  /// evaluated at `subclaim.point` will be `subclaim.expected_evaluation`.
  /// Otherwise, it is highly unlikely that those two will be equal.
  /// Larger field size guarantees smaller soundness error.
  fn check_and_generate_subclaim(
    &self,
    asserted_sum: &F,
  ) -> Result<Self::SumCheckSubClaim, NovaError>;
}

/// A SumCheckSubClaim is a claim generated by the verifier at the end of
/// verification when it is convinced.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SumCheckSubClaim<F: PrimeField> {
  /// the multi-dimensional point that this multilinear extension is evaluated
  /// to
  pub point: Vec<F>,
  /// the expected evaluation
  pub expected_evaluation: F,
}

#[derive(Clone, Debug, Default, Copy, PartialEq, Eq)]
/// Struct for PolyIOP protocol.
/// It has an associated type `F` that defines the prime field the multi-variate
/// polynomial operates on.
///
/// An PolyIOP may be instantiated with one of the following:
/// - SumCheck protocol.
/// - ZeroCheck protocol.
/// - PermutationCheck protocol.
///
/// Those individual protocol may have similar or identical APIs.
/// The systematic way to invoke specific protocol is, for example
///     `<PolyIOP<F> as SumCheck<F>>::prove()`
pub struct PolyIOP<F: PrimeField> {
  /// Associated field
  #[doc(hidden)]
  phantom: PhantomData<F>,
}

impl<C: Group> SumCheck<C> for PolyIOP<C::Scalar> {
  type VirtualPolynomial = VirtualPolynomial<C::Scalar>;
  type VPAuxInfo = VPAuxInfo<C::Scalar>;
  type MultilinearExtension = Arc<MultiLinearPolynomial<C::Scalar>>;
  type SumCheckProof = IOPProof<C>;
  type Transcript = C::TE;
  type SumCheckSubClaim = SumCheckSubClaim<C::Scalar>;

  fn extract_sum(proof: &Self::SumCheckProof) -> C::Scalar {
    proof.proofs[0].evaluations[0] + proof.proofs[0].evaluations[1]
  }

  fn prove(
    poly: &Self::VirtualPolynomial,
    transcript: &mut Self::Transcript,
  ) -> Result<Self::SumCheckProof, NovaError> {
    transcript.absorb(b"aux info", &poly.aux_info);

    let mut prover_state = IOPProverState::prover_init(poly)?;
    let mut challenge = None;
    let mut prover_msgs = Vec::with_capacity(poly.aux_info.num_variables);
    for _ in 0..poly.aux_info.num_variables {
      let prover_msg = prover_state.prove_round_and_update_state(&challenge)?;
      transcript.absorb(b"prover msg", &prover_msg);
      prover_msgs.push(prover_msg);
      challenge = Some(transcript.squeeze(b"Internal round")?);
    }
    // pushing the last challenge point to the state
    if let Some(p) = challenge {
      prover_state.challenges.push(p)
    };

    Ok(IOPProof {
      point: prover_state.challenges,
      proofs: prover_msgs,
    })
  }

  fn verify(
    claimed_sum: C::Scalar,
    proof: &Self::SumCheckProof,
    aux_info: &Self::VPAuxInfo,
    transcript: &mut Self::Transcript,
  ) -> Result<Self::SumCheckSubClaim, NovaError> {
    transcript.absorb(b"aux info", aux_info);

    let mut verifier_state = IOPVerifierState::verifier_init(aux_info);
    for i in 0..aux_info.num_variables {
      let prover_msg = proof.proofs.get(i).expect("proof is incomplete");
      transcript.absorb(b"prover msg", prover_msg);
      verifier_state.verify_round_and_update_state(prover_msg, transcript)?;
    }

    verifier_state.check_and_generate_subclaim(&claimed_sum)
  }
}
