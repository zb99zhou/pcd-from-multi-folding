//! This module implements traits using the following configuration:
//! `CommitmentEngine` with Pedersen's commitments
//! `Group` with pasta curves and BN256/Grumpkin
//! `RO` traits with Poseidon
//! `EvaluationEngine` with an IPA-based polynomial evaluation argument

pub mod bn256_grumpkin;
pub mod ipa_pc;
pub mod keccak;
pub mod pasta;
pub mod pedersen;
pub mod poseidon;
pub mod secp_secq;

use ff::PrimeField;
use pasta_curves::{self, arithmetic::CurveAffine, group::Group as AnotherGroup};

/// Native implementation of fast multiexp
/// Adapted from zcash/halo2
fn cpu_multiexp_serial<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C], acc: &mut C::Curve) {
  let coeffs: Vec<_> = coeffs.iter().map(|a| a.to_repr()).collect();

  let c = if bases.len() < 4 {
    1
  } else if bases.len() < 32 {
    3
  } else {
    (f64::from(bases.len() as u32)).ln().ceil() as usize
  };

  fn get_at<F: PrimeField>(segment: usize, c: usize, bytes: &F::Repr) -> usize {
    let skip_bits = segment * c;
    let skip_bytes = skip_bits / 8;

    if skip_bytes >= 32 {
      return 0;
    }

    let mut v = [0; 8];
    for (v, o) in v.iter_mut().zip(bytes.as_ref()[skip_bytes..].iter()) {
      *v = *o;
    }

    let mut tmp = u64::from_le_bytes(v);
    tmp >>= skip_bits - (skip_bytes * 8);
    tmp %= 1 << c;

    tmp as usize
  }

  let segments = (256 / c) + 1;

  for current_segment in (0..segments).rev() {
    for _ in 0..c {
      *acc = acc.double();
    }

    #[derive(Clone, Copy)]
    enum Bucket<C: CurveAffine> {
      None,
      Affine(C),
      Projective(C::Curve),
    }

    impl<C: CurveAffine> Bucket<C> {
      fn add_assign(&mut self, other: &C) {
        *self = match *self {
          Bucket::None => Bucket::Affine(*other),
          Bucket::Affine(a) => Bucket::Projective(a + *other),
          Bucket::Projective(mut a) => {
            a += *other;
            Bucket::Projective(a)
          }
        }
      }

      fn add(self, mut other: C::Curve) -> C::Curve {
        match self {
          Bucket::None => other,
          Bucket::Affine(a) => {
            other += a;
            other
          }
          Bucket::Projective(a) => other + a,
        }
      }
    }

    let mut buckets: Vec<Bucket<C>> = vec![Bucket::None; (1 << c) - 1];

    for (coeff, base) in coeffs.iter().zip(bases.iter()) {
      let coeff = get_at::<C::Scalar>(current_segment, c, coeff);
      if coeff != 0 {
        buckets[coeff - 1].add_assign(base);
      }
    }

    // Summation by parts
    // e.g. 3a + 2b + 1c = a +
    //                    (a) + b +
    //                    ((a) + b) + c
    let mut running_sum = C::Curve::identity();
    for exp in buckets.into_iter().rev() {
      running_sum = exp.add(running_sum);
      *acc += &running_sum;
    }
  }
}

/// Performs a multi-exponentiation operation without GPU acceleration.
///
/// This function will panic if coeffs and bases have a different length.
///
/// This will use multithreading if beneficial.
/// Adapted from zcash/halo2
pub(crate) fn cpu_best_multiexp<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
  assert_eq!(coeffs.len(), bases.len());

  let num_threads = rayon::current_num_threads();
  if coeffs.len() > num_threads {
    let chunk = coeffs.len() / num_threads;
    let num_chunks = coeffs.chunks(chunk).len();
    let mut results = vec![C::Curve::identity(); num_chunks];
    rayon::scope(|scope| {
      for ((coeffs, bases), acc) in coeffs
        .chunks(chunk)
        .zip(bases.chunks(chunk))
        .zip(results.iter_mut())
      {
        scope.spawn(move |_| {
          cpu_multiexp_serial(coeffs, bases, acc);
        });
      }
    });
    results.iter().fold(C::Curve::identity(), |a, b| a + b)
  } else {
    let mut acc = C::Curve::identity();
    cpu_multiexp_serial(coeffs, bases, &mut acc);
    acc
  }
}

/// Curve ops
/// This implementation behaves in ways specific to the halo2curves suite of curves in:
// - to_coordinates,
// - vartime_multiscalar_mul, where it does not call into accelerated implementations.
// A specific reimplementation exists for the pasta curves in their own module.
#[macro_export]
macro_rules! impl_traits {
  (
    $name:ident,
    $name_compressed:ident,
    $name_curve:ident,
    $name_curve_affine:ident,
    $order_str:literal
  ) => {
    impl Group for $name::Point {
      type Base = $name::Base;
      type Scalar = $name::Scalar;
      type CompressedGroupElement = $name_compressed;
      type PreprocessedGroupElement = $name::Affine;
      type RO = PoseidonRO<Self::Base, Self::Scalar>;
      type ROCircuit = PoseidonROCircuit<Self::Base>;
      type FoldTE = PoseidonTranscript<Self>;
      type FoldTECircuit = PoseidonTranscriptCircuit<Self>;
      type CompressTE = Keccak256Transcript<Self>;
      type CE = CommitmentEngine<Self>;

      fn vartime_multiscalar_mul(
        scalars: &[Self::Scalar],
        bases: &[Self::PreprocessedGroupElement],
      ) -> Self {
        cpu_best_multiexp(scalars, bases)
      }

      fn preprocessed(&self) -> Self::PreprocessedGroupElement {
        self.to_affine()
      }

      fn compress(&self) -> Self::CompressedGroupElement {
        self.to_bytes()
      }

      fn from_label(label: &'static [u8], n: usize) -> Vec<Self::PreprocessedGroupElement> {
        let mut shake = Shake256::default();
        shake.update(label);
        let mut reader = shake.finalize_xof();
        let mut uniform_bytes_vec = Vec::new();
        for _ in 0..n {
          let mut uniform_bytes = [0u8; 32];
          reader.read_exact(&mut uniform_bytes).unwrap();
          uniform_bytes_vec.push(uniform_bytes);
        }
        let gens_proj: Vec<$name_curve> = (0..n)
          .into_par_iter()
          .map(|i| {
            let hash = $name_curve::hash_to_curve("from_uniform_bytes");
            hash(&uniform_bytes_vec[i])
          })
          .collect();

        let num_threads = rayon::current_num_threads();
        if gens_proj.len() > num_threads {
          let chunk = (gens_proj.len() as f64 / num_threads as f64).ceil() as usize;
          (0..num_threads)
            .into_par_iter()
            .flat_map(|i| {
              let start = i * chunk;
              let end = if i == num_threads - 1 {
                gens_proj.len()
              } else {
                core::cmp::min((i + 1) * chunk, gens_proj.len())
              };
              if end > start {
                let mut gens = vec![$name_curve_affine::identity(); end - start];
                <Self as Curve>::batch_normalize(&gens_proj[start..end], &mut gens);
                gens
              } else {
                vec![]
              }
            })
            .collect()
        } else {
          let mut gens = vec![$name_curve_affine::identity(); n];
          <Self as Curve>::batch_normalize(&gens_proj, &mut gens);
          gens
        }
      }

      fn to_coordinates(&self) -> (Self::Base, Self::Base, bool) {
        // see: grumpkin implementation at src/provider/bn256_grumpkin.rs
        let coordinates = self.to_affine().coordinates();
        if coordinates.is_some().unwrap_u8() == 1
          && (Self::PreprocessedGroupElement::identity() != self.to_affine())
        {
          (*coordinates.unwrap().x(), *coordinates.unwrap().y(), false)
        } else {
          (Self::Base::zero(), Self::Base::zero(), true)
        }
      }

      fn get_curve_params() -> (Self::Base, Self::Base, BigInt) {
        let A = $name::Point::a();
        let B = $name::Point::b();
        let order = BigInt::from_str_radix($order_str, 16).unwrap();

        (A, B, order)
      }

      fn zero() -> Self {
        $name::Point::identity()
      }

      fn get_generator() -> Self {
        $name::Point::generator()
      }
    }

    impl PrimeFieldExt for $name::Scalar {
      fn from_uniform(bytes: &[u8]) -> Self {
        let mut bytes_arr = [0u8; 64];
        bytes_arr[64 - bytes.len()..64].copy_from_slice(bytes);
        $name::Scalar::from_uniform_bytes(&bytes_arr)
      }
    }

    impl<G: Group> TranscriptReprTrait<G> for $name_compressed {
      fn to_transcript_bytes(&self) -> Vec<u8> {
        self.as_ref().to_vec()
      }

      fn to_transcript_scalars(&self) -> Vec<G::Scalar> {
        vec![G::Scalar::from_uniform(self.as_ref())]
      }
    }

    impl CompressedGroup for $name_compressed {
      type GroupElement = $name::Point;

      fn decompress(&self) -> Option<$name::Point> {
        Some($name_curve::from_bytes(&self).unwrap())
      }
    }
  };
}
