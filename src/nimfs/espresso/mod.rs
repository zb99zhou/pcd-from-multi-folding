use ff::PrimeField;
use rayon::prelude::{ParallelIterator, ParallelSliceMut};

pub mod errors;
pub mod multilinear_polynomial;
pub mod virtual_polynomial;

pub mod sum_check;

// Given a vector of field elements {v_i}, compute the vector {v_i^(-1)}
pub fn batch_inversion<F: PrimeField>(v: &mut [F]) {
  batch_inversion_and_mul(v, &F::ONE);
}

// #[cfg(not(feature = "parallel"))]
// // Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}
// pub fn batch_inversion_and_mul<F: Field>(v: &mut [F], coeff: &F) {
//     serial_batch_inversion_and_mul(v, coeff);
// }
//
// #[cfg(feature = "parallel")]
// Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}
pub fn batch_inversion_and_mul<F: PrimeField>(v: &mut [F], coeff: &F) {
  // Divide the vector v evenly between all available cores
  let min_elements_per_thread = 1;
  let num_cpus_available = rayon::current_num_threads();
  let num_elems = v.len();
  let num_elem_per_thread = std::cmp::max(num_elems / num_cpus_available, min_elements_per_thread);

  // Batch invert in parallel, without copying the vector
  v.par_chunks_mut(num_elem_per_thread).for_each(|chunk| {
    serial_batch_inversion_and_mul(chunk, coeff);
  });
}

/// Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}.
/// This method is explicitly single-threaded.
fn serial_batch_inversion_and_mul<F: PrimeField>(v: &mut [F], coeff: &F) {
  // Montgomery’s Trick and Fast Implementation of Masked AES
  // Genelle, Prouff and Quisquater
  // Section 3.2
  // but with an optimization to multiply every element in the returned vector by coeff

  // First pass: compute [a, ab, abc, ...]
  let mut prod = Vec::with_capacity(v.len());
  let mut tmp = F::ONE;
  for f in v.iter().filter(|f| bool::from(!f.is_zero())) {
    tmp.mul_assign(f);
    prod.push(tmp);
  }

  // Invert `tmp`.
  tmp = tmp.invert().unwrap(); // Guaranteed to be nonzero.

  // Multiply product by coeff, so all inverses will be scaled by coeff
  tmp.mul_assign(coeff);

  // Second pass: iterate backwards to compute inverses
  for (f, s) in v.iter_mut()
        // Backwards
        .rev()
        // Ignore normalized elements
        .filter(|f| bool::from(!f.is_zero()))
        // Backwards, skip last element, fill in one for last term.
        .zip(prod.into_iter().rev().skip(1).chain(Some(F::ONE)))
  {
    // tmp := tmp * f; f := tmp * s = 1/f
    let new_tmp = tmp * *f;
    *f = tmp * s;
    tmp = new_tmp;
  }
}
