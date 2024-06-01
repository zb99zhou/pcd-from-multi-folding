use ff::PrimeFieldBits;

pub fn truncate_field_bits<F: PrimeFieldBits>(elt: F, num_bits: usize) -> F {
  let bits = elt.to_le_bits();
  let mut res = F::ZERO;
  let mut coeff = F::ONE;
  for bit in bits[0..num_bits].into_iter() {
    if *bit {
      res += coeff;
    }
    coeff += coeff;
  }
  res
}
