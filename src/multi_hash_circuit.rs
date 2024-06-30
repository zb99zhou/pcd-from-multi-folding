#![allow(non_snake_case)]

use crate::traits::circuit::PCDStepCircuit;
use bellpepper::gadgets::sha256::sha256;
use bellpepper::gadgets::Assignment;
use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::{AllocatedNum, Num};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeFieldBits;
use std::marker::PhantomData;
use std::ops::Index;

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;

#[derive(Clone, Debug)]
pub struct MultiHashCircuit<F: PrimeFieldBits, const ARITY: usize, const R: usize> {
  _p: PhantomData<F>,
}

impl<F: PrimeFieldBits, const ARITY: usize, const R: usize> MultiHashCircuit<F, ARITY, R> {
  pub fn new() -> Self {
    Self { _p: PhantomData }
  }
}

impl<F: PrimeFieldBits, const ARITY: usize, const R: usize> PCDStepCircuit<F, ARITY, R>
  for MultiHashCircuit<F, ARITY, R>
{
  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    z: &[&[AllocatedNum<F>]],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    let mut z_out: Vec<AllocatedNum<F>> = Vec::new();
    let mut z_bits: Vec<Boolean> = Vec::new();

    for (i, &ref zi) in z.iter().enumerate() {
      assert_eq!(zi.len(), 1);
      let bit_values = zi
        .index(0)
        .to_bits_le_strict(cs.namespace(|| format!("z{i} to bits")))?;

      let mut bits_temp = bit_values.clone();
      bits_temp.resize(256, Boolean::Constant(false));
      z_bits.append(&mut bits_temp);
    }

    let hash_bits = sha256(cs.namespace(|| "sha256"), &z_bits)?;

    // iteratively use hash to increase the size of the test circuit
    // let num_iterations = 0;
    // for i in 0..num_iterations {
    //   let namespace = format!("sha256_iteration_{}", i);
    //   hash_bits = sha256(cs.namespace(|| namespace), &hash_bits)?;
    // }

    for (i, hash_bits) in hash_bits.chunks(256_usize).enumerate() {
      let mut num = Num::<F>::zero();
      let mut coeff = F::ONE;
      for bit in hash_bits {
        num = num.add_bool_with_coeff(CS::one(), bit, coeff);

        coeff = coeff.double();
      }

      let hash = AllocatedNum::alloc(cs.namespace(|| format!("input {i}")), || {
        Ok(*num.get_value().get()?)
      })?;

      // num * 1 = hash
      cs.enforce(
        || format!("packing constraint {i}"),
        |_| num.lc(F::ONE),
        |lc| lc + CS::one(),
        |lc| lc + hash.get_variable(),
      );

      z_out.push(hash);
    }

    Ok(z_out)
  }
}

mod test {
  use bellpepper_core::num::AllocatedNum;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use bellpepper_core::{ConstraintSystem, SynthesisError};
  // use digest::Digest;
  use ff::{Field, PrimeField};
  // use sha2::Sha256;
  use crate::multi_hash_circuit::MultiHashCircuit;
  use crate::traits::circuit::PCDStepCircuit;
  use crate::traits::Group;

  fn test_multi_hash_circuit_with<G, const ARITY: usize, const R: usize>()
  where
    G: Group,
  {
    let multi_hash_circuit = MultiHashCircuit::<G::Base, ARITY, R>::new();
    let mut test_cs: TestConstraintSystem<<G as Group>::Base> = TestConstraintSystem::new();
    let zi = vec![G::Base::ZERO];
    let z = vec![zi.clone(), zi.clone()];
    let z_i = (0..R)
      .map(|i| {
        (0..ARITY)
          .map(|j| {
            AllocatedNum::alloc(
              test_cs.namespace(|| format!("zi is {j}th_io for {i}th lcccs")),
              || Ok(z[i][j]),
            )
          })
          .collect::<Result<Vec<_>, SynthesisError>>()
      })
      .collect::<Result<Vec<Vec<AllocatedNum<G::Base>>>, SynthesisError>>()
      .unwrap();

    let mut hash_input: Vec<u8> = Vec::new();
    for zi in &z_i {
      assert_eq!(zi.len(), 1);
      let mut Bytes_temp = zi[0].get_value().unwrap().to_repr().as_ref().to_vec();
      hash_input.append(&mut Bytes_temp);
    }
    // dbg!(hash_input.clone());
    // let mut hasher = Sha256::new();
    // hasher.update(&hash_input);
    // let hash_result = hasher.finalize();
    // let mut hash_rev_vec = Vec::<u8>::new();
    // for hash in hash_result.iter() {
    //     hash_rev_vec.push(hash.reverse_bits());
    // }
    let result = multi_hash_circuit.synthesize(
      &mut test_cs,
      &z_i.iter().map(|z| &z[..]).collect::<Vec<_>>(),
    );
    println!("number of constraints: {}", test_cs.num_constraints());
    // let ans = result.as_ref().unwrap();
    // assert_eq!(ans.len(), 1);
    // let binding = ans[0].get_value().unwrap().to_repr();
    // let res = binding.as_ref();
    // // dbg!(hash_result);
    // println!("out of circuit");
    // hash_rev_vec.iter().for_each(|a| println!("{:08b}", a));
    // // dbg!(res);
    // println!("from circuit");
    // res.iter().for_each(|a| println!("{:08b}", a));
    assert!(result.is_ok());
    assert!(test_cs.is_satisfied())
  }

  #[test]
  fn test_multi_hash_circuit() {
    type G = pasta_curves::pallas::Point;
    const ARITY: usize = 1;
    const R: usize = 2; // arity in PCD

    test_multi_hash_circuit_with::<G, ARITY, R>()
  }
}
