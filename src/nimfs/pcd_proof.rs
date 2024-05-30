use crate::nimfs::ccs::cccs::{CCSWitness, CCCS};
use crate::nimfs::ccs::lcccs::LCCCS;
use crate::traits::Group;

pub struct PCDProof<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  pub r_W_secondary: CCSWitness<G2>,
  pub r_U_secondary: LCCCS<G2>,
  pub r_W_primary: CCSWitness<G1>,
  pub r_U_primary: LCCCS<G1>,
  pub l_w_secondary: CCSWitness<G2>,
  pub l_u_secondary: CCCS<G2>,

  pub zi_primary: Vec<G1::Scalar>,
  pub zi_secondary: Vec<G2::Scalar>,
}
