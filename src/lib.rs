//! This library implements the paper "Proof-Carrying Data from Multi-folding Schemes" (https://eprint.iacr.org/2023/1282)
#![allow(dead_code)]
#![deny(warnings, future_incompatible, nonstandard_style, rust_2018_idioms)]
#![allow(non_snake_case)]
#![allow(clippy::type_complexity)]
// #![forbid(unsafe_code)]
#![allow(clippy::upper_case_acronyms)]

// private modules
mod bellpepper;
mod constants;
mod multi_hash_circuit;
mod nifs;
mod nimfs;
mod pcd_aux_circuit;
mod pcd_circuit;
mod utils;

// public modules
pub mod compress_snark;
pub mod errors;
pub mod gadgets;
pub mod pcd_node;
pub mod provider;
pub mod traits;

pub use gadgets::utils::scalar_as_base;
pub use utils::*;
