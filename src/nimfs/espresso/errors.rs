// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

//! Error module.

/// A `enum` specifying the possible failure modes of the arithmetics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArithErrors {
    /// Invalid parameters: {0}
    InvalidParameters(String),
    /// Should not arrive to this point
    ShouldNotArrive,
}
