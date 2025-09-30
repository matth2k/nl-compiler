/*!

  Error types

*/

use crate::aig::U;
use std::num::ParseIntError;
use sv_parser::Locate;
use thiserror::Error;

/// Errors for Verilog Compilation.
#[derive(Error, Debug)]
pub enum VerilogError {
    /// Errors in parsing ints.
    #[error("Parsing int error {0} `{1:?}`")]
    ParseIntError(ParseIntError, Locate),
    /// Errors in parsing string.
    #[error("Parsing string error {0:?}")]
    ParseStrError(Locate),
    /// A RefNode that was not expected to be compiled.
    #[error("Unexpected RefNode {0:?} `{1}`")]
    UnexpectedRefNode(Locate, String),
    /// A RefNode that is missing.
    #[error("Missing RefNode `{0}`")]
    MissingRefNode(String),
    /// An error originating from `safety-net`.
    #[error(" `{1}` : {0:?}")]
    SafetyNetError(Option<Locate>, safety_net::error::Error),
    /// An error originating from `sv-parser`.
    #[error("{0:?}")]
    ParserError(#[from] sv_parser::Error),
    /// Any other compilation error
    #[error(" `{1}` : {0:?}")]
    Other(Option<Locate>, String),
}

/// Errors for AIG Compilation.
#[derive(Error, Debug)]
pub enum AigError {
    /// Contains bad state properties.
    #[error("Contains bad state properties `{0:?}`")]
    ContainsBadStates(Vec<U>),
    /// Contains latches.
    #[error("Contains latches `{0:?}`")]
    ContainsLatches(Vec<U>),
    /// An error originating from `safety-net`.
    #[error("Safety net error `{0}`")]
    SafetyNetError(#[from] safety_net::error::Error),
}
