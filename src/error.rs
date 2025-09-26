/*!

  Error types

*/

use crate::aig::U;
use thiserror::Error;

/// Errors for Verilog Compilation.
#[derive(Error, Debug)]
pub enum VerilogError {
    /// Errors in parsing literals/identifiers.
    #[error("Parsing error `{0}`")]
    ParseError(String),
    /// An error originating from `safety-net`.
    #[error("Safety net error `{0}`")]
    SafetyNetError(#[from] safety_net::error::Error),
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
