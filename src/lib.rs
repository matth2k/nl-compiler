#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_docs, unreachable_pub)]
/*!

`nl-compiler`

An experimental library for HDL frontends that can compile to [safety-net](https://crates.io/crates/safety-net) netlists.

*/
mod aig;
mod cells;
mod error;
mod verilog;

pub use aig::{U, from_aig, to_aig, write_aig};
pub use cells::FromId;
pub use error::{AigError, VerilogError};
pub use verilog::from_vast;
