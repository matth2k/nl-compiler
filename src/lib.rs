#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_docs, unreachable_pub)]
#![recursion_limit = "256"]
/*!

`nl-compiler`

An experimental library for HDL frontends that can compile to [safety-net](https://crates.io/crates/safety-net) netlists.

*/
mod aig;
mod cells;
mod error;
mod verilog;

pub use aig::{U, from_aig, from_aig_bytes, to_aig, write_aig};
pub use cells::FromId;
pub use error::{AigError, VerilogError};
pub use verilog::{from_vast, from_vast_overrides};
