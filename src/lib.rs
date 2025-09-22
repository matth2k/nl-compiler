#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_docs, unreachable_pub)]
/*!

`nl-compiler`

An experimental library for HDL frontends that can compile to [safety-net](https://crates.io/crates/safety-net) netlists.

*/
pub mod aig;
pub mod cells;
pub mod verilog;
