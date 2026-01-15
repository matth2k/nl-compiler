![](https://github.com/matth2k/nl-compiler/actions/workflows/rust.yml/badge.svg)
[![Docs](https://img.shields.io/badge/docs-github--pages-blue)](https://matth2k.github.io/nl-compiler/)
[![crates.io](https://img.shields.io/badge/crates.io-github--pages-blue)](https://crates.io/crates/nl-compiler)

# `nl-compiler`: Frontend Compiler for [Safety-Net](https://github.com/matth2k/safety-net)

## Getting Started

Below is a minimal example to get you started:

```verilog
module and_test (
    a,
    b,
    y
);
  input a;
  wire a;
  input b;
  wire b;
  output y;
  wire y;

  AND _0_ (
      .A(a),
      .B(b),
      .Y(y)
  );

endmodule
```

Save the above file to `and.v`.

`cargo run --example roundtrip -- and.v`

Also, take a look at some of the [tests](https://github.com/matth2k/nl-compiler/blob/main/tests/verilog.rs):

```rust
#[test]
fn mux_lut() {
    let src = "module lut_test (
                           a,
                           b,
                           c,
                           y
                       );
                         input a;
                         wire a;
                         input b;
                         wire b;
                         input c;
                         wire c;
                         output y;
                         wire y;
                       
                         LUT3 #(
                             .INIT(8'b11001010)
                         ) _0_ (
                             .I0(a),
                             .I1(b),
                             .I2(c),
                             .O(y)
                         );
                       
                       endmodule
                       "
    .to_string();

    assert_verilog_eq!(src, roundtrip(&src).unwrap());
}
```
