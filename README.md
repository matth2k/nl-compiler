![](https://github.com/matth2k/nl-compiler/actions/workflows/rust.yml/badge.svg)
[![Docs](https://img.shields.io/badge/docs-github--pages-blue)](https://matth2k.github.io/nl-compiler/)
[![crates.io](https://img.shields.io/badge/crates.io-github--pages-blue)](https://crates.io/crates/nl-compiler)

# `nl-compiler`: Verilog Frontend Compilation

nl-compiler provides frontend compilation for Verilog netlists. The output format is a memory-safe netlist data structure called [safety-net](https://github.com/matth2k/safety-net).

## Getting Started

Getting a compilation flow working quickly is easy with nl-compiler. Here are the basic steps to follow:

### 1. Produce a Verilog AST with sv-parser

Use the [sv-parser crate](https://crates.io/crates/sv-parser) to generate an AST for your netlist:

```rust
/// A wrapper for parsing verilog at file `path` with content `s`
fn sv_parse_wrapper(
    s: &str,
    path: Option<PathBuf>,
) -> Result<sv_parser::SyntaxTree, sv_parser::Error> {
    let incl: Vec<std::path::PathBuf> = vec![];
    let path = path.unwrap_or(Path::new("top.v").to_path_buf());
    match sv_parser::parse_sv_str(s, path, &HashMap::new(), &incl, true, false) {
        Ok((ast, _defs)) => Ok(ast),
        Err(e) => Err(e),
    }
}
```

### 2. Define a Cell Library

Safety-Net netlists are generic to the cell library under an [Instantiable] interface. Simple create a cell library that implements this interface. This is where the most of the boiler-plate comes from.

```rust
use safety_net::{Net, Identifier, Instantiable}
/// A primitive AND2 or INV gamte
#[derive(Debug, Clone)]
struct Gate {
    /// The name of the primitive
    name: Identifier,
    /// Input ports, order matters
    inputs: Vec<Net>,
    /// Output ports, order matters
    outputs: Vec<Net>,
    /// Parameters
    params: HashMap<Identifier, Parameter>,
}


impl FromId for Gate {
    fn from_id(s: &Identifier) -> Result<Self, safety_net::Error> {
        match s.to_string().as_str() {
            "AND" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A".into(), "B".into()],
                outputs: vec!["Y".into()],
                params: HashMap::new(),
            }),
            "INV" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A".into()],
                outputs: vec!["ZN".into()],
                params: HashMap::new(),
            }),
            _ => Err(safety_net::Error::ParseError(format!(
                "Unknown primitive gate: {}",
                s
            ))),
        }
    }
}

impl Instantiable for Gate {
    fn get_name(&self) -> &Identifier {
        &self.name
    }

    fn get_input_ports(&self) -> impl IntoIterator<Item = &Net> {
        &self.inputs
    }

    fn get_output_ports(&self) -> impl IntoIterator<Item = &Net> {
        &self.outputs
    }

    fn has_parameter(&self, id: &Identifier) -> bool {
        self.params.contains_key(id)
    }

    fn get_parameter(&self, id: &Identifier) -> Option<Parameter> {
        self.params.get(id).cloned()
    }

    fn set_parameter(&mut self, id: &Identifier, val: Parameter) -> Option<Parameter> {
        self.params.insert(id.clone(), val)
    }

    fn parameters(&self) -> impl Iterator<Item = (Identifier, Parameter)> {
        self.params.clone().into_iter()
    }

    fn from_constant(val: Logic) -> Option<Self> {
        match val {
            Logic::False => Some(Gate {
                name: "GND".into(),
                inputs: vec![],
                outputs: vec!["Y".into()],
                params: HashMap::new(),
            }),
            Logic::True => Some(Gate {
                name: "VDD".into(),
                inputs: vec![],
                outputs: vec!["Y".into()],
                params: HashMap::new(),
            }),
            _ => None,
        }
    }
}
```

### 3. Compile!

```rust

    let buf = // Collect the source Verilog into a string

    let ast = sv_parse_wrapper(&buf, path).map_err(std::io::Error::other)?;

    let netlist = match from_vast::<Gate>(&ast) {
        Ok(nl) => nl,
        Err(e) => {
            eprintln!("{e}");
            return Err(std::io::Error::other(e));
        }
    };

    netlist.verify().map_err(std::io::Error::other)?;

```

## Example Netlist

Here is an example netlist to get you started:

```verilog
module and_test (
    input wire a,
    input wire b,
    input wire y
);

  AND _0_ (
      .A(a),
      .B(b),
      .Y(y)
  );

endmodule
```

Save the above file to `and.v` and try running it on the baseline implementation.

`cargo run --example roundtrip -- and.v`

## Testing

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
