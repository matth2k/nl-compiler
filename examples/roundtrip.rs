use std::{
    collections::HashMap,
    io::{Read, stdin},
    path::{Path, PathBuf},
};

use clap::Parser;
use nl_compiler::result::{self, FromId};
use safety_net::{
    attribute::Parameter,
    circuit::{Identifier, Instantiable, Net},
};

/// A primitive gate in a digital circuit, such as AND, OR, NOT, etc.
#[derive(Debug, Clone)]
struct Gate {
    /// The name of the primitive
    name: Identifier,
    /// Input ports, order matters
    inputs: Vec<Net>,
    /// Output ports, order matters
    outputs: Vec<Net>,
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

    fn has_parameter(&self, _id: &Identifier) -> bool {
        false
    }

    fn get_parameter(&self, _id: &Identifier) -> Option<Parameter> {
        None
    }

    fn parameters(&self) -> impl Iterator<Item = (Identifier, Parameter)> {
        std::iter::empty()
    }
}

impl FromId for Gate {
    fn from_id(s: &Identifier) -> Result<Self, String> {
        match s.to_string().as_str() {
            "AND" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A".into(), "B".into()],
                outputs: vec!["Y".into()],
            }),
            "OR" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A".into(), "B".into()],
                outputs: vec!["Y".into()],
            }),
            "NOT" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A".into()],
                outputs: vec!["Y".into()],
            }),
            _ => Err(format!("Unknown primitive gate: {}", s)),
        }
    }
}

/// Parse structural verilog
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Path to input file. If not provided, reads from stdin
    input: Option<PathBuf>,
    /// Dump ast
    #[arg(short = 'd', long, default_value_t = false)]
    dump_ast: bool,
}

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

fn main() -> std::io::Result<()> {
    let args = Args::parse();
    let mut buf = String::new();

    let path: Option<PathBuf> = match args.input {
        Some(p) => {
            std::fs::File::open(&p)?.read_to_string(&mut buf)?;
            Some(p)
        }
        None => {
            stdin().read_to_string(&mut buf)?;
            None
        }
    };

    let ast = sv_parse_wrapper(&buf, path).map_err(std::io::Error::other)?;

    if args.dump_ast {
        println!("{ast}");
        return Ok(());
    }

    let netlist = result::from_ast::<Gate>(&ast).map_err(std::io::Error::other)?;

    println!("{}", netlist);

    Ok(())
}
