use std::{
    collections::HashMap,
    io::{Read, stdin},
    path::{Path, PathBuf},
};

use clap::Parser;
use nl_compiler::{AigError, FromId, from_vast, to_aig, write_aig};
#[cfg(feature = "serde")]
use safety_net::serde::netlist_serialize;
use safety_net::{Identifier, Instantiable, Logic, Net, Parameter};

/// A primitive gate in a digital circuit, such as AND, OR, NOT, etc.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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

    fn get_constant(&self) -> Option<Logic> {
        match self.name.to_string().as_str() {
            "GND" => Some(Logic::False),
            "VDD" => Some(Logic::True),
            _ => None,
        }
    }

    fn is_seq(&self) -> bool {
        false
    }
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
            "OR" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A".into(), "B".into()],
                outputs: vec!["Y".into()],
                params: HashMap::new(),
            }),
            "NOT" | "INV" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A".into()],
                outputs: vec!["Y".into()],
                params: HashMap::new(),
            }),
            "LUT1" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["I0".into()],
                outputs: vec!["O".into()],
                params: HashMap::new(),
            }),
            "LUT2" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["I0".into(), "I1".into()],
                outputs: vec!["O".into()],
                params: HashMap::new(),
            }),
            "LUT3" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["I0".into(), "I1".into(), "I2".into()],
                outputs: vec!["O".into()],
                params: HashMap::new(),
            }),
            "LUT4" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["I0".into(), "I1".into(), "I2".into(), "I3".into()],
                outputs: vec!["O".into()],
                params: HashMap::new(),
            }),
            "LUT5" => Ok(Gate {
                name: s.clone(),
                inputs: vec![
                    "I0".into(),
                    "I1".into(),
                    "I2".into(),
                    "I3".into(),
                    "I4".into(),
                ],
                outputs: vec!["O".into()],
                params: HashMap::new(),
            }),
            "LUT6" => Ok(Gate {
                name: s.clone(),
                inputs: vec![
                    "I0".into(),
                    "I1".into(),
                    "I2".into(),
                    "I3".into(),
                    "I4".into(),
                    "I5".into(),
                ],
                outputs: vec!["O".into()],
                params: HashMap::new(),
            }),
            "FDRE" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["C".into(), "CE".into(), "D".into(), "R".into()],
                outputs: vec!["Q".into()],
                params: HashMap::new(),
            }),
            "NOR2_X1" | "NAND2_X1" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A1".into(), "A2".into()],
                outputs: vec!["ZN".into()],
                params: HashMap::new(),
            }),
            "INV_X1" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A".into()],
                outputs: vec!["ZN".into()],
                params: HashMap::new(),
            }),
            "AOI21_X1" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A".into(), "B1".into(), "B2".into()],
                outputs: vec!["ZN".into()],
                params: HashMap::new(),
            }),
            "AOI22_X1" => Ok(Gate {
                name: s.clone(),
                inputs: vec!["A1".into(), "A2".into(), "B1".into(), "B2".into()],
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

impl Gate {
    /// Returns true if the gate is an inverter
    fn is_inverter(&self) -> bool {
        let name = self.get_name().to_string();
        name == "NOT" || name == "INV" || name == "INV_X1"
    }

    /// Returns true if the gate is an AND gate
    fn is_and(&self) -> bool {
        let name = self.get_name().to_string();
        name == "AND" || name == "AND2_X1"
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
    /// Write output as an AIG
    #[arg(short = 'c', long, default_value_t = false)]
    convert_aig: bool,
    /// Serialize
    #[cfg(feature = "serde")]
    #[arg(short = 's', long, default_value_t = false)]
    serialize: bool,
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

    let netlist = from_vast::<Gate>(&ast).map_err(std::io::Error::other)?;

    netlist.verify().map_err(std::io::Error::other)?;

    #[cfg(feature = "serde")]
    if args.serialize {
        let netlist = netlist.reclaim().unwrap();
        netlist_serialize(netlist, std::io::stdout()).map_err(std::io::Error::other)?;
        return Ok(());
    }

    if args.convert_aig {
        let aig =
            to_aig(&netlist, |g| g.is_and(), |g| g.is_inverter()).map_err(std::io::Error::other)?;

        write_aig(&aig, std::io::stdout().lock()).map_err(|e| match e {
            AigError::IoError(ioe) => ioe,
            _ => std::io::Error::other(e),
        })?;

        return Ok(());
    }

    eprintln!("{netlist}");
    let analysis = netlist
        .get_analysis::<safety_net::MultiDiGraph<_>>()
        .unwrap();
    let graph = analysis.get_graph();
    let dot = petgraph::dot::Dot::with_config(graph, &[]);
    println!("{dot}");

    Ok(())
}
