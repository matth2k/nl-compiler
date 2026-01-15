use std::{collections::HashMap, path::PathBuf};

use clap::Parser;
use flussab_aiger::ascii;
use nl_compiler::from_aig;
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

fn and() -> Gate {
    Gate {
        name: "AND".into(),
        inputs: vec!["A".into(), "B".into()],
        outputs: vec!["Y".into()],
        params: HashMap::new(),
    }
}

fn inv() -> Gate {
    Gate {
        name: "INV".into(),
        inputs: vec!["A".into()],
        outputs: vec!["Y".into()],
        params: HashMap::new(),
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
    /// Serialize
    #[cfg(feature = "serde")]
    #[arg(short = 's', long, default_value_t = false)]
    serialize: bool,
}

fn main() -> std::io::Result<()> {
    let args = Args::parse();

    let rdr = match args.input {
        Some(p) => {
            ascii::Parser::<u64>::from_read(std::fs::File::open(&p)?, ascii::Config::default())
                .map_err(std::io::Error::other)?
        }
        None => ascii::Parser::<u64>::from_read(std::io::stdin().lock(), ascii::Config::default())
            .map_err(std::io::Error::other)?,
    };

    let aig = rdr.parse().map_err(std::io::Error::other)?;

    if args.dump_ast {
        println!("{aig:?}");
        return Ok(());
    }

    let netlist = from_aig::<Gate>(&aig, and(), inv()).map_err(std::io::Error::other)?;

    netlist.verify().map_err(std::io::Error::other)?;

    let netlist = netlist.reclaim().unwrap();

    #[cfg(feature = "serde")]
    if args.serialize {
        netlist_serialize(netlist, std::io::stdout()).map_err(std::io::Error::other)?;
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
