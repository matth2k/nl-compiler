use nl_compiler::{FromId, VerilogError, from_vast};
use safety_net::{Identifier, Instantiable, Logic, Net, Netlist, Parameter, assert_verilog_eq};
use std::{collections::HashMap, path::Path, rc::Rc};

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

fn compile(src: &str) -> Result<Rc<Netlist<Gate>>, VerilogError> {
    let incl: Vec<std::path::PathBuf> = vec![];
    let path = Path::new("top.v").to_path_buf();
    let (ast, _) = sv_parser::parse_sv_str(src, path, &HashMap::new(), &incl, true, false)?;
    from_vast(&ast)
}

fn roundtrip(src: &str) -> Result<String, VerilogError> {
    let netlist = compile(src)?;
    Ok(netlist.to_string())
}

#[test]
fn and_gate() {
    let src = "module and_test (
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
                       "
    .to_string();

    assert_verilog_eq!(src, roundtrip(&src).unwrap());
}

#[test]
fn and_const_gate() {
    let src = "module and_test (
                           b,
                           y
                       );
                         input b;
                         wire b;
                         output y;
                         wire y;
                       
                         AND _0_ (
                             .A(1'b1),
                             .B(b),
                             .Y(y)
                         );
                       
                       endmodule
                       "
    .to_string();

    assert_verilog_eq!(src, roundtrip(&src).unwrap());
}

#[test]
fn passthru() {
    let src = "module passthru (
                           b,
                           y
                       );
                         input b;
                         wire b;
                         output y;
                         wire y;
                       
                         assign y = b;
                       
                       endmodule
                       "
    .to_string();

    assert_verilog_eq!(src, roundtrip(&src).unwrap());
}

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

#[test]
fn bad_lut_name() {
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
                       
                         LUT #(
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

    let r = compile(&src);
    assert!(r.is_err());
    let e = r.err().unwrap();
    assert!(matches!(
        e,
        VerilogError::SafetyNetError(_, safety_net::Error::ParseError(_))
    ));
}

#[test]
fn bad_lut_input() {
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
                             .I00(a),
                             .I1(b),
                             .I2(c),
                             .O(y)
                         );
                       
                       endmodule
                       "
    .to_string();

    let r = compile(&src);
    assert!(r.is_err());
    let e = r.err().unwrap();
    assert!(matches!(e, VerilogError::Other(_, _)));
}

#[test]
fn assignment_chain() {
    let src = "module lut_test (
                           a,
                           y
                       );
                         input a;
                         wire a;
                         output y;
                         wire y;
                         wire tmp1;
                         wire tmp2;
                       
                         assign tmp1 = a;
                         assign tmp2 = tmp1;
                         assign y = tmp2;
                       
                       endmodule
                       "
    .to_string();

    let comp = "module lut_test (
                           a,
                           y
                       );
                         input a;
                         wire a;
                         output y;
                         wire y;
                       
                         assign y = a;
                       
                       endmodule
                       "
    .to_string();

    assert_verilog_eq!(comp, roundtrip(&src).unwrap());
}
