/*!

  The consumed AST

*/

use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use safety_net::{
    attribute::Parameter,
    circuit::{Identifier, Instantiable, Net},
    logic::Logic,
    netlist::{DrivenNet, NetRef, Netlist},
};
use sv_parser::{Locate, NodeEvent, RefNode, unwrap_node};

/// A trait to specify how to map primitive instantiation names ([Identifier]s) to the instance [Instantiable] type.
pub trait FromId: Sized {
    /// Maps primitive instantiation names ([Identifier]s) to the instance [Instantiable] type.
    fn from_id(s: &Identifier) -> Result<Self, String>;
}

/// From a AST node, read in the identifier from the source location
fn get_identifier(node: RefNode, ast: &sv_parser::SyntaxTree) -> Result<Identifier, String> {
    let id: Option<Locate> = match unwrap_node!(
        node,
        SimpleIdentifier,
        EscapedIdentifier,
        NetIdentifier,
        PortIdentifier,
        Identifier
    ) {
        Some(RefNode::SimpleIdentifier(x)) => Some(x.nodes.0),
        Some(RefNode::EscapedIdentifier(x)) => Some(x.nodes.0),
        Some(RefNode::NetIdentifier(x)) => match &x.nodes.0 {
            sv_parser::Identifier::SimpleIdentifier(x) => Some(x.nodes.0),
            sv_parser::Identifier::EscapedIdentifier(x) => Some(x.nodes.0),
        },
        Some(RefNode::PortIdentifier(x)) => match &x.nodes.0 {
            sv_parser::Identifier::SimpleIdentifier(x) => Some(x.nodes.0),
            sv_parser::Identifier::EscapedIdentifier(x) => Some(x.nodes.0),
        },
        Some(RefNode::Identifier(x)) => match x {
            sv_parser::Identifier::SimpleIdentifier(x) => Some(x.nodes.0),
            sv_parser::Identifier::EscapedIdentifier(x) => Some(x.nodes.0),
        },
        _ => None,
    };

    match id {
        None => Err("Expected a Simple, Escaped, or Net identifier".to_string()),
        Some(x) => match ast.get_str(&x) {
            None => Err(format!("Expected an identifier at {x:?}")),
            Some(x) => Ok(x.to_string().into()),
        },
    }
}

/// Parse a literal `node` in the `ast` into a four-state logic value
fn parse_literal_as_logic(node: RefNode, ast: &sv_parser::SyntaxTree) -> Result<Logic, String> {
    let value = unwrap_node!(node, BinaryValue, HexValue, UnsignedNumber);

    if value.is_none() {
        return Err(
            "Expected a BinaryValue, HexValue, or UnsignedNumber Node under the Literal"
                .to_string(),
        );
    }

    match value.unwrap() {
        RefNode::BinaryValue(b) => {
            let loc = b.nodes.0;
            let val = ast.get_str(&loc).unwrap();
            if val == "x" {
                return Ok(Logic::X);
            }
            let num = u64::from_str_radix(val, 2)
                .map_err(|_e| format!("Could not parse binary value {val} as bool"))?;
            match num {
                1 => Ok(true.into()),
                0 => Ok(false.into()),
                _ => Err(format!("Expected a 1 bit constant. Found {num}")),
            }
        }
        RefNode::HexValue(b) => {
            let loc = b.nodes.0;
            let val = ast.get_str(&loc).unwrap();
            if val == "x" {
                return Ok(Logic::X);
            }
            let num = u64::from_str_radix(val, 16)
                .map_err(|_e| format!("Could not parse hex value {val} as bool"))?;
            match num {
                1 => Ok(true.into()),
                0 => Ok(false.into()),
                _ => Err(format!("Expected a 1 bit constant. Found {num}")),
            }
        }
        RefNode::UnsignedNumber(b) => {
            let loc = b.nodes.0;
            let val = ast.get_str(&loc).unwrap();
            if val == "x" {
                return Ok(Logic::X);
            }
            let num = val
                .parse::<u64>()
                .map_err(|_e| format!("Could not parse decimal value {val} as bool"))?;
            match num {
                1 => Ok(true.into()),
                0 => Ok(false.into()),
                _ => Err(format!("Expected a 1 bit constant. Found {num}")),
            }
        }
        _ => unreachable!(),
    }
}

/// Construct a Safety Net [Netlist] from a Verilog netlist AST.
/// Type parameter I defines the primitive library to parse into.
pub fn from_ast<I: Instantiable + FromId>(
    ast: &sv_parser::SyntaxTree,
) -> Result<Rc<Netlist<I>>, String> {
    let netlist = Netlist::new("top".to_string());
    let mut output_set = HashSet::new();
    let mut multiple = false;
    let mut drivers: HashMap<Identifier, DrivenNet<I>> = HashMap::new();

    // Pass one
    let mut last_gate: Option<NetRef<I>> = None;
    for node_event in ast.into_iter().event() {
        match node_event {
            // Hande module definition
            NodeEvent::Enter(RefNode::ModuleDeclarationAnsi(decl)) => {
                if multiple {
                    return Err(
                        "Multiple module definitions in a single file are not supported"
                            .to_string(),
                    );
                }

                let id = unwrap_node!(decl, ModuleIdentifier).unwrap();
                let name = get_identifier(id, ast)?;
                netlist.set_name(name.to_string());
                multiple = true;
            }

            NodeEvent::Enter(RefNode::ModuleDeclarationNonansi(decl)) => {
                if multiple {
                    return Err(
                        "Multiple module definitions in a single file are not supported"
                            .to_string(),
                    );
                }

                let id = unwrap_node!(decl, ModuleIdentifier).unwrap();
                let name = get_identifier(id, ast)?;
                netlist.set_name(name.to_string());
                multiple = true;
            }

            // Handle primitive instantiation
            NodeEvent::Enter(RefNode::ModuleInstantiation(inst)) => {
                let id = unwrap_node!(inst, ModuleIdentifier).unwrap();
                let mod_name = get_identifier(id, ast)?;
                let id = unwrap_node!(inst, InstanceIdentifier).unwrap();
                let inst_name = get_identifier(id, ast)?;
                let instantiable = I::from_id(&mod_name)?;
                last_gate = Some(netlist.insert_gate_disconnected(instantiable, inst_name)?);
            }

            // Handle instance parameters
            NodeEvent::Enter(RefNode::NamedParameterAssignment(assignment)) => {
                let gate = last_gate.as_ref().unwrap();
                let mut instance_type = gate.get_instance_type_mut().unwrap();
                let key_node = unwrap_node!(assignment, ParameterIdentifier).unwrap();
                let key_node = unwrap_node!(key_node, Identifier).unwrap();
                let key = get_identifier(key_node, ast)?;
                // let expr = unwrap_node!(assignment, ParamExpression).unwrap();
                // TODO(matth2k): Read the actual parameter value
                instance_type.set_parameter(&key, Parameter::Integer(1337));
            }

            // Handle input decl
            NodeEvent::Enter(RefNode::InputDeclarationNet(input)) => {
                let id = unwrap_node!(input, PortIdentifier).unwrap();
                let name = get_identifier(id, ast)?;
                let net = Net::new_logic(name.clone());
                let net = netlist.insert_input(net);
                last_gate = Some(net.clone().unwrap());
                drivers.insert(name, net);
            }

            // Handle output decl
            NodeEvent::Enter(RefNode::OutputDeclarationNet(output)) => {
                let id = unwrap_node!(output, PortIdentifier).unwrap();
                let name = get_identifier(id, ast)?;
                output_set.insert(name);
            }

            // Handle instance connection
            NodeEvent::Enter(RefNode::NamedPortConnection(connection)) => {
                let port = unwrap_node!(connection, PortIdentifier).unwrap();
                let port_name = get_identifier(port, ast)?;
                let arg = unwrap_node!(connection, Expression).unwrap();
                let arg_i = unwrap_node!(arg.clone(), HierarchicalIdentifier);
                let gate = last_gate.as_ref().unwrap();

                match arg_i {
                    Some(n) => {
                        let arg_name = get_identifier(n, ast)?;
                        if let Some(oport) = gate.find_output(&port_name) {
                            if output_set.contains(&arg_name) {
                                oport.clone().expose_with_name(arg_name.clone());
                            }
                            oport.as_net_mut().set_identifier(arg_name.clone());

                            drivers.insert(arg_name, oport);
                        } else if gate.find_input(&port_name).is_none() {
                            return Err(format!(
                                "Could not find port {} on instance {}",
                                port_name,
                                gate.get_instance_name().unwrap()
                            ));
                        }
                    }
                    None => {
                        if gate.find_output(&port_name).is_some() {
                            return Err("Cannot drive a constant from an output port".to_string());
                        } else if gate.find_input(&port_name).is_some() {
                            let literal = unwrap_node!(arg, PrimaryLiteral);
                            if literal.is_none() {
                                return Err(format!(
                                    "Expected a literal for connection on port {port_name}"
                                ));
                            }
                            let value = parse_literal_as_logic(literal.unwrap(), ast)?;

                            let val_name = &"const".into()
                                + &gate.get_instance_name().unwrap()
                                + port_name.clone();
                            let driverless = netlist.insert_constant(
                                value,
                                Identifier::new("const_inst".to_string())
                                    + gate.get_instance_name().unwrap()
                                    + port_name,
                            )?;

                            driverless.as_net_mut().set_identifier(val_name.clone());
                            drivers.insert(val_name, driverless);
                        } else {
                            return Err(format!(
                                "Could not find port {} on instance {}",
                                port_name,
                                gate.get_instance_name().unwrap()
                            ));
                        }
                    }
                }
            }

            // Handle wire/net decl
            NodeEvent::Enter(RefNode::NetDeclAssignment(net_decl)) => {
                if unwrap_node!(net_decl, UnpackedDimension).is_some() {
                    return Err("Only single bit nets are supported".to_string());
                }
            }

            // Handle wire assignment
            // NodeEvent::Enter(RefNode::NetAssignment(net_assign)) => {
            //     let lhs = unwrap_node!(net_assign, NetLvalue).unwrap();
            //     let lhs_id = unwrap_node!(lhs, Identifier).unwrap();
            //     let lhs_name = get_identifier(lhs_id, ast).unwrap();
            //     let rhs = unwrap_node!(net_assign, Expression).unwrap();
            //     let rhs_id = unwrap_node!(rhs, Identifier, PrimaryLiteral).unwrap();
            //     let assignment = unwrap_node!(net_assign, Symbol).unwrap();
            //     match assignment {
            //         RefNode::Symbol(sym) => {
            //             let loc = sym.nodes.0;
            //             let eq = ast.get_str(&loc).unwrap();
            //             if eq != "=" {
            //                 return Err(format!("Expected an assignment operator, got {eq}"));
            //             }
            //         }
            //         _ => {
            //             return Err("Expected an assignment operator".to_string());
            //         }
            //     }
            //     if matches!(rhs_id, RefNode::Identifier(_)) {
            //         let rhs_name = get_identifier(rhs_id, ast).unwrap();
            //         cur_insts.push(SVPrimitive::new_wire(
            //             rhs_name.clone(),
            //             lhs_name.clone(),
            //             lhs_name + "_wire_" + &rhs_name,
            //         ));
            //     } else {
            //         let val = parse_literal_as_logic(rhs_id, ast)?;
            //         cur_insts.push(SVPrimitive::new_const(
            //             val,
            //             lhs_name.clone(),
            //             lhs_name + "_const_binary",
            //         ));
            //     }
            // }

            // The stuff we definitely don't support
            NodeEvent::Enter(RefNode::BinaryOperator(_)) => {
                return Err("Binary operators are not supported".to_string());
            }
            NodeEvent::Enter(RefNode::UnaryOperator(_)) => {
                return Err("Unary operators are not supported".to_string());
            }
            NodeEvent::Enter(RefNode::Concatenation(_)) => {
                return Err("Concatenation not supported".to_string());
            }
            NodeEvent::Enter(RefNode::AlwaysConstruct(_)) => {
                return Err("Always block not supported".to_string());
            }
            NodeEvent::Enter(RefNode::ConditionalStatement(_)) => {
                return Err("If/else block not supported".to_string());
            }
            _ => (),
        }
    }

    {
        // Pass two
        let mut iter = netlist.objects();
        let mut gate = None;
        for node_event in ast.into_iter().event() {
            match node_event {
                NodeEvent::Enter(RefNode::ModuleInstantiation(_))
                | NodeEvent::Enter(RefNode::InputDeclarationNet(_)) => {
                    gate = iter.next();
                }

                // Handle instance drivers
                NodeEvent::Enter(RefNode::NamedPortConnection(connection)) => {
                    let port = unwrap_node!(connection, PortIdentifier).unwrap();
                    let port_name = get_identifier(port, ast)?;
                    let arg = unwrap_node!(connection, Expression).unwrap();
                    let arg_i = unwrap_node!(arg.clone(), HierarchicalIdentifier);
                    if let Some(iport) = gate.as_ref().unwrap().find_input(&port_name) {
                        match arg_i {
                            Some(n) => {
                                let arg_name = get_identifier(n, ast)?;
                                iport.connect(drivers[&arg_name].clone());
                            }
                            None => {
                                let val_name = &"const".into()
                                    + &gate.as_ref().unwrap().get_instance_name().unwrap()
                                    + port_name;
                                iport.connect(drivers[&val_name].clone());
                                iter.next();
                            }
                        }
                    }
                }

                _ => (),
            }
        }
    }

    Ok(netlist)
}
