/*!

  Compile Verilog AST

*/

use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{cells::FromId, error::VerilogError};
use safety_net::{DrivenNet, Identifier, Instantiable, Logic, Net, NetRef, Netlist, Parameter};
use sv_parser::{Locate, NodeEvent, RefNode, unwrap_node};

/// From a AST node, read in the identifier from the source location
fn get_identifier(node: RefNode, ast: &sv_parser::SyntaxTree) -> Result<Identifier, VerilogError> {
    let id: Option<Locate> = match unwrap_node!(
        node,
        SimpleIdentifier,
        EscapedIdentifier,
        NetIdentifier,
        PortIdentifier,
        Identifier,
        Locate
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
        Some(RefNode::Locate(x)) => {
            return Err(VerilogError::UnexpectedRefNode(
                *x,
                "Expected a SimpleIdentifier, EscapedIdentifier, NetIdentifier, PortIdentifier, or Identifier"
                    .to_string(),
            ));
        }
        _ => None,
    };

    match id {
        None => Err(VerilogError::MissingRefNode("Expected a SimpleIdentifier, EscapedIdentifier, NetIdentifier, PortIdentifier, or Identifier"
                    .to_string())),
        Some(x) => match ast.get_str(&x) {
            None => Err(VerilogError::ParseStrError(x)),
            Some(x) => Ok(x.to_string().into()),
        },
    }
}

/// Parse a literal `node` in the `ast` into a four-state logic value
fn parse_literal_as_logic(
    node: RefNode,
    ast: &sv_parser::SyntaxTree,
) -> Result<Logic, VerilogError> {
    let loc = unwrap_node!(node.clone(), Locate);
    let loc = match loc {
        Some(RefNode::Locate(x)) => Some(*x),
        None => None,
        _ => None,
    };
    let value = unwrap_node!(node, BinaryValue, HexValue, UnsignedNumber);

    if value.is_none() {
        match loc {
            Some(l) => {
                return Err(VerilogError::UnexpectedRefNode(
                    l,
                    "Expected a BinaryValue, HexValue, UnsignedNumber".to_string(),
                ));
            }
            None => {
                return Err(VerilogError::MissingRefNode(
                    "Expected a BinaryValue, HexValue, UnsignedNumber".to_string(),
                ));
            }
        };
    }

    match value.unwrap() {
        RefNode::BinaryValue(b) => {
            let loc = b.nodes.0;
            let val = ast.get_str(&loc).unwrap();
            if val == "x" {
                return Ok(Logic::X);
            }
            let num =
                u64::from_str_radix(val, 2).map_err(|e| VerilogError::ParseIntError(e, loc))?;
            match num {
                0 => Ok(false.into()),
                _ => Ok(true.into()),
            }
        }
        RefNode::HexValue(b) => {
            let loc = b.nodes.0;
            let val = ast.get_str(&loc).unwrap();
            if val == "x" {
                return Ok(Logic::X);
            }
            let num =
                u64::from_str_radix(val, 16).map_err(|e| VerilogError::ParseIntError(e, loc))?;
            match num {
                0 => Ok(false.into()),
                _ => Ok(true.into()),
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
                .map_err(|e| VerilogError::ParseIntError(e, loc))?;
            match num {
                0 => Ok(false.into()),
                _ => Ok(true.into()),
            }
        }
        _ => unreachable!(),
    }
}

/// Parse a literal `node` in the `ast` into a four-state logic value
fn parse_literal_as_param(
    node: RefNode,
    ast: &sv_parser::SyntaxTree,
) -> Result<Parameter, VerilogError> {
    let value = unwrap_node!(node.clone(), BinaryValue, HexValue, UnsignedNumber);
    let loc = unwrap_node!(node.clone(), Locate);
    let loc = match loc {
        Some(RefNode::Locate(x)) => Some(*x),
        None => None,
        _ => None,
    };
    let size = unwrap_node!(node, Size);

    // TODO(matth2k): Params need to be four-state logic too. Example: Reg init 1'hx
    if value.is_none() {
        match loc {
            Some(l) => {
                return Err(VerilogError::UnexpectedRefNode(
                    l,
                    "Expected a BinaryValue, HexValue, UnsignedNumber".to_string(),
                ));
            }
            None => {
                return Err(VerilogError::MissingRefNode(
                    "Expected a BinaryValue, HexValue, UnsignedNumber".to_string(),
                ));
            }
        };
    }

    match (size, value) {
        (None, Some(RefNode::UnsignedNumber(n))) => Ok(Parameter::Integer(
            ast.get_str(&n.nodes.0)
                .unwrap()
                .parse::<u64>()
                .map_err(|e| VerilogError::ParseIntError(e, n.nodes.0))?,
        )),
        (Some(size), Some(RefNode::UnsignedNumber(n))) => {
            let size = unwrap_node!(size, NonZeroUnsignedNumber).unwrap();
            if let RefNode::NonZeroUnsignedNumber(s) = size {
                let size = ast
                    .get_str(&s.nodes.0)
                    .unwrap()
                    .parse::<usize>()
                    .map_err(|e| VerilogError::ParseIntError(e, s.nodes.0))?;
                let val = ast
                    .get_str(&n.nodes.0)
                    .unwrap()
                    .parse::<u64>()
                    .map_err(|e| VerilogError::ParseIntError(e, n.nodes.0))?;
                Ok(Parameter::bitvec(size, val))
            } else {
                Err(VerilogError::MissingRefNode(
                    "Expected a NonZeroUnsignedNumber for the literal size".to_string(),
                ))
            }
        }
        (Some(size), Some(RefNode::HexValue(n))) => {
            let size = unwrap_node!(size, NonZeroUnsignedNumber).unwrap();
            if let RefNode::NonZeroUnsignedNumber(s) = size {
                let size = ast
                    .get_str(&s.nodes.0)
                    .unwrap()
                    .parse::<usize>()
                    .map_err(|e| VerilogError::ParseIntError(e, s.nodes.0))?;
                let val = u64::from_str_radix(ast.get_str(&n.nodes.0).unwrap(), 16)
                    .map_err(|e| VerilogError::ParseIntError(e, n.nodes.0))?;
                Ok(Parameter::bitvec(size, val))
            } else {
                Err(VerilogError::MissingRefNode(
                    "Expected a NonZeroUnsignedNumber for the literal size".to_string(),
                ))
            }
        }

        (Some(size), Some(RefNode::BinaryValue(n))) => {
            let size = unwrap_node!(size, NonZeroUnsignedNumber).unwrap();
            if let RefNode::NonZeroUnsignedNumber(s) = size {
                let size = ast
                    .get_str(&s.nodes.0)
                    .unwrap()
                    .parse::<usize>()
                    .map_err(|e| VerilogError::ParseIntError(e, s.nodes.0))?;
                let val = u64::from_str_radix(ast.get_str(&n.nodes.0).unwrap(), 2)
                    .map_err(|e| VerilogError::ParseIntError(e, n.nodes.0))?;
                Ok(Parameter::bitvec(size, val))
            } else {
                Err(VerilogError::MissingRefNode(
                    "Expected a NonZeroUnsignedNumber for the literal size".to_string(),
                ))
            }
        }

        _ => Err(VerilogError::Other(
            None,
            "Size type combination is not supported".to_string(),
        )),
    }
}

/// Construct a Safety Net [Netlist] from a Verilog netlist AST.
/// Type parameter I defines the primitive library to parse into.
pub fn from_vast<I: Instantiable + FromId>(
    ast: &sv_parser::SyntaxTree,
) -> Result<Rc<Netlist<I>>, VerilogError> {
    let netlist = Netlist::new("top".to_string());
    let mut output_set = HashSet::new();
    let mut multiple = false;
    let mut drivers: HashMap<Identifier, DrivenNet<I>> = HashMap::new();

    // Cell creation pass
    let mut last_gate: Option<NetRef<I>> = None;
    let mut locs: Vec<Locate> = Vec::new();
    for node_event in ast.into_iter().event() {
        match node_event {
            // Track last location for error reporting
            NodeEvent::Enter(RefNode::Locate(loc)) => {
                locs.push(*loc);
            }

            // Hande module definition
            NodeEvent::Enter(RefNode::ModuleDeclarationAnsi(decl)) => {
                if multiple {
                    return Err(VerilogError::Other(
                        locs.last().cloned(),
                        "Multiple module definitions in a single file are not supported"
                            .to_string(),
                    ));
                }

                let id = unwrap_node!(decl, ModuleIdentifier).unwrap();
                let name = get_identifier(id, ast)?;
                netlist.set_name(name.to_string());
                multiple = true;
            }

            NodeEvent::Enter(RefNode::ModuleDeclarationNonansi(decl)) => {
                if multiple {
                    return Err(VerilogError::Other(
                        locs.last().cloned(),
                        "Multiple module definitions in a single file are not supported"
                            .to_string(),
                    ));
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
                let instantiable = I::from_id(&mod_name)
                    .map_err(|e| VerilogError::SafetyNetError(locs.last().cloned(), e))?;
                last_gate = Some(netlist.insert_gate_disconnected(instantiable, inst_name));
            }

            // Handle instance parameters
            NodeEvent::Enter(RefNode::NamedParameterAssignment(assignment)) => {
                let gate = last_gate.as_ref().unwrap();
                let mut instance_type = gate.get_instance_type_mut().unwrap();
                let key_node = unwrap_node!(assignment, ParameterIdentifier).unwrap();
                let key_node = unwrap_node!(key_node, Identifier).unwrap();
                let key = get_identifier(key_node, ast)?;
                let expr = unwrap_node!(assignment, ParamExpression).unwrap();
                let expr = unwrap_node!(expr, PrimaryLiteral).unwrap();
                let val = parse_literal_as_param(expr, ast)?;
                instance_type.set_parameter(&key, val);
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
                            return Err(VerilogError::Other(
                                locs.last().cloned(),
                                format!(
                                    "Could not find port {} on instance {}",
                                    port_name,
                                    gate.get_instance_name().unwrap()
                                ),
                            ));
                        }
                    }
                    None => {
                        if gate.find_output(&port_name).is_some() {
                            return Err(VerilogError::Other(
                                locs.last().cloned(),
                                "Cannot drive a constant from an output port".to_string(),
                            ));
                        } else if gate.find_input(&port_name).is_some() {
                            let literal = unwrap_node!(arg, PrimaryLiteral);
                            if literal.is_none() {
                                return Err(VerilogError::Other(
                                    locs.last().cloned(),
                                    format!(
                                        "Expected a literal for connection on port {port_name}"
                                    ),
                                ));
                            }
                            let value = parse_literal_as_logic(literal.unwrap(), ast)?;

                            let val_name = &"const".into()
                                + &gate.get_instance_name().unwrap()
                                + port_name.clone();
                            let driverless = netlist
                                .insert_constant(
                                    value,
                                    Identifier::new("const_inst".to_string())
                                        + gate.get_instance_name().unwrap()
                                        + port_name,
                                )
                                .map_err(|e| {
                                    VerilogError::SafetyNetError(locs.last().cloned(), e)
                                })?;

                            driverless.as_net_mut().set_identifier(val_name.clone());
                            drivers.insert(val_name, driverless);
                        } else {
                            return Err(VerilogError::Other(
                                locs.last().cloned(),
                                format!(
                                    "Could not find port {} on instance {}",
                                    port_name,
                                    gate.get_instance_name().unwrap()
                                ),
                            ));
                        }
                    }
                }
            }

            // Handle wire/net decl
            NodeEvent::Enter(RefNode::NetDeclAssignment(net_decl)) => {
                if unwrap_node!(net_decl, UnpackedDimension).is_some() {
                    return Err(VerilogError::Other(
                        locs.last().cloned(),
                        "Only single bit nets are supported".to_string(),
                    ));
                }
            }

            // Handle constant wire assignment
            NodeEvent::Enter(RefNode::NetAssignment(net_assign)) => {
                let lhs = unwrap_node!(net_assign, NetLvalue).unwrap();
                let lhs_id = unwrap_node!(lhs, Identifier).unwrap();
                let lhs_id = get_identifier(lhs_id, ast).unwrap();
                let rhs = unwrap_node!(net_assign, Expression).unwrap();
                let rhs_id = unwrap_node!(rhs, Identifier, PrimaryLiteral).unwrap();
                let assignment = unwrap_node!(net_assign, Symbol).unwrap();

                // Check assignment is an assignment
                match assignment {
                    RefNode::Symbol(sym) => {
                        let loc = sym.nodes.0;
                        let eq = ast.get_str(&loc).unwrap();
                        if eq != "=" {
                            return Err(VerilogError::Other(
                                locs.last().cloned(),
                                format!("Expected an assignment operator, got {eq}"),
                            ));
                        }
                    }
                    _ => {
                        return Err(VerilogError::Other(
                            locs.last().cloned(),
                            "Expected an assignment operator".to_string(),
                        ));
                    }
                }

                // Only dealing with constants
                if matches!(rhs_id, RefNode::PrimaryLiteral(_)) {
                    let val = parse_literal_as_logic(rhs_id, ast)?;
                    let id = lhs_id.clone() + Identifier::new("const_logic".to_string());
                    let net = netlist
                        .insert_constant(val, id.clone())
                        .map_err(|e| VerilogError::SafetyNetError(locs.last().cloned(), e))?;
                    last_gate = Some(net.clone().unwrap());
                    eprintln!("Inserted constant net {id}");
                    drivers.insert(lhs_id, net);
                }
            }

            // The stuff we definitely don't support
            NodeEvent::Enter(RefNode::BinaryOperator(_)) => {
                return Err(VerilogError::Other(
                    locs.last().cloned(),
                    "Binary operators are not supported".to_string(),
                ));
            }
            NodeEvent::Enter(RefNode::UnaryOperator(_)) => {
                return Err(VerilogError::Other(
                    locs.last().cloned(),
                    "Unary operators are not supported".to_string(),
                ));
            }
            NodeEvent::Enter(RefNode::Concatenation(_)) => {
                return Err(VerilogError::Other(
                    locs.last().cloned(),
                    "Concatenation not supported".to_string(),
                ));
            }
            NodeEvent::Enter(RefNode::AlwaysConstruct(_)) => {
                return Err(VerilogError::Other(
                    locs.last().cloned(),
                    "Always block not supported".to_string(),
                ));
            }
            NodeEvent::Enter(RefNode::ConditionalStatement(_)) => {
                return Err(VerilogError::Other(
                    locs.last().cloned(),
                    "If/else block not supported".to_string(),
                ));
            }
            _ => (),
        }
    }

    // Wire aliasing pass
    let mut changing = true;
    while changing {
        changing = false;

        for node_event in ast.into_iter().event() {
            if let NodeEvent::Enter(RefNode::NetAssignment(net_assign)) = node_event {
                let lhs = unwrap_node!(net_assign, NetLvalue).unwrap();
                let lhs_id = unwrap_node!(lhs, Identifier).unwrap();
                let lhs_id = get_identifier(lhs_id, ast).unwrap();
                let rhs = unwrap_node!(net_assign, Expression).unwrap();
                let rhs_id = unwrap_node!(rhs, Identifier, PrimaryLiteral).unwrap();

                // Only dealing with identifier aliasing
                if matches!(rhs_id, RefNode::Identifier(_)) {
                    if drivers.contains_key(&lhs_id) {
                        continue;
                    }
                    let rhs_id = get_identifier(rhs_id, ast).unwrap();
                    if !drivers.contains_key(&rhs_id) {
                        continue;
                    }
                    let alias = drivers[&rhs_id].clone();

                    if output_set.contains(&lhs_id) {
                        netlist.expose_net_with_name(alias.clone(), lhs_id.clone());
                    }
                    drivers.insert(lhs_id, alias);

                    changing = true;
                }
            }
        }
    }

    locs.clear();
    {
        // Final wiring pass
        let mut iter = netlist.objects();
        let mut gate = None;
        for node_event in ast.into_iter().event() {
            match node_event {
                // Track last location for error reporting
                NodeEvent::Enter(RefNode::Locate(loc)) => {
                    locs.push(*loc);
                }

                NodeEvent::Enter(RefNode::ModuleInstantiation(_))
                | NodeEvent::Enter(RefNode::InputDeclarationNet(_)) => {
                    gate = iter.next();
                }

                NodeEvent::Enter(RefNode::NetAssignment(net_assign)) => {
                    let rhs = unwrap_node!(net_assign, Expression).unwrap();
                    let rhs_id = unwrap_node!(rhs, Identifier, PrimaryLiteral).unwrap();

                    // Only dealing with constants
                    if matches!(rhs_id, RefNode::PrimaryLiteral(_)) {
                        gate = iter.next();
                    }
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
                                if let Some(d) = drivers.get(&arg_name) {
                                    iport.connect(d.clone());
                                } else {
                                    return Err(VerilogError::Other(
                                        locs.last().cloned(),
                                        format!("{arg_name} is not a valid driver"),
                                    ));
                                }
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
