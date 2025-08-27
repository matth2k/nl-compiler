/*!

  The consumed AST

*/

use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use safety_net::{
    circuit::{Identifier, Instantiable, Net},
    netlist::{DrivenNet, Netlist},
};
use sv_parser::{Locate, NodeEvent, RefNode, unwrap_node};

pub trait FromId: Sized {
    fn from_id(s: &Identifier) -> Result<Self, String>;
}

pub fn get_identifier(node: RefNode, ast: &sv_parser::SyntaxTree) -> Result<Identifier, String> {
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
            None => Err("Expected an identifier".to_string()),
            Some(x) => Ok(x.to_string().into()),
        },
    }
}

pub fn from_ast<I: Instantiable + FromId>(
    ast: &sv_parser::SyntaxTree,
) -> Result<Rc<Netlist<I>>, String> {
    let netlist = Netlist::new("top".to_string());
    let mut output_set = HashSet::new();
    let mut multiple = false;
    let mut drivers: HashMap<Identifier, DrivenNet<I>> = HashMap::new();
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
                let name = get_identifier(id, ast).unwrap();
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
                let name = get_identifier(id, ast).unwrap();
                netlist.set_name(name.to_string());
                multiple = true;
            }

            // Handle primitive instantiation
            NodeEvent::Enter(RefNode::ModuleInstantiation(inst)) => {
                let id = unwrap_node!(inst, ModuleIdentifier).unwrap();
                let mod_name = get_identifier(id, ast).unwrap();
                let id = unwrap_node!(inst, InstanceIdentifier).unwrap();
                let inst_name = get_identifier(id, ast).unwrap();
                let instantiable = I::from_id(&mod_name)?;
                netlist.insert_gate_disconnected(instantiable, inst_name)?;
            }

            // Handle input decl
            NodeEvent::Enter(RefNode::InputDeclarationNet(output)) => {
                let id = unwrap_node!(output, PortIdentifier).unwrap();
                let name = get_identifier(id, ast).unwrap();
                let net = Net::new_logic(name.clone());
                drivers.insert(name, netlist.insert_input(net));
            }

            // Handle output decl
            NodeEvent::Enter(RefNode::OutputDeclarationNet(output)) => {
                let id = unwrap_node!(output, PortIdentifier).unwrap();
                let name = get_identifier(id, ast).unwrap();
                output_set.insert(name);
            }

            // Handle instance connection
            NodeEvent::Enter(RefNode::NamedPortConnection(connection)) => {
                let port = unwrap_node!(connection, PortIdentifier).unwrap();
                let port_name = get_identifier(port, ast).unwrap();
                let arg = unwrap_node!(connection, Expression).unwrap();
                let arg_i = unwrap_node!(arg.clone(), HierarchicalIdentifier);

                match arg_i {
                    Some(n) => {
                        let arg_name = get_identifier(n, ast).unwrap();
                        let gate = netlist.last().unwrap();
                        if let Some(iport) = gate.find_input(&port_name) {
                            // TODO: This will fail for cycles / not in topo order
                            iport.connect(drivers[&arg_name].clone());
                        } else if let Some(oport) = gate.find_output(&port_name) {
                            oport.as_net_mut().set_identifier(arg_name.clone());
                            drivers.insert(arg_name, oport);
                        } else {
                            return Err(format!(
                                "Could not find port {} on instance {}",
                                port_name,
                                gate.get_instance_name().unwrap()
                            ));
                        }
                    }
                    None => {
                        todo!("Handle tied/constant drivers");
                    }
                }
            }
            // NodeEvent::Leave(RefNode::NamedPortConnection(_connection)) => (),

            // // Handle wire/net decl
            // NodeEvent::Enter(RefNode::NetDeclAssignment(net_decl)) => {
            //     let id = unwrap_node!(net_decl, NetIdentifier).unwrap();
            //     if unwrap_node!(net_decl, UnpackedDimension).is_some() {
            //         panic!("Only support 1 bit signals!");
            //     }
            //     let name = get_identifier(id, ast).unwrap();
            //     cur_signals.push(SVSignal::new(1, name));
            // }
            // NodeEvent::Leave(RefNode::NetDeclAssignment(_net_decl)) => (),

            // // Handle wire assignment
            // // TODO(mrh259): Refactor this branch of logic and this function in general
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
            NodeEvent::Leave(RefNode::NetAssignment(_net_assign)) => (),

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
    Ok(netlist)
}
