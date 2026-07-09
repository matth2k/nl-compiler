/*!

  Compile Verilog AST

*/

use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{cells::FromId, error::VerilogError};
use safety_net::{DrivenNet, Identifier, Instantiable, Logic, Net, NetRef, Netlist, Parameter};
use sv_parser::Identifier as SvIdentifier;
use sv_parser::{
    BinaryNumber, BinaryValue, DecimalNumber, HexNumber, HexValue, IntegralNumber,
    NonZeroUnsignedNumber, Number, Size, UnsignedNumber,
};
use sv_parser::{EscapedIdentifier, NetIdentifier, PortIdentifier, SimpleIdentifier};
use sv_parser::{Locate, NodeEvent, RefNode, SyntaxTree, unwrap_node};

/// The visitor for the first cell creation pass
struct NetlistVisitor<'a> {
    ast: &'a SyntaxTree,
}

impl<'a> NetlistVisitor<'a> {
    fn new(ast: &'a SyntaxTree) -> Self {
        Self { ast }
    }

    fn visit_locate(&self, loc: &Locate) -> Option<String> {
        self.ast.get_str(loc).map(|s| s.to_string())
    }

    fn visit_simple_identifier(&self, id: &SimpleIdentifier) -> Option<Identifier> {
        self.visit_locate(&id.nodes.0).map(Identifier::new)
    }

    fn visit_escaped_identifier(&self, id: &EscapedIdentifier) -> Option<Identifier> {
        // Already has the '\\' attached
        self.visit_locate(&id.nodes.0).map(Identifier::new)
    }

    fn visit_identifier(&self, id: &SvIdentifier) -> Option<Identifier> {
        match id {
            SvIdentifier::SimpleIdentifier(x) => self.visit_simple_identifier(x),
            SvIdentifier::EscapedIdentifier(x) => self.visit_escaped_identifier(x),
        }
    }

    fn visit_net_identifier(&self, id: &NetIdentifier) -> Option<Identifier> {
        self.visit_identifier(&id.nodes.0)
    }

    fn visit_port_identifier(&self, id: &PortIdentifier) -> Option<Identifier> {
        self.visit_identifier(&id.nodes.0)
    }

    fn visit_unsigned_number(&self, num: &UnsignedNumber) -> Option<u64> {
        self.visit_locate(&num.nodes.0)
            .and_then(|s| s.parse::<u64>().ok())
    }

    fn visit_decimal_number(&self, num: &DecimalNumber) -> Option<u64> {
        match num {
            DecimalNumber::UnsignedNumber(x) => self.visit_unsigned_number(x),
            DecimalNumber::BaseUnsigned(_) => None,
            DecimalNumber::BaseXNumber(_) => None,
            DecimalNumber::BaseZNumber(_) => None,
        }
    }

    fn visit_non_zero_unsigned_number(&self, num: &NonZeroUnsignedNumber) -> Option<usize> {
        self.visit_locate(&num.nodes.0)
            .and_then(|s| s.parse::<usize>().ok())
            .filter(|&n| n != 0)
    }

    fn visit_size(&self, size: &Size) -> Option<usize> {
        self.visit_non_zero_unsigned_number(&size.nodes.0)
    }

    fn visit_binary_value(&self, num: &BinaryValue) -> Option<u64> {
        self.visit_locate(&num.nodes.0)
            .and_then(|s| u64::from_str_radix(&s, 2).ok())
    }

    fn visit_binary_number(&self, num: &BinaryNumber) -> Option<Parameter> {
        let size = match &num.nodes.0 {
            Some(x) => self.visit_size(x),
            None => None,
        };

        let val = self.visit_binary_value(&num.nodes.2)?;

        match size {
            Some(1) => Some(Parameter::Logic(Logic::from_bool(val != 0))),
            Some(s) => Some(Parameter::bitvec(s, val)),
            None => Some(Parameter::Integer(val)),
        }
    }

    fn visit_hex_value(&self, num: &HexValue) -> Option<u64> {
        self.visit_locate(&num.nodes.0)
            .and_then(|s| u64::from_str_radix(&s, 16).ok())
    }

    fn visit_hex_number(&self, num: &HexNumber) -> Option<Parameter> {
        let size = match &num.nodes.0 {
            Some(x) => self.visit_size(x),
            None => None,
        };

        let val = self.visit_hex_value(&num.nodes.2)?;

        match size {
            Some(1) => Some(Parameter::Logic(Logic::from_bool(val != 0))),
            Some(s) => Some(Parameter::bitvec(s, val)),
            None => Some(Parameter::Integer(val)),
        }
    }

    fn visit_integral_number(&self, num: &IntegralNumber) -> Option<Parameter> {
        match num {
            IntegralNumber::DecimalNumber(x) => {
                self.visit_decimal_number(x).map(Parameter::Integer)
            }
            IntegralNumber::OctalNumber(_) => None,
            IntegralNumber::BinaryNumber(x) => self.visit_binary_number(x),
            IntegralNumber::HexNumber(x) => self.visit_hex_number(x),
        }
    }

    fn visit_number(&self, num: &Number) -> Option<Parameter> {
        match num {
            Number::IntegralNumber(x) => self.visit_integral_number(x),
            Number::RealNumber(_) => None,
        }
    }
}

/// Construct a Safety Net [Netlist] from a Verilog netlist AST.
/// Type parameter I defines the primitive library to parse into.
/// You can provide a closure `overrides` to modify each instantiated cell after creation.
pub fn from_vast_overrides<I: Instantiable + FromId, F: Fn(&Identifier, &I) -> Option<I>>(
    ast: &sv_parser::SyntaxTree,
    overrides: F,
) -> Result<Rc<Netlist<I>>, VerilogError> {
    todo!()
}

/// Construct a Safety Net [Netlist] from a Verilog netlist AST.
/// Type parameter I defines the primitive library to parse into.
pub fn from_vast<I: Instantiable + FromId>(
    ast: &sv_parser::SyntaxTree,
) -> Result<Rc<Netlist<I>>, VerilogError> {
    from_vast_overrides::<I, _>(ast, |_, _| None)
}
