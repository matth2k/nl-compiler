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
    BinaryNumber, BinaryValue, ConstantExpression, DecimalNumber, Expression, HexNumber, HexValue,
    HierarchicalIdentifier, IntegralNumber, NonZeroUnsignedNumber, Number, Primary,
    PrimaryHierarchical, Select, Size, UnsignedNumber,
};
use sv_parser::{ConstantRange, PackedDimension};
use sv_parser::{
    EscapedIdentifier, InstanceIdentifier, ListOfPortIdentifiers, ModuleIdentifier, NetIdentifier,
    PortIdentifier, SimpleIdentifier,
};
use sv_parser::{Locate, NodeEvent, RefNode, SyntaxTree, unwrap_node};
use sv_parser::{ModuleDeclaration, ModuleDeclarationNonansi};

type ErrorMsg = (String, Locate);

/// The visitor for the first cell creation pass
/// Can get bit selector, bit ranges, wire identifiers, port identifiers, most params
struct SemanticVisitor<'a> {
    ast: &'a SyntaxTree,
}

impl<'a> SemanticVisitor<'a> {
    fn new(ast: &'a SyntaxTree) -> Self {
        Self { ast }
    }

    fn unravel_locate<'b, T>(&self, t: T) -> Locate
    where
        T: Into<RefNode<'b>>,
    {
        let refnode: RefNode = t.into();
        let refnode = unwrap_node!(refnode, Locate).unwrap();
        match refnode {
            RefNode::Locate(&x) => x,
            _ => unreachable!(),
        }
    }

    fn visit_locate(&self, loc: &Locate) -> String {
        self.ast.get_str(loc).map(|s| s.to_string()).unwrap()
    }

    fn visit_simple_identifier(&self, id: &SimpleIdentifier) -> Identifier {
        Identifier::new(self.visit_locate(&id.nodes.0))
    }

    fn visit_escaped_identifier(&self, id: &EscapedIdentifier) -> Identifier {
        // Already has the '\\' attached
        Identifier::new(self.visit_locate(&id.nodes.0))
    }

    fn visit_identifier(&self, id: &SvIdentifier) -> Identifier {
        match id {
            SvIdentifier::SimpleIdentifier(x) => self.visit_simple_identifier(x),
            SvIdentifier::EscapedIdentifier(x) => self.visit_escaped_identifier(x),
        }
    }

    fn visit_net_identifier(&self, id: &NetIdentifier) -> Identifier {
        self.visit_identifier(&id.nodes.0)
    }

    fn visit_port_identifier(&self, id: &PortIdentifier) -> Identifier {
        self.visit_identifier(&id.nodes.0)
    }

    fn visit_module_identifier(&self, id: &ModuleIdentifier) -> Identifier {
        self.visit_identifier(&id.nodes.0)
    }

    fn visit_instance_identifier(&self, id: &InstanceIdentifier) -> Identifier {
        self.visit_identifier(&id.nodes.0)
    }

    /// For parsing most port identifiers
    fn visit_list_of_port_identifiers(
        &self,
        list: &ListOfPortIdentifiers,
    ) -> Result<Vec<Identifier>, ErrorMsg> {
        let list = &list.nodes.0;
        for (x, p) in list.contents() {
            if !p.is_empty() {
                return Err((
                    "Expected a list of port identifiers".to_string(),
                    self.unravel_locate(x),
                ));
            }
        }

        Ok(list
            .contents()
            .iter()
            .map(|(x, _)| self.visit_port_identifier(x))
            .collect())
    }

    fn visit_unsigned_number(&self, num: &UnsignedNumber) -> u64 {
        self.visit_locate(&num.nodes.0).parse::<u64>().unwrap()
    }

    fn visit_decimal_number(&self, num: &DecimalNumber) -> Result<u64, ErrorMsg> {
        match num {
            DecimalNumber::UnsignedNumber(x) => Ok(self.visit_unsigned_number(x)),
            DecimalNumber::BaseUnsigned(_) => Err((
                "Base unsigned decimal numbers are not supported".to_string(),
                self.unravel_locate(num),
            )),
            DecimalNumber::BaseXNumber(_) => Err((
                "Base X decimal numbers are not supported".to_string(),
                self.unravel_locate(num),
            )),
            DecimalNumber::BaseZNumber(_) => Err((
                "Base Z decimal numbers are not supported".to_string(),
                self.unravel_locate(num),
            )),
        }
    }

    fn visit_non_zero_unsigned_number(&self, num: &NonZeroUnsignedNumber) -> usize {
        self.visit_locate(&num.nodes.0).parse::<usize>().unwrap()
    }

    fn visit_size(&self, size: &Size) -> usize {
        self.visit_non_zero_unsigned_number(&size.nodes.0)
    }

    fn visit_binary_value(&self, num: &BinaryValue) -> u64 {
        u64::from_str_radix(&self.visit_locate(&num.nodes.0), 2).unwrap()
    }

    fn visit_binary_number(&self, num: &BinaryNumber) -> Parameter {
        let size = num.nodes.0.as_ref().map(|x| self.visit_size(x));

        let val = self.visit_binary_value(&num.nodes.2);

        match size {
            Some(1) => Parameter::Logic(Logic::from_bool(val != 0)),
            Some(s) => Parameter::bitvec(s, val),
            None => Parameter::Integer(val),
        }
    }

    fn visit_hex_value(&self, num: &HexValue) -> u64 {
        u64::from_str_radix(&self.visit_locate(&num.nodes.0), 16).unwrap()
    }

    fn visit_hex_number(&self, num: &HexNumber) -> Parameter {
        let size = num.nodes.0.as_ref().map(|x| self.visit_size(x));

        let val = self.visit_hex_value(&num.nodes.2);

        match size {
            Some(1) => Parameter::Logic(Logic::from_bool(val != 0)),
            Some(s) => Parameter::bitvec(s, val),
            None => Parameter::Integer(val),
        }
    }

    fn visit_integral_number(&self, num: &IntegralNumber) -> Result<Parameter, ErrorMsg> {
        match num {
            IntegralNumber::DecimalNumber(x) => {
                self.visit_decimal_number(x).map(Parameter::Integer)
            }
            IntegralNumber::OctalNumber(_) => Err((
                "Octal numbers are not supported".to_string(),
                self.unravel_locate(num),
            )),
            IntegralNumber::BinaryNumber(x) => Ok(self.visit_binary_number(x)),
            IntegralNumber::HexNumber(x) => Ok(self.visit_hex_number(x)),
        }
    }

    /// For parsing most parameters
    fn visit_number(&self, num: &Number) -> Result<Parameter, ErrorMsg> {
        match num {
            Number::IntegralNumber(x) => self.visit_integral_number(x),
            Number::RealNumber(_) => Err((
                "Real numbers are not supported".to_string(),
                self.unravel_locate(num),
            )),
        }
    }

    fn visit_constant_expression(&self, expr: &ConstantExpression) -> Result<Parameter, ErrorMsg> {
        match expr {
            ConstantExpression::ConstantPrimary(x) => {
                let refnode: RefNode = x.as_ref().into();
                let refnode = unwrap_node!(refnode, ConstantPrimary).ok_or((
                    "Expected a ConstantPrimary node".to_string(),
                    self.unravel_locate(expr),
                ))?;
                let refnode = unwrap_node!(refnode, PrimaryLiteral).ok_or((
                    "Expected a PrimaryLiteral node".to_string(),
                    self.unravel_locate(expr),
                ))?;
                let refnode = unwrap_node!(refnode, Number).ok_or((
                    "Expected a Number node".to_string(),
                    self.unravel_locate(expr),
                ))?;
                match refnode {
                    RefNode::Number(x) => self.visit_number(x),
                    _ => unreachable!(),
                }
            }
            ConstantExpression::Binary(_) => Err((
                "Binary expressions are not supported".to_string(),
                self.unravel_locate(expr),
            )),
            ConstantExpression::Unary(_) => Err((
                "Unary expressions are not supported".to_string(),
                self.unravel_locate(expr),
            )),
            ConstantExpression::Ternary(_) => Err((
                "Ternary expressions are not supported".to_string(),
                self.unravel_locate(expr),
            )),
            ConstantExpression::Inside(_) => Err((
                "Inside expressions are not supported".to_string(),
                self.unravel_locate(expr),
            )),
        }
    }

    fn visit_hierarchical_identifier(
        &self,
        id: &HierarchicalIdentifier,
    ) -> Result<Identifier, ErrorMsg> {
        if !id.nodes.1.is_empty() {
            return Err((
                "Hierarchical identifiers with qualifiers are not supported".to_string(),
                self.unravel_locate(id),
            ));
        }
        Ok(self.visit_identifier(&id.nodes.2))
    }

    fn visit_select(&self, select: &Select) -> Result<usize, ErrorMsg> {
        let refnode: RefNode = select.into();
        let refnode = unwrap_node!(refnode, BitSelect).ok_or((
            "Expected a BitSelect node".to_string(),
            self.unravel_locate(select),
        ))?;
        let refnode = unwrap_node!(refnode, Expression).ok_or((
            "Expected a Expression node".to_string(),
            self.unravel_locate(select),
        ))?;
        let refnode = unwrap_node!(refnode, PrimaryLiteral).ok_or((
            "Expected a PrimaryLiteral node".to_string(),
            self.unravel_locate(select),
        ))?;
        let refnode = unwrap_node!(refnode, Number).ok_or((
            "Expected a Number node".to_string(),
            self.unravel_locate(select),
        ))?;
        match refnode {
            RefNode::Number(x) => {
                let param = self.visit_number(x)?;
                match param {
                    Parameter::Integer(i) => Ok(i as usize),
                    _ => Err((
                        "Expected an integer for the select expression".to_string(),
                        self.unravel_locate(select),
                    )),
                }
            }
            _ => unreachable!(),
        }
    }

    fn visit_hierarchical_primary(
        &self,
        primary: &PrimaryHierarchical,
    ) -> Result<Identifier, ErrorMsg> {
        let id = self.visit_hierarchical_identifier(&primary.nodes.1)?;
        let select = self.visit_select(&primary.nodes.2)?;
        Ok(Identifier::new(format!("{}[{}]", id, select)))
    }

    fn visit_primary(&self, primary: &Primary) -> Result<Identifier, ErrorMsg> {
        match primary {
            Primary::Hierarchical(h) => self.visit_hierarchical_primary(h),
            _ => Err((
                "Only hierarchical primary expressions are supported".to_string(),
                self.unravel_locate(primary),
            )),
        }
    }

    /// For parsing connections
    fn visit_expression(&self, expr: &Expression) -> Result<Identifier, ErrorMsg> {
        match expr {
            Expression::Primary(p) => self.visit_primary(p),
            _ => Err((
                "Only primary expressions are supported".to_string(),
                self.unravel_locate(expr),
            )),
        }
    }

    fn visit_constant_range(&self, range: &ConstantRange) -> Result<(usize, usize), ErrorMsg> {
        let l = self.visit_constant_expression(&range.nodes.0)?;
        let r = self.visit_constant_expression(&range.nodes.2)?;
        let Parameter::Integer(l) = l else {
            return Err((
                "Expected an integer for the left side of range".to_string(),
                self.unravel_locate(range),
            ));
        };
        let Parameter::Integer(r) = r else {
            return Err((
                "Expected an integer for the left side of range".to_string(),
                self.unravel_locate(range),
            ));
        };
        Ok((l as usize, r as usize))
    }

    /// For parsing bus decl component
    fn visit_packed_dimension(&self, dim: &PackedDimension) -> Result<(usize, usize), ErrorMsg> {
        let refnode: RefNode = dim.into();
        let refnode = unwrap_node!(refnode, PackedDimensionRange).ok_or((
            "Expected a PackedDimensionRange node".to_string(),
            self.unravel_locate(dim),
        ))?;
        let refnode = unwrap_node!(refnode, ConstantRange).ok_or((
            "Expected a ConstantRange node".to_string(),
            self.unravel_locate(dim),
        ))?;
        match refnode {
            RefNode::ConstantRange(x) => self.visit_constant_range(x),
            _ => unreachable!(),
        }
    }
}

/// The visitor that iterate over basic items to create
struct ItemVisitor<'a, I: Instantiable + FromId> {
    ast: &'a SyntaxTree,
    netlist: Rc<Netlist<I>>,
    has_name: bool,
    lookup: SemanticVisitor<'a>,
}

impl<'a, I: Instantiable + FromId> ItemVisitor<'a, I> {
    fn new(ast: &'a SyntaxTree, netlist: Rc<Netlist<I>>) -> Self {
        Self {
            ast,
            netlist,
            has_name: false,
            lookup: SemanticVisitor::new(ast),
        }
    }

    fn visit_module_identifier(&mut self, id: &ModuleIdentifier) -> Result<(), ErrorMsg> {
        if self.has_name {
            return Err((
                "Multiple module identifiers found".to_string(),
                self.lookup.unravel_locate(id),
            ));
        }
        let id = self.lookup.visit_module_identifier(id);
        self.netlist.set_name(id.to_string());
        self.has_name = true;
        Ok(())
    }

    fn visit_module_declaration(&mut self, decl: &ModuleDeclaration) -> Result<(), ErrorMsg> {
        let id: RefNode = decl.into();
        let id = unwrap_node!(id, ModuleIdentifier).unwrap();
        match id {
            RefNode::ModuleIdentifier(x) => self.visit_module_identifier(x)?,
            _ => unreachable!(),
        }

        let id: RefNode = decl.into();
        if unwrap_node!(id, ModuleDeclarationAnsi).is_some() {
            todo!()
        }

        Ok(())
    }
}

/// Construct a Safety Net [Netlist] from a Verilog netlist AST.
/// Type parameter I defines the primitive library to parse into.
/// You can provide a closure `overrides` to modify each instantiated cell after creation.
pub fn from_vast_overrides<I: Instantiable + FromId, F: Fn(&Identifier, &I) -> Option<I>>(
    ast: &sv_parser::SyntaxTree,
    overrides: F,
) -> Result<Rc<Netlist<I>>, VerilogError> {
    let sv = SemanticVisitor::new(ast);

    todo!()
}

/// Construct a Safety Net [Netlist] from a Verilog netlist AST.
/// Type parameter I defines the primitive library to parse into.
pub fn from_vast<I: Instantiable + FromId>(
    ast: &sv_parser::SyntaxTree,
) -> Result<Rc<Netlist<I>>, VerilogError> {
    from_vast_overrides::<I, _>(ast, |_, _| None)
}
