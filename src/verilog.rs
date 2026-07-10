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
    AnsiPortDeclaration, AnsiPortDeclarationNet, InputDeclaration, InputDeclarationNet,
    ListOfPortDeclarations, ModuleDeclaration, ModuleItem, NetPortHeader,
    NetPortHeaderOrInterfacePortHeader, NonPortModuleItem, OutputDeclaration, OutputDeclarationNet,
    PortDeclaration, PortDeclarationInput, PortDeclarationOutput, PortDirection,
};
use sv_parser::{
    BinaryNumber, BinaryValue, ConstantExpression, DecimalNumber, Expression, HexNumber, HexValue,
    HierarchicalIdentifier, IntegralNumber, NonZeroUnsignedNumber, Number, Primary,
    PrimaryHierarchical, PrimaryLiteral, Select, Size, UnsignedNumber,
};
use sv_parser::{
    ConstantBitSelect, ConstantSelect, ContinuousAssign, ContinuousAssignNet, ListOfNetAssignments,
    NetAssignment, NetLvalue, NetLvalueIdentifier,
};
use sv_parser::{
    ConstantRange, HierarchicalNetIdentifier, NetPortType, NetPortTypeDataType, NetType,
    PackedDimension, PsOrHierarchicalNetIdentifier, PsOrHierarchicalNetIdentifierPackageScope,
};
use sv_parser::{
    EscapedIdentifier, InstanceIdentifier, ListOfPortIdentifiers, MintypmaxExpression,
    ModuleIdentifier, NetIdentifier, ParamExpression, ParameterIdentifier, PortIdentifier,
    SimpleIdentifier,
};
use sv_parser::{
    HierarchicalInstance, ListOfParameterAssignments, ListOfParameterAssignmentsNamed,
    ListOfPortConnections, ListOfPortConnectionsNamed, ModuleCommonItem, ModuleInstantiation,
    ModuleOrGenerateItem, ModuleOrGenerateItemDeclaration, ModuleOrGenerateItemModule,
    ModuleOrGenerateItemModuleItem, NamedParameterAssignment, NamedPortConnection,
    NamedPortConnectionIdentifier, NetDeclaration, PackageOrGenerateItemDeclaration,
    ParameterValueAssignment,
};
use sv_parser::{Locate, RefNode, SyntaxTree, unwrap_node};

type ErrorMsg = (String, Locate);

enum IdentifierOrLogic {
    Identifier(Identifier),
    Logic(Logic),
}

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

    fn visit_parameter_identifier(&self, id: &ParameterIdentifier) -> Identifier {
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
                let refnode = unwrap_node!(refnode, PrimaryLiteral);
                match refnode {
                    Some(RefNode::PrimaryLiteral(x)) => self.visit_primary_literal(x),
                    _ => Err((
                        "Expected a PrimaryLiteral node".to_string(),
                        self.unravel_locate(expr),
                    )),
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

    fn visit_select(&self, select: &Select) -> Result<Option<u64>, ErrorMsg> {
        let refnode: RefNode = select.into();
        let Some(refnode) = unwrap_node!(refnode, BitSelect) else {
            return Ok(None);
        };

        let Some(refnode) = unwrap_node!(refnode, Expression) else {
            return Ok(None);
        };

        let refnode = unwrap_node!(refnode, PrimaryLiteral);
        match refnode {
            Some(RefNode::PrimaryLiteral(x)) => match self.visit_primary_literal(x)? {
                Parameter::Integer(i) => Ok(Some(i)),
                _ => Err((
                    "Expected an integer for the select expression".to_string(),
                    self.unravel_locate(select),
                )),
            },
            _ => Err((
                "Expected a PrimaryLiteral node".to_string(),
                self.unravel_locate(select),
            )),
        }
    }

    fn visit_hierarchical_primary(
        &self,
        primary: &PrimaryHierarchical,
    ) -> Result<Identifier, ErrorMsg> {
        let id = self.visit_hierarchical_identifier(&primary.nodes.1)?;
        let select = self.visit_select(&primary.nodes.2)?;
        match select {
            Some(s) => Ok(Identifier::new(format!("{}[{}]", id, s))),
            None => Ok(id),
        }
    }

    fn visit_primary_literal(&self, literal: &PrimaryLiteral) -> Result<Parameter, ErrorMsg> {
        match literal {
            PrimaryLiteral::Number(x) => self.visit_number(x),
            _ => Err((
                "Only number literals are supported".to_string(),
                self.unravel_locate(literal),
            )),
        }
    }

    fn visit_primary(&self, primary: &Primary) -> Result<IdentifierOrLogic, ErrorMsg> {
        match primary {
            Primary::Hierarchical(h) => Ok(IdentifierOrLogic::Identifier(
                self.visit_hierarchical_primary(h)?,
            )),
            Primary::PrimaryLiteral(literal) => match self.visit_primary_literal(literal)? {
                Parameter::Logic(l) => Ok(IdentifierOrLogic::Logic(l)),
                _ => Err((
                    "Only logical literals are supported".to_string(),
                    self.unravel_locate(primary),
                )),
            },
            _ => Err((
                "Only hierarchical primary expressions and literals are supported".to_string(),
                self.unravel_locate(primary),
            )),
        }
    }

    /// For parsing connections
    fn visit_expression(&self, expr: &Expression) -> Result<IdentifierOrLogic, ErrorMsg> {
        match expr {
            Expression::Primary(p) => self.visit_primary(p),
            _ => Err((
                "Only primary expressions are supported".to_string(),
                self.unravel_locate(expr),
            )),
        }
    }

    fn visit_mintypmax_expression(
        &self,
        expr: &MintypmaxExpression,
    ) -> Result<Parameter, ErrorMsg> {
        match expr {
            MintypmaxExpression::Expression(e) => {
                let refnode: RefNode = e.as_ref().into();
                let refnode = unwrap_node!(refnode, Number);
                match refnode {
                    Some(RefNode::Number(x)) => self.visit_number(x),
                    _ => Err((
                        "Expected a Number parameter".to_string(),
                        self.unravel_locate(expr),
                    )),
                }
            }
            _ => Err((
                "Ternary in params not supported".to_string(),
                self.unravel_locate(expr),
            )),
        }
    }

    /// For parsinging parameter argument values
    fn visit_param_expression(&self, expr: &ParamExpression) -> Result<Parameter, ErrorMsg> {
        match expr {
            ParamExpression::MintypmaxExpression(e) => self.visit_mintypmax_expression(e),
            _ => Err((
                "Only expressions for parameters are supported".to_string(),
                self.unravel_locate(expr),
            )),
        }
    }

    fn visit_constant_range(&self, range: &ConstantRange) -> Result<(u64, u64), ErrorMsg> {
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
        Ok((l, r))
    }

    /// For parsing bus decl component
    fn visit_packed_dimension(&self, dim: &PackedDimension) -> Result<(u64, u64), ErrorMsg> {
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

    fn visit_net_port_type_data_type(&self, ntype: &NetPortTypeDataType) -> Result<u64, ErrorMsg> {
        let wire = &ntype.nodes.0;

        if !matches!(wire, Some(NetType::Wire(_)) | None) {
            return Err((
                format!("Only wire type net port types are supported ({wire:?})"),
                Locate::default(),
            ));
        }

        let nefnode: RefNode = ntype.into();
        let refnode = unwrap_node!(nefnode, PackedDimension);

        match refnode {
            Some(RefNode::PackedDimension(x)) => {
                let (l, r) = self.visit_packed_dimension(x)?;
                if r != 0 || l <= r {
                    return Err((
                        "Bus range should be N-1:0".to_string(),
                        self.unravel_locate(ntype),
                    ));
                }
                Ok(l + 1)
            }
            _ => Ok(1),
        }
    }

    /// Visit net port type to get bw
    fn visit_net_port_type(&self, ntype: &NetPortType) -> Result<u64, ErrorMsg> {
        match ntype {
            NetPortType::DataType(d) => self.visit_net_port_type_data_type(d),
            _ => Err((
                "Only data type net port types are supported".to_string(),
                self.unravel_locate(ntype),
            )),
        }
    }

    fn visit_net_port_header<'b>(
        &self,
        ph: &'b NetPortHeader,
    ) -> Result<(&'b PortDirection, u64), ErrorMsg> {
        let pt = self.visit_net_port_type(&ph.nodes.1)?;
        let direction = &ph.nodes.0;
        match direction {
            Some(dir) => Ok((dir, pt)),
            None => Err((
                "Port direction is required".to_string(),
                self.unravel_locate(ph),
            )),
        }
    }

    fn visit_constant_bit_select(
        &self,
        select: &ConstantBitSelect,
    ) -> Result<Option<u64>, ErrorMsg> {
        let expr = &select.nodes.0;
        if expr.is_empty() {
            return Ok(None);
        }
        if expr.len() != 1 {
            return Err((
                "Only single bit selects are supported".to_string(),
                self.unravel_locate(select),
            ));
        }
        let expr = &expr[0];
        let param = self.visit_constant_expression(&expr.nodes.1)?;
        if let Parameter::Integer(i) = param {
            Ok(Some(i))
        } else {
            Err((
                "Expected an integer for the bit select expression".to_string(),
                self.unravel_locate(select),
            ))
        }
    }

    fn visit_constant_select(&self, select: &ConstantSelect) -> Result<Option<u64>, ErrorMsg> {
        self.visit_constant_bit_select(&select.nodes.1)
    }
}

type Items<I> = (
    HashSet<Identifier>,
    HashMap<Identifier, NetRef<I>>,
    HashMap<Identifier, DrivenNet<I>>,
);

/// The visitor that iterates over basic items to create
struct ItemVisitor<'a, I: Instantiable + FromId, F: Fn(&Identifier, &I) -> Option<I>> {
    ast: &'a SyntaxTree,
    netlist: &'a Rc<Netlist<I>>,
    lookup: SemanticVisitor<'a>,
    outputs: HashSet<Identifier>,
    instances: HashMap<Identifier, NetRef<I>>,
    drivers: HashMap<Identifier, DrivenNet<I>>,
    overrides: F,
}

impl<'a, I: Instantiable + FromId, F: Fn(&Identifier, &I) -> Option<I>> ItemVisitor<'a, I, F> {
    fn new(ast: &'a SyntaxTree, netlist: &'a Rc<Netlist<I>>, overrides: F) -> Self {
        Self {
            ast,
            netlist,
            lookup: SemanticVisitor::new(ast),
            outputs: HashSet::new(),
            instances: HashMap::new(),
            drivers: HashMap::new(),
            overrides,
        }
    }

    fn visit(mut self) -> Result<Items<I>, (&'a SyntaxTree, ErrorMsg)> {
        let root = self.ast.into_iter().next().ok_or((
            self.ast,
            ("SourceText is empty".to_string(), Locate::default()),
        ))?;

        let decl = unwrap_node!(root, ModuleDeclaration);

        match decl {
            Some(RefNode::ModuleDeclaration(x)) => self
                .visit_module_declaration(x)
                .map_err(|e| (self.ast, e))?,
            _ => {
                return Err((
                    self.ast,
                    (
                        "Expected a ModuleDeclaration node".to_string(),
                        Locate::default(),
                    ),
                ));
            }
        }

        Ok((self.outputs, self.instances, self.drivers))
    }

    fn visit_module_identifier(&self, id: &ModuleIdentifier) {
        let id = self.lookup.visit_module_identifier(id);
        self.netlist.set_name(id.to_string())
    }

    fn visit_module_declaration(&mut self, decl: &ModuleDeclaration) -> Result<(), ErrorMsg> {
        let id: RefNode = decl.into();
        let id = unwrap_node!(id, ModuleIdentifier).unwrap();
        match id {
            RefNode::ModuleIdentifier(x) => self.visit_module_identifier(x),
            _ => unreachable!(),
        }

        match decl {
            ModuleDeclaration::Nonansi(f) => {
                let items = &f.nodes.2;
                for item in items {
                    self.visit_module_item(item)?;
                }
            }
            ModuleDeclaration::Ansi(f) => {
                let ports = &f.nodes.0;
                let ports = &ports.nodes.6;
                if let Some(ports) = ports {
                    self.visit_list_of_port_declarations(ports)?;
                }

                let items = &f.nodes.2;
                for item in items {
                    self.visit_non_port_module_item(item)?;
                }
            }
            _ => {
                return Err((
                    "Unsupported type of module declaration".to_string(),
                    self.lookup.unravel_locate(decl),
                ));
            }
        }

        Ok(())
    }

    fn visit_input_declaration_net(
        &mut self,
        decl: &InputDeclarationNet,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        let ntype = self.lookup.visit_net_port_type(&decl.nodes.1)?;
        let list = &decl.nodes.2;
        let ids = self.lookup.visit_list_of_port_identifiers(list)?;

        let ids = if ntype == 1 {
            ids
        } else {
            ids.into_iter()
                .flat_map(|id| (0..ntype).map(move |i| Identifier::new(format!("{}[{}]", id, i))))
                .collect()
        };

        let mut nets = Vec::new();
        for id in ids {
            let driver = self.netlist.insert_input(Net::new_logic(id.clone()));
            self.drivers.insert(id, driver.clone());
            nets.push(driver);
        }

        Ok(nets)
    }

    fn visit_input_declaration(
        &mut self,
        decl: &InputDeclaration,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        match decl {
            InputDeclaration::Net(n) => self.visit_input_declaration_net(n),
            InputDeclaration::Variable(_) => Err((
                "Variable input declarations are not supported".to_string(),
                self.lookup.unravel_locate(decl),
            )),
        }
    }

    fn visit_output_declaration_net(
        &mut self,
        decl: &OutputDeclarationNet,
    ) -> Result<(), ErrorMsg> {
        let ntype = self.lookup.visit_net_port_type(&decl.nodes.1)?;
        let list = &decl.nodes.2;
        let ids = self.lookup.visit_list_of_port_identifiers(list)?;

        let ids = if ntype == 1 {
            ids
        } else {
            ids.into_iter()
                .flat_map(|id| (0..ntype).map(move |i| Identifier::new(format!("{}[{}]", id, i))))
                .collect()
        };

        for id in ids {
            self.outputs.insert(id);
        }

        Ok(())
    }

    fn visit_output_declaration(&mut self, decl: &OutputDeclaration) -> Result<(), ErrorMsg> {
        match decl {
            OutputDeclaration::Net(n) => self.visit_output_declaration_net(n),
            OutputDeclaration::Variable(_) => Err((
                "Variable output declarations are not supported".to_string(),
                self.lookup.unravel_locate(decl),
            )),
        }
    }

    fn visit_port_declaration_input(
        &mut self,
        decl: &PortDeclarationInput,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        self.visit_input_declaration(&decl.nodes.1)
    }

    fn visit_port_declaration_output(
        &mut self,
        decl: &PortDeclarationOutput,
    ) -> Result<(), ErrorMsg> {
        self.visit_output_declaration(&decl.nodes.1)
    }

    fn visit_port_declaration(
        &mut self,
        decl: &PortDeclaration,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        match decl {
            PortDeclaration::Input(input) => self.visit_port_declaration_input(input),
            PortDeclaration::Output(output) => {
                self.visit_port_declaration_output(output)?;
                Ok(vec![])
            }
            _ => Err((
                "Only input and output port declarations are supported".to_string(),
                self.lookup.unravel_locate(decl),
            )),
        }
    }

    fn visit_named_port_connection_identifier(
        &self,
        inst: &I,
        conn: &NamedPortConnectionIdentifier,
    ) -> Result<(usize, bool, IdentifierOrLogic), ErrorMsg> {
        let port = self.lookup.visit_port_identifier(&conn.nodes.2);
        let Some(c) = &conn.nodes.3 else {
            return Err((
                "Expected a connection expression".to_string(),
                self.lookup.unravel_locate(conn),
            ));
        };

        let c = &c.nodes.1;

        let Some(expr) = c else {
            return Err((
                "Expected a connection expression".to_string(),
                self.lookup.unravel_locate(conn),
            ));
        };

        let c = self.lookup.visit_expression(expr)?;
        let (idx, is_output) = match (inst.find_input(&port), inst.find_output(&port)) {
            (Some(input), None) => (input, false),
            (None, Some(output)) => (output, true),
            (None, None) => {
                return Err((
                    format!("Port {port} not found on instance"),
                    self.lookup.unravel_locate(conn),
                ));
            }
            _ => unreachable!(),
        };

        Ok((idx, is_output, c))
    }

    fn visit_named_port_connection(
        &self,
        inst: &I,
        conn: &NamedPortConnection,
    ) -> Result<(usize, bool, IdentifierOrLogic), ErrorMsg> {
        match conn {
            NamedPortConnection::Identifier(id) => {
                self.visit_named_port_connection_identifier(inst, id)
            }
            NamedPortConnection::Asterisk(_) => Err((
                "Asterisk port connections are not supported".to_string(),
                self.lookup.unravel_locate(conn),
            )),
        }
    }

    fn visit_list_of_port_connections_named(
        &self,
        inst: &I,
        list: &ListOfPortConnectionsNamed,
    ) -> Result<Vec<(usize, bool, IdentifierOrLogic)>, ErrorMsg> {
        let list = &list.nodes.0;
        let mut res = Vec::new();
        for c in list.contents() {
            res.push(self.visit_named_port_connection(inst, c)?);
        }
        Ok(res)
    }

    fn visit_list_of_port_connections(
        &self,
        inst: &I,
        list: &ListOfPortConnections,
    ) -> Result<Vec<(usize, bool, IdentifierOrLogic)>, ErrorMsg> {
        match list {
            ListOfPortConnections::Named(list) => {
                self.visit_list_of_port_connections_named(inst, list)
            }
            _ => Err((
                "Only named port connections are supported".to_string(),
                self.lookup.unravel_locate(list),
            )),
        }
    }

    fn visit_hierarchical_instance(
        &mut self,
        i: I,
        inst: &HierarchicalInstance,
    ) -> Result<NetRef<I>, ErrorMsg> {
        let name = &inst.nodes.0;
        let name = &name.nodes.0;
        let name = self.lookup.visit_instance_identifier(name);

        let connections = &inst.nodes.1;
        let connections = &connections.nodes.1;
        let mut vec: Vec<(usize, Identifier)> = Vec::new();
        if let Some(connections) = connections {
            vec = self
                .visit_list_of_port_connections(&i, connections)?
                .into_iter()
                .filter_map(|(idx, output, driving)| {
                    if output && let IdentifierOrLogic::Identifier(driver) = driving {
                        Some((idx, driver))
                    } else {
                        None
                    }
                })
                .collect();
        }
        let ans = self.netlist.insert_gate_disconnected(i, name.clone());
        self.instances.insert(name, ans.clone());

        for (idx, driving) in vec {
            ans.get_output(idx)
                .as_net_mut()
                .set_identifier(driving.clone());
            if self.outputs.contains(&driving) {
                ans.get_output(idx).expose_with_name(driving.clone());
            }
            self.drivers.insert(driving, ans.get_output(idx));
        }

        Ok(ans)
    }

    fn visit_named_parameter_assignment(
        &self,
        p: &NamedParameterAssignment,
    ) -> Result<(Identifier, Parameter), ErrorMsg> {
        let key = self.lookup.visit_parameter_identifier(&p.nodes.1);
        let val = &p.nodes.2;
        let val = &val.nodes.1;
        let Some(val) = val else {
            return Err((
                "Expected a parameter value".to_string(),
                self.lookup.unravel_locate(p),
            ));
        };

        let val = self.lookup.visit_param_expression(val)?;

        Ok((key, val))
    }

    fn visit_list_of_parameter_assignments_named(
        &self,
        list: &ListOfParameterAssignmentsNamed,
    ) -> Result<Vec<(Identifier, Parameter)>, ErrorMsg> {
        let list = &list.nodes.0;
        let mut res = Vec::new();
        for p in list.contents() {
            res.push(self.visit_named_parameter_assignment(p)?);
        }
        Ok(res)
    }

    fn visit_list_of_parameter_assignments(
        &self,
        list: &ListOfParameterAssignments,
    ) -> Result<Vec<(Identifier, Parameter)>, ErrorMsg> {
        match list {
            ListOfParameterAssignments::Named(list) => {
                self.visit_list_of_parameter_assignments_named(list)
            }
            ListOfParameterAssignments::Ordered(_) => Err((
                "Ordered parameter assignments are not supported".to_string(),
                self.lookup.unravel_locate(list),
            )),
        }
    }

    fn visit_parameter_value_assignment(
        &self,
        p: &ParameterValueAssignment,
    ) -> Result<Vec<(Identifier, Parameter)>, ErrorMsg> {
        let list = &p.nodes.1;
        let list = &list.nodes.1;
        match list {
            Some(list) => self.visit_list_of_parameter_assignments(list),
            None => Ok(vec![]),
        }
    }

    fn visit_module_instantiation(
        &mut self,
        inst: &ModuleInstantiation,
    ) -> Result<Vec<NetRef<I>>, ErrorMsg> {
        let inst_type_name = self.lookup.visit_module_identifier(&inst.nodes.0);
        let inst_type = I::from_id(&inst_type_name).map_err(|e| {
            (
                format!("Unknown instantiable type: {}", e),
                self.lookup.unravel_locate(inst),
            )
        })?;

        let mut inst_type = match (self.overrides)(&inst_type_name, &inst_type) {
            Some(overridden) => overridden,
            None => inst_type,
        };

        let params = &inst.nodes.1;
        if let Some(params) = params {
            let assignments = self.visit_parameter_value_assignment(params)?;
            for (id, value) in assignments {
                inst_type.set_parameter(&id, value);
            }
        }

        let instances = &inst.nodes.2;
        let mut vec = Vec::new();
        for instance in instances.contents() {
            vec.push(self.visit_hierarchical_instance(inst_type.clone(), instance)?);
        }
        Ok(vec)
    }

    fn visit_package_or_generate_item_declaration(
        &self,
        item: &PackageOrGenerateItemDeclaration,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        match item {
            PackageOrGenerateItemDeclaration::NetDeclaration(decl) => match decl.as_ref() {
                NetDeclaration::NetType(ntype) => {
                    if !matches!(ntype.nodes.0, NetType::Wire(_)) {
                        Err((
                            "Only wire typed declarations are supported".to_string(),
                            self.lookup.unravel_locate(item),
                        ))
                    } else {
                        Ok(vec![])
                    }
                }
                _ => Err((
                    "Only wire typed declarations are supported".to_string(),
                    self.lookup.unravel_locate(item),
                )),
            },
            _ => Err((
                "Only wire decl constructs are allowed".to_string(),
                self.lookup.unravel_locate(item),
            )),
        }
    }

    fn visit_module_or_generate_item_declaration(
        &self,
        item: &ModuleOrGenerateItemDeclaration,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        match item {
            ModuleOrGenerateItemDeclaration::PackageOrGenerateItemDeclaration(pkg) => {
                self.visit_package_or_generate_item_declaration(pkg)
            }
            _ => Err((
                "Only wire decl constructs are allowed".to_string(),
                self.lookup.unravel_locate(item),
            )),
        }
    }

    fn visit_module_common_item(
        &self,
        item: &ModuleCommonItem,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        match item {
            ModuleCommonItem::ModuleOrGenerateItemDeclaration(decl) => {
                self.visit_module_or_generate_item_declaration(decl)
            }
            ModuleCommonItem::ContinuousAssign(_) =>
            // Handled by wire visitor
            {
                Ok(vec![])
            }
            _ => Err((
                "Only wire decl and assignment constructs are allowed".to_string(),
                self.lookup.unravel_locate(item),
            )),
        }
    }

    fn visit_module_or_generate_item_module_item(
        &self,
        item: &ModuleOrGenerateItemModuleItem,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        self.visit_module_common_item(&item.nodes.1)
    }

    fn visit_module_or_generate_item_module(
        &mut self,
        item: &ModuleOrGenerateItemModule,
    ) -> Result<Vec<NetRef<I>>, ErrorMsg> {
        self.visit_module_instantiation(&item.nodes.1)
    }

    fn visit_module_or_generate_item(
        &mut self,
        item: &ModuleOrGenerateItem,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        match item {
            ModuleOrGenerateItem::Module(m) => Ok(self
                .visit_module_or_generate_item_module(m)?
                .into_iter()
                .flat_map(|nr| nr.outputs().collect::<Vec<_>>())
                .collect()),
            ModuleOrGenerateItem::ModuleItem(mi) => {
                self.visit_module_or_generate_item_module_item(mi)
            }
            _ => Err((
                "Only cell instances and wires are allowed".to_string(),
                self.lookup.unravel_locate(item),
            )),
        }
    }

    fn visit_non_port_module_item(
        &mut self,
        item: &NonPortModuleItem,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        match item {
            NonPortModuleItem::ModuleOrGenerateItem(item) => {
                self.visit_module_or_generate_item(item)
            }
            _ => Err((
                "Only cell instances and wires are allowed".to_string(),
                self.lookup.unravel_locate(item),
            )),
        }
    }

    fn visit_module_item(&mut self, item: &ModuleItem) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        match item {
            ModuleItem::NonPortModuleItem(item) => self.visit_non_port_module_item(item),
            ModuleItem::PortDeclaration(p) => self.visit_port_declaration(&p.0),
        }
    }

    fn visit_ansi_port_declaration_net(
        &mut self,
        decl: &AnsiPortDeclarationNet,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        if !decl.nodes.2.is_empty() {
            return Err((
                "Only simple port declarations are supported".to_string(),
                self.lookup.unravel_locate(decl),
            ));
        }

        let id = self.lookup.visit_port_identifier(&decl.nodes.1);

        let (dir, bw) = match &decl.nodes.0 {
            Some(NetPortHeaderOrInterfacePortHeader::NetPortHeader(ph)) => {
                self.lookup.visit_net_port_header(ph)?
            }
            _ => {
                return Err((
                    "Net port header is required".to_string(),
                    self.lookup.unravel_locate(decl),
                ));
            }
        };

        let ids = if bw == 1 {
            vec![id]
        } else {
            (0..bw)
                .map(move |i| Identifier::new(format!("{}[{}]", id, i)))
                .collect()
        };

        match dir {
            PortDirection::Input(_) => Ok(ids
                .into_iter()
                .map(|id| {
                    let driver = self.netlist.insert_input(Net::new_logic(id.clone()));
                    self.drivers.insert(id, driver.clone());
                    driver
                })
                .collect()),
            PortDirection::Output(_) => {
                for id in ids {
                    self.outputs.insert(id);
                }
                Ok(vec![])
            }
            _ => Err((
                "Only input and output port directions are supported".to_string(),
                self.lookup.unravel_locate(decl),
            )),
        }
    }

    fn visit_ansi_port_declaration(
        &mut self,
        decl: &AnsiPortDeclaration,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        match decl {
            AnsiPortDeclaration::Net(net) => self.visit_ansi_port_declaration_net(net),
            _ => Err((
                "Only net port declarations are supported".to_string(),
                self.lookup.unravel_locate(decl),
            )),
        }
    }

    fn visit_list_of_port_declarations(
        &mut self,
        list: &ListOfPortDeclarations,
    ) -> Result<Vec<DrivenNet<I>>, ErrorMsg> {
        let list = &list.nodes.0;
        let list = &list.nodes.1;
        match list {
            Some(list) => {
                let mut nets = Vec::new();
                for decl in list.contents() {
                    let decl = &decl.1;
                    nets.append(&mut self.visit_ansi_port_declaration(decl)?);
                }
                Ok(nets)
            }
            None => Ok(vec![]),
        }
    }
}

type Wires<I> = (HashSet<Identifier>, bool, HashMap<Identifier, DrivenNet<I>>);

/// The visitor that iterates over basic items to create
struct WireVisitor<'a, I: Instantiable> {
    ast: &'a SyntaxTree,
    netlist: &'a Rc<Netlist<I>>,
    lookup: SemanticVisitor<'a>,
    outputs: HashSet<Identifier>,
    drivers: HashMap<Identifier, DrivenNet<I>>,
    changed: bool,
}

impl<'a, I: Instantiable> WireVisitor<'a, I> {
    fn new(
        ast: &'a SyntaxTree,
        netlist: &'a Rc<Netlist<I>>,
        outputs: HashSet<Identifier>,
        drivers: HashMap<Identifier, DrivenNet<I>>,
    ) -> Self {
        Self {
            ast,
            netlist,
            lookup: SemanticVisitor::new(ast),
            outputs,
            drivers,
            changed: false,
        }
    }

    fn visit(mut self) -> Result<Wires<I>, (&'a SyntaxTree, ErrorMsg)> {
        for n in self.ast {
            if let RefNode::ContinuousAssign(assign) = n {
                self.changed |= self
                    .visit_continuous_assign(assign)
                    .map_err(|e| (self.ast, e))?;
            }
        }

        Ok((self.outputs, self.changed, self.drivers))
    }

    fn visit_hierarchical_net_identifier(
        &self,
        id: &HierarchicalNetIdentifier,
    ) -> Result<Identifier, ErrorMsg> {
        self.lookup.visit_hierarchical_identifier(&id.nodes.0)
    }

    fn visit_ps_or_hierarchical_net_identifier_package_scope(
        &self,
        id: &PsOrHierarchicalNetIdentifierPackageScope,
    ) -> Identifier {
        self.lookup.visit_net_identifier(&id.nodes.1)
    }

    fn visit_ps_or_hierarchical_net_identifier(
        &self,
        id: &PsOrHierarchicalNetIdentifier,
    ) -> Result<Identifier, ErrorMsg> {
        match id {
            PsOrHierarchicalNetIdentifier::HierarchicalNetIdentifier(id) => {
                self.visit_hierarchical_net_identifier(id)
            }
            PsOrHierarchicalNetIdentifier::PackageScope(pc) => {
                Ok(self.visit_ps_or_hierarchical_net_identifier_package_scope(pc))
            }
        }
    }

    fn visit_net_lvalue_identifier(
        &self,
        id: &NetLvalueIdentifier,
    ) -> Result<Identifier, ErrorMsg> {
        let ident = self.visit_ps_or_hierarchical_net_identifier(&id.nodes.0)?;
        let select = self.lookup.visit_constant_select(&id.nodes.1)?;
        match select {
            Some(s) => Ok(Identifier::new(format!("{}[{}]", ident, s))),
            None => Ok(ident),
        }
    }

    fn visit_net_lvalue(&self, lvalue: &NetLvalue) -> Result<Identifier, ErrorMsg> {
        match lvalue {
            NetLvalue::Identifier(id) => self.visit_net_lvalue_identifier(id),
            _ => Err((
                "Only identifier lvalues are supported".to_string(),
                self.lookup.unravel_locate(lvalue),
            )),
        }
    }

    fn visit_net_assignment(&mut self, assign: &NetAssignment) -> Result<bool, ErrorMsg> {
        let lhs = &assign.nodes.0;
        let rhs = &assign.nodes.2;
        let lhs = self.visit_net_lvalue(lhs)?;
        let rhs = self.lookup.visit_expression(rhs)?;

        let rhs = match rhs {
            IdentifierOrLogic::Identifier(id) => id,
            IdentifierOrLogic::Logic(val) => {
                let Some(inst) = I::from_constant(val) else {
                    return Err((
                        "Instiable type does not support constant".to_string(),
                        self.lookup.unravel_locate(assign),
                    ));
                };
                let inst_name = lhs.clone() + "const".into();
                let dnet = self
                    .netlist
                    .insert_gate_disconnected(inst, inst_name)
                    .get_output(0);
                let output = dnet.as_net().get_identifier().clone();
                self.drivers.insert(output.clone(), dnet);
                output
            }
        };

        if let Some(driver) = self.drivers.get(&rhs).cloned()
            && !self.drivers.contains_key(&lhs)
        {
            if self.outputs.contains(&lhs) {
                driver.clone().expose_with_name(lhs.clone());
            }
            self.drivers.insert(lhs, driver);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn visit_list_of_net_assignments(
        &mut self,
        assign: &ListOfNetAssignments,
    ) -> Result<bool, ErrorMsg> {
        let mut changed = false;
        for stmt in assign.nodes.0.contents() {
            changed |= self.visit_net_assignment(stmt)?;
        }
        Ok(changed)
    }

    fn visit_continuous_assign_net(
        &mut self,
        assign: &ContinuousAssignNet,
    ) -> Result<bool, ErrorMsg> {
        let list = &assign.nodes.3;
        self.visit_list_of_net_assignments(list)
    }

    fn visit_continuous_assign(&mut self, assign: &ContinuousAssign) -> Result<bool, ErrorMsg> {
        match assign {
            ContinuousAssign::Net(assign) => self.visit_continuous_assign_net(assign),
            ContinuousAssign::Variable(_) => Err((
                "Variable assignments are not supported".to_string(),
                self.lookup.unravel_locate(assign),
            )),
        }
    }
}

fn set_default_drivers<I: Instantiable>(
    outputs: &HashSet<Identifier>,
    drivers: &mut HashMap<Identifier, DrivenNet<I>>,
    netlist: &Rc<Netlist<I>>,
) -> Result<(), VerilogError> {
    // Handle undriven outputs
    for output in outputs {
        if !drivers.contains_key(output) {
            let inst =
                I::from_constant(Logic::Z).unwrap_or(I::from_constant(Logic::False).unwrap());
            let id = output.clone() + "default_logic".into();
            let net = netlist
                .insert_gate(inst, id, &[])
                .map_err(|e| VerilogError::SafetyNetError(None, e))?
                .get_output(0);
            netlist.expose_net_with_name(net.clone(), output.clone());
            drivers.insert(output.clone(), net);
        }
    }
    Ok(())
}

/// The visitor that connects all the drivers at their uses
struct InputVisitor<'a, I: Instantiable> {
    ast: &'a SyntaxTree,
    netlist: &'a Rc<Netlist<I>>,
    lookup: SemanticVisitor<'a>,
    instances: HashMap<Identifier, NetRef<I>>,
    drivers: HashMap<Identifier, DrivenNet<I>>,
}

impl<'a, I: Instantiable> InputVisitor<'a, I> {
    fn new(
        ast: &'a SyntaxTree,
        netlist: &'a Rc<Netlist<I>>,
        instances: HashMap<Identifier, NetRef<I>>,
        drivers: HashMap<Identifier, DrivenNet<I>>,
    ) -> Self {
        Self {
            ast,
            netlist,
            lookup: SemanticVisitor::new(ast),
            instances,
            drivers,
        }
    }

    fn visit(self) -> Result<(), (&'a SyntaxTree, ErrorMsg)> {
        for n in self.ast {
            if let RefNode::HierarchicalInstance(inst) = n {
                self.visit_hierarchical_instance(inst)
                    .map_err(|e| (self.ast, e))?;
            }
        }
        Ok(())
    }

    fn visit_named_port_connection_identifier(
        &self,
        inst: &I,
        conn: &NamedPortConnectionIdentifier,
    ) -> Result<(usize, bool, IdentifierOrLogic), ErrorMsg> {
        let port = self.lookup.visit_port_identifier(&conn.nodes.2);
        let Some(c) = &conn.nodes.3 else {
            return Err((
                "Expected a connection expression".to_string(),
                self.lookup.unravel_locate(conn),
            ));
        };

        let c = &c.nodes.1;

        let Some(expr) = c else {
            return Err((
                "Expected a connection expression".to_string(),
                self.lookup.unravel_locate(conn),
            ));
        };

        let c = self.lookup.visit_expression(expr)?;
        let (idx, is_output) = match (inst.find_input(&port), inst.find_output(&port)) {
            (Some(input), None) => (input, false),
            (None, Some(output)) => (output, true),
            (None, None) => {
                return Err((
                    format!("Port {port} not found on instance"),
                    self.lookup.unravel_locate(conn),
                ));
            }
            _ => unreachable!(),
        };

        Ok((idx, is_output, c))
    }

    fn visit_named_port_connection(
        &self,
        inst: &I,
        conn: &NamedPortConnection,
    ) -> Result<(usize, bool, IdentifierOrLogic), ErrorMsg> {
        match conn {
            NamedPortConnection::Identifier(id) => {
                self.visit_named_port_connection_identifier(inst, id)
            }
            NamedPortConnection::Asterisk(_) => Err((
                "Asterisk port connections are not supported".to_string(),
                self.lookup.unravel_locate(conn),
            )),
        }
    }

    fn visit_list_of_port_connections_named(
        &self,
        inst: &I,
        list: &ListOfPortConnectionsNamed,
    ) -> Result<Vec<(usize, bool, IdentifierOrLogic)>, ErrorMsg> {
        let list = &list.nodes.0;
        let mut res = Vec::new();
        for c in list.contents() {
            res.push(self.visit_named_port_connection(inst, c)?);
        }
        Ok(res)
    }

    fn visit_list_of_port_connections(
        &self,
        inst: &I,
        list: &ListOfPortConnections,
    ) -> Result<Vec<(usize, bool, IdentifierOrLogic)>, ErrorMsg> {
        match list {
            ListOfPortConnections::Named(list) => {
                self.visit_list_of_port_connections_named(inst, list)
            }
            _ => Err((
                "Only named port connections are supported".to_string(),
                self.lookup.unravel_locate(list),
            )),
        }
    }

    fn visit_hierarchical_instance(&self, inst: &HierarchicalInstance) -> Result<(), ErrorMsg> {
        let name = &inst.nodes.0;
        let name = &name.nodes.0;
        let name = self.lookup.visit_instance_identifier(name);
        let nr = self.instances.get(&name).ok_or((
            format!("Instance {name} not inserted into netlist"),
            self.lookup.unravel_locate(inst),
        ))?;

        let connections = &inst.nodes.1;
        let connections = &connections.nodes.1;
        let mut vec: Vec<(usize, DrivenNet<I>)> = Vec::new();
        let Some(i) = nr.get_instance_type().map(|i| i.clone()) else {
            return Ok(());
        };

        if let Some(connections) = connections {
            for (idx, output, driving) in self.visit_list_of_port_connections(&i, connections)? {
                if !output {
                    let driver = match driving {
                        IdentifierOrLogic::Identifier(id) => self.drivers[&id].clone(),
                        IdentifierOrLogic::Logic(val) => {
                            let Some(inst) = I::from_constant(val) else {
                                return Err((
                                    "Instiable type does not support constant".to_string(),
                                    self.lookup.unravel_locate(inst),
                                ));
                            };
                            let inst_name = name.clone()
                                + i.get_input_port(idx).get_identifier().clone()
                                + "const".into();
                            self.netlist
                                .insert_gate_disconnected(inst, inst_name)
                                .get_output(0)
                        }
                    };
                    vec.push((idx, driver));
                }
            }
        }

        for (idx, driving) in vec {
            nr.get_input(idx).connect(driving);
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
    let netlist = Netlist::<I>::new("top".to_string());
    let item_visitor = ItemVisitor::new(ast, &netlist, overrides);
    let (outputs, instances, drivers) = item_visitor
        .visit()
        .map_err(|(_, (s, l))| VerilogError::Other(Some(l), s))?;

    let (mut outputs, mut changing, mut drivers) = (outputs, true, drivers);
    while changing {
        let wire_visitor = WireVisitor::new(ast, &netlist, outputs, drivers);
        (outputs, changing, drivers) = wire_visitor
            .visit()
            .map_err(|(_, (s, l))| VerilogError::Other(Some(l), s))?;
    }

    set_default_drivers(&outputs, &mut drivers, &netlist)?;

    let input_visitor = InputVisitor::new(ast, &netlist, instances, drivers);
    input_visitor
        .visit()
        .map_err(|(_, (s, l))| VerilogError::Other(Some(l), s))?;

    Ok(netlist)
}

/// Construct a Safety Net [Netlist] from a Verilog netlist AST.
/// Type parameter I defines the primitive library to parse into.
pub fn from_vast<I: Instantiable + FromId>(
    ast: &sv_parser::SyntaxTree,
) -> Result<Rc<Netlist<I>>, VerilogError> {
    from_vast_overrides::<I, _>(ast, |_, _| None)
}
