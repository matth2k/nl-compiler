/*!

  Error types

*/

use crate::aig::U;
use std::{fmt::Display, path::PathBuf};
use sv_parser::{RefNode, RefNodes, SyntaxTree, unwrap_node};
use thiserror::Error;

/// Errors for Verilog Compilation.
#[derive(Error, Debug)]
pub struct VerilogError {
    origin: Option<(PathBuf, usize)>,
    message: String,
    content: String,
}

impl VerilogError {
    /// Create a new error from an AST node
    pub fn new<'a, T: Into<RefNodes<'a>> + Into<RefNode<'a>> + Clone, K>(
        ast: &'a SyntaxTree,
        nodes: T,
        message: String,
    ) -> Result<K, Self> {
        let content = match ast.get_str_trim(nodes.clone()) {
            Some(s) => s.lines().next().unwrap_or("").to_string(),
            None => String::new(),
        };
        let rn: RefNode<'_> = nodes.into();
        let locate = match unwrap_node!(rn, Locate) {
            Some(RefNode::Locate(l)) => Some(*l),
            _ => None,
        };
        let origin = match locate {
            Some(l) => ast.get_origin(&l),
            None => None,
        };
        let origin = origin.map(|(p, l)| (p.clone(), l));
        Err(Self {
            origin,
            message,
            content,
        })
    }
}

impl Default for VerilogError {
    fn default() -> Self {
        Self {
            origin: None,
            message: "Source text is missing".to_string(),
            content: String::new(),
        }
    }
}

impl Display for VerilogError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some((path, line)) = &self.origin {
            write!(f, "{}:{}: ", path.display(), line)?;
        }
        writeln!(f, "{}", self.message)?;
        if !self.content.is_empty() {
            writeln!(f, ">    {}", self.content)?;
        }
        Ok(())
    }
}

/// Errors for AIG Compilation.
#[derive(Error, Debug)]
pub enum AigError {
    /// Contains bad state properties.
    #[error("Contains bad state properties `{0:?}`")]
    ContainsBadStates(Vec<U>),
    /// Contains latches.
    #[error("Contains latches `{0:?}`")]
    ContainsLatches(Vec<U>),
    /// Attempted aig contains cycles.
    #[error("Attempted aig contains cycles")]
    ContainsCycle,
    /// Attempted aig contains gates besides AND and INV.
    #[error("Attempted aig contains gates besides AND and INV")]
    ContainsOtherGates,
    /// Attempted aig has disconnected gates.
    #[error("Attempted aig has disconnected gates.")]
    DisconnectedGates,
    /// An error originating from `safety-net`.
    #[error("Safety net error `{0}`")]
    SafetyNetError(#[from] safety_net::Error),
    /// An error originating from `flussab`.
    #[error("flussab error `{0}`")]
    FlussabError(#[from] flussab_aiger::aig::AigStructureError<crate::aig::U>),
    /// An error originating from `io`.
    #[error("IO error `{0}`")]
    IoError(#[from] std::io::Error),
}
