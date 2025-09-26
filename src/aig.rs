/*!

  Compile AIG to Safety Net netlist

*/

use crate::error::AigError;
use flussab_aiger::aig::Aig;
use safety_net::{
    circuit::{Identifier, Instantiable, Net},
    netlist::{DrivenNet, Netlist},
};
use std::{collections::HashMap, rc::Rc};

/// The index type for the AIG
pub type U = u64;

/// Construct a Safety Net [Netlist] from a AIG
/// Type parameter I defines the primitive library to parse into.
pub fn from_aig<I: Instantiable>(aig: &Aig<U>, and: I, inv: I) -> Result<Rc<Netlist<I>>, AigError> {
    if !aig.bad_state_properties.is_empty() {
        return Err(AigError::ContainsBadStates(
            aig.bad_state_properties.clone(),
        ));
    }

    if !aig.latches.is_empty() {
        return Err(AigError::ContainsLatches(
            aig.latches.iter().map(|l| l.state).collect(),
        ));
    }

    let netlist = Netlist::<I>::new("top".to_string());

    let inputs: Vec<(U, Identifier)> = aig
        .inputs
        .iter()
        .map(|&id| (id, id.to_string().into()))
        .collect();

    let inputs: Vec<(U, DrivenNet<I>)> = inputs
        .into_iter()
        .map(|(u, id)| (u, netlist.insert_input(Net::new_logic(id))))
        .collect();

    let mut mapping: HashMap<U, DrivenNet<I>> = HashMap::new();

    for (u, n) in inputs {
        mapping.insert(u, n.clone());
        let inv_id = n.get_identifier() + "_inv".into();
        let inverted = netlist.insert_gate(inv.clone(), inv_id, &[n])?;
        mapping.insert(u + 1, inverted.get_output(0));
    }

    for gate in &aig.and_gates {
        let id = Identifier::new(gate.output.to_string());
        let inv_id = id.clone() + "_inv".into();
        let operands: Vec<_> = gate.inputs.iter().map(|u| mapping[u].clone()).collect();
        let n = netlist
            .insert_gate(and.clone(), id, &operands)?
            .get_output(0);
        mapping.insert(gate.output, n.clone());
        let inverted = netlist.insert_gate(inv.clone(), inv_id, std::slice::from_ref(&n))?;
        mapping.insert(gate.output + 1, inverted.get_output(0));
    }

    for o in &aig.outputs {
        let n = mapping[o].clone();
        netlist.expose_net(n)?;
    }

    netlist.clean()?;

    Ok(netlist)
}
