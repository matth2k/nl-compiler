/*!

  Compile AIG to Safety Net netlist

*/

use crate::cells::FromId;
use flussab_aiger::aig::Aig;
use safety_net::{
    circuit::{Identifier, Instantiable, Net},
    netlist::{DrivenNet, Netlist},
};
use std::{collections::HashMap, rc::Rc};

/// What [Identifier] to map AND gates to
pub const AIG_AND: &str = "AND";
/// What [Identifier] to map inverters to
pub const AIG_INV: &str = "INV";
/// The index type for the AIG
pub type U = u64;

/// Construct a Safety Net [Netlist] from a AIG
/// Type parameter I defines the primitive library to parse into.
pub fn from_aig<I: Instantiable + FromId>(
    aig: &Aig<U>,
    name: String,
) -> Result<Rc<Netlist<I>>, String> {
    let netlist = Netlist::<I>::new(name);

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
        let inverted = netlist.insert_gate(
            I::from_id(&Identifier::new(AIG_INV.to_string()))?,
            inv_id,
            &[n],
        )?;
        mapping.insert(u + 1, inverted.get_output(0));
    }

    for gate in &aig.and_gates {
        let id = Identifier::new(gate.output.to_string());
        let inv_id = id.clone() + "_inv".into();
        let operands: Vec<_> = gate.inputs.iter().map(|u| mapping[u].clone()).collect();
        let n = netlist
            .insert_gate(
                I::from_id(&Identifier::new(AIG_AND.to_string()))?,
                id,
                &operands,
            )?
            .get_output(0);
        mapping.insert(gate.output, n.clone());
        let inverted = netlist.insert_gate(
            I::from_id(&Identifier::new(AIG_INV.to_string()))?,
            inv_id,
            std::slice::from_ref(&n),
        )?;
        mapping.insert(gate.output + 1, inverted.get_output(0));
    }

    // TODO: check latches and bad state

    for o in &aig.outputs {
        let n = mapping[o].clone();
        netlist.expose_net(n)?;
    }

    netlist.clean()?;

    Ok(netlist)
}
