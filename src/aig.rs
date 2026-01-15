/*!

  Compile AIG to Safety Net netlist

*/

use crate::error::AigError;
use flussab::DeferredWriter;
use flussab_aiger::aig::{Aig, AndGate, Renumber, RenumberConfig};
use flussab_aiger::ascii;
use safety_net::iter::DFSIterator;
use safety_net::{DrivenNet, Identifier, Instantiable, Logic, Net, Netlist};
use std::collections::HashSet;
use std::{collections::HashMap, io::Write, rc::Rc};

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

/// Write an AIG to an ASCII file
pub fn write_aig<'a>(aig: &Aig<U>, output: impl Write + 'a) -> Result<(), AigError> {
    let mut aag_writer = DeferredWriter::from_write(output);
    let aag_writer = ascii::Writer::<U>::new(&mut aag_writer);

    let (aig, _) = Renumber::renumber_aig(
        RenumberConfig::default()
            .trim(false)
            .structural_hash(false)
            .const_fold(false),
        aig,
    )?;

    aag_writer.write_ordered_aig(&aig);

    aag_writer.flush()?;
    Ok(())
}

fn topo_sort_iter<I: Instantiable>(
    netlist: &Netlist<I>,
    item: DrivenNet<I>,
    sorted: &mut Vec<DrivenNet<I>>,
    rdy: &mut HashSet<DrivenNet<I>>,
) -> Result<(), AigError> {
    if rdy.contains(&item) {
        return Ok(());
    }

    let mut dfs = DFSIterator::new(netlist, item.clone().unwrap());
    dfs.next();
    while let Some(n) = dfs.next() {
        if n.is_an_input() {
            continue;
        }

        if n.outputs().count() != 1 {
            return Err(AigError::ContainsOtherGates);
        }

        if dfs.check_cycles() {
            return Err(AigError::ContainsCycle);
        }

        let output = n.get_output(0);
        if !rdy.contains(&output) {
            topo_sort_iter(netlist, output, sorted, rdy)?;
        }
    }

    rdy.insert(item.clone());
    if !item.is_an_input() {
        sorted.push(item);
    }

    Ok(())
}

fn topo_sort<I: Instantiable>(netlist: &Netlist<I>) -> Result<Vec<DrivenNet<I>>, AigError> {
    let mut sorted = Vec::new();
    let mut rdy = HashSet::new();

    for (output, _) in netlist.outputs() {
        topo_sort_iter(netlist, output, &mut sorted, &mut rdy)?;
    }
    Ok(sorted)
}

/// Convert a Safety Net [Netlist] to an AIG
pub fn to_aig<I: Instantiable, And: Fn(&I) -> bool, Inv: Fn(&I) -> bool>(
    netlist: &Rc<Netlist<I>>,
    and: And,
    inv: Inv,
) -> Result<Aig<U>, AigError> {
    let mut aig = Aig::<U>::default();

    let mut mapping: HashMap<DrivenNet<I>, U> = HashMap::new();
    for input in netlist.inputs() {
        let id = aig.inputs.len() as U * 2 + 2;
        mapping.insert(input.clone(), id);
        aig.inputs.push(id);
    }

    // Aig is supposed to be acyclic
    let nodes = topo_sort(netlist)?;

    for gate in nodes {
        if mapping.contains_key(&gate) {
            continue;
        }

        if inv(&gate.get_instance_type().unwrap()) {
            let input = gate
                .clone()
                .unwrap()
                .get_input(0)
                .get_driver()
                .ok_or(AigError::DisconnectedGates)?;
            let id = mapping[&input] + 1;
            mapping.insert(gate, id);
        } else if and(&gate.get_instance_type().unwrap()) {
            let input1 = gate
                .clone()
                .unwrap()
                .get_input(0)
                .get_driver()
                .ok_or(AigError::DisconnectedGates)?;
            let input2 = gate
                .clone()
                .unwrap()
                .get_input(1)
                .get_driver()
                .ok_or(AigError::DisconnectedGates)?;
            let id = (aig.and_gates.len() as U * 2) + (aig.inputs.len() as U * 2) + 2;
            let input_ids = [mapping[&input1], mapping[&input2]];
            aig.and_gates.push(AndGate {
                output: id,
                inputs: input_ids,
            });
            mapping.insert(gate, id);
        } else if let Some(b) = gate.clone().get_instance_type().unwrap().get_constant() {
            let id = match b {
                Logic::False => 0,
                Logic::True => 1,
                _ => return Err(AigError::ContainsOtherGates),
            };
            mapping.insert(gate, id);
        } else {
            return Err(AigError::ContainsOtherGates);
        }
    }

    for (output, _) in netlist.outputs() {
        let id = mapping[&output];
        aig.outputs.push(id);
    }

    aig.max_var_index = aig.inputs.len() + 1;
    aig.comment = Some(format!(
        "/* Generated by {} {} */",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION")
    ));
    Ok(aig)
}
