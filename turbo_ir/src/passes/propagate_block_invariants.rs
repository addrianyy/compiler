use crate::{FunctionData, Map, Label, Value, Location, Instruction, IntPredicate,
            Type, analysis::Const};

fn get_invariant_value(
    function: &FunctionData,
    from:     Label,
    to:       Label,
    creators: &Map<Value, Location>,
    consts:   &Map<Value, (Type, Const)>,
) -> Option<(Value, Value)> {
    // We can get invariant value if `from` ends with conditional branch with condition being
    // a result from `icmp ne` or `icmp eq` instruction.

    // Get the conditional branch at the end of `from`.
    if let Instruction::BranchCond { cond, on_true, on_false } = function.last_instruction(from) {
        let creator = creators.get(cond).map(|location| function.instruction(*location));

        // Get the `icmp` instruction that is used as `bcond` condition.
        if let Some(Instruction::IntCompare { a, pred, b, .. }) = creator {
            // We cannot get invariant if on_true == on_false or a == b
            // (it's an unconditional branch then).
            if on_true == on_false || a == b {
                return None;
            }

            // if (a == b) { label1 } else { label2 } => we know that in `label1` a == b.
            // if (a != b) { label1 } else { label2 } => we know that in `label2` a == b.
            if (*pred == IntPredicate::Equal    && *on_true  == to) ||
               (*pred == IntPredicate::NotEqual && *on_false == to) {
                // Check for both input constness.
                let a_const = consts.get(a).is_some();
                let b_const = consts.get(b).is_some();

                // If both are constant we don't care about picking one.
                if a_const && b_const {
                    return None;
                }

                // Return substitution of non-const value with const value.

                if a_const {
                    return Some((*b, *a));
                } 

                if b_const {
                    return Some((*a, *b));
                }
            }
        }
    }

    None
}

pub struct PropagateBlockInvariantsPass;

impl super::Pass for PropagateBlockInvariantsPass {
    fn name(&self) -> &str {
        "block invariant propagation"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::propagate_block_invariants()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        let mut invariants: Map<Label, Map<Value, Value>> = Map::default();

        // Certain blocks have invariants and to be reached some condition must be true.
        // if (x == y) { label1 }
        // In this case in label1 it is known that x == y. If one of these is constant we will
        // optimize all accesses to non-constant value.
        
        let labels   = function.reachable_labels_bfs();
        let creators = function.value_creators_with_labels(&labels);
        let consts   = function.constant_values_with_labels(&labels);
        let incoming = function.flow_graph_incoming();

        for label in labels {
            // Entry label doesn't have any invariants so nothing can be optimized.
            if label == function.entry() {
                continue;
            }

            let predecessors                = &incoming[&label];
            let mut predecessors_invariants = Vec::with_capacity(predecessors.len());

            // Get invariants for every predecessor.
            for &predecessor in predecessors {
                // Get known invariants for this predecessor. If we don't know them just
                // create an empty invariant list.
                let mut invariants = invariants.get(&predecessor).cloned()
                    .unwrap_or_else(Map::default);

                // Get new invariant that we may know thanks to the conditional branch result.
                let invariant = get_invariant_value(function, predecessor, label,
                                                    &creators, &consts);

                if let Some((from, to)) = invariant {
                    // Try to add new invariant. If there is cyclic substiution
                    // (from, to) and (to, from) than remove it and don't continue further.
                    if invariants.remove(&to).is_none() {
                        if let Some(old_to) = invariants.get(&from) {
                            // If there is already invariant from `from` we will keep it only if
                            // `to` values match.
                            if *old_to != to {
                                invariants.remove(&from);
                            }
                        } else {
                            // We are free to insert this new invariant.
                            invariants.insert(from, to);
                        }
                    }
                }

                // Register invariants for this predecessor.
                predecessors_invariants.push(invariants);
            }

            let mut final_invariants = Map::default();

            // Merge all invariants from predecessors into one invariant list.
            for (&from, &to) in &predecessors_invariants[0] {
                let mut valid = true;

                // Make sure that this invariant is valid from every entrypoint.
                for other in &predecessors_invariants[1..] {
                    // If this block has conflicting invariant or not matching invariant
                    // than whole invariant is invalid.
                    if !(other.get(&to).is_none() && other.get(&from) == Some(&to)) {
                        valid = false;
                        break;
                    }
                }

                if valid {
                    final_invariants.insert(from, to);
                }
            }

            // Transform inputs in the block based on calculated invariants.
            for instruction in function.blocks.get_mut(&label).unwrap() {
                instruction.transform_inputs(|input| {
                    if let Some(to) = final_invariants.get(input) {
                        did_something = true;
                        *input        = *to;
                    }
                });
            }

            // Set computed invariants for this label.
            invariants.insert(label, final_invariants);
        }

        did_something
    }
}
