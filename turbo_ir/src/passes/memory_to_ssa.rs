use crate::{FunctionData, Instruction, Location, Label, Value, Map, FlowGraph};

pub struct MemoryToSsaPass;

fn rewrite_memory_to_ssa(function: &mut FunctionData, pointer: Value, start_label: Label,
                         flow_incoming: &FlowGraph, undef: Value) {
    let mut load_aliases = Vec::new();
    let mut dead_stores  = Vec::new();
    let mut phi_updates  = Vec::new();
    let mut block_values = Map::default();

    // Go through every reachable label from `start_label` (including itself).
    for label in function.traverse_bfs(start_label, true) {
        let body = &function.blocks[&label];

        // Try to get our inserted PHI output value. Maybe it will be used
        // as an initial value in the current block.
        let phi_value = match &body[0] {
            Instruction::Phi { dst, .. } => Some(*dst),
            _                            => None,
        };

        let mut used_phi = false;

        // Current value that is present in `pointer`.
        let mut value = None;

        // Go through every instruction to rewrite all load and stores related
        // to `stackalloc`.
        for (inst_id, instruction) in body.iter().enumerate() {
            let location = Location::new(label, inst_id);

            match instruction {
                Instruction::Load { dst, ptr } => {
                    if *ptr == pointer {
                        if value.is_none() && phi_value.is_some() {
                            // `pointer` wasn't written to in this block. We will need to
                            // take `value` from PHI instruction.
                            value    = phi_value;
                            used_phi = true;
                        }

                        // This load will use currently known value or undef.
                        load_aliases.push((location, *dst, value.unwrap_or(undef)));
                    }
                }
                Instruction::Store { ptr, value: stored_value } => {
                    if *ptr == pointer {
                        // This store can be removed and current value at `pointer` is
                        // now equal to `stored_value`.
                        value = Some(*stored_value);
                        dead_stores.push(location);
                    }
                }
                _ => {}
            }
        }

        // Make sure that PHI actually exists if we have used its value.
        assert!(!(phi_value.is_none() && used_phi), "Used value of non-existent PHI.");

        // If there is a PHI available and value wasn't used then assume that
        // we need this PHI instruction for the successors.
        if value.is_none() && phi_value.is_some() {
            value    = phi_value;
            used_phi = true;
        }

        // Insert value which is stored in `pointer` at the and of block `label`.
        if let Some(value) = value {
            assert!(block_values.insert(label, value).is_none(),
                    "Multple exit values for the same block.");
        }

        // If PHI was used then queue update of PHI incoming values.
        if used_phi {
            phi_updates.push((label, phi_value.unwrap()));
        }
    }

    // Go through all queued PHI updates and update their incoming values.
    for (label, phi_value) in phi_updates {
        let mut incoming = Vec::new();

        // Get incoming value for every predecessor.
        for &predecessor in &flow_incoming[&label] {
            let value = block_values.get(&predecessor).copied()
                .unwrap_or(undef);

            incoming.push((predecessor, value));
        }

        // Replace PHI with new incoming values.
        *function.instruction_mut(Location::new(label, 0)) = Instruction::Phi {
            dst: phi_value,
            incoming,
        };
    }

    // Remove all stores to `stackalloc` output pointer.
    for location in dead_stores {
        *function.instruction_mut(location) = Instruction::Nop;
    }

    // Alias all `stackalloc` pointer loads to calculated value.
    for (location, dst, value) in load_aliases {
        *function.instruction_mut(location) = Instruction::Alias {
            dst,
            value,
        };
    }
}

impl super::Pass for MemoryToSsaPass {
    fn name(&self) -> &str {
        "memory to SSA"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        // Rewrite stackallocs to use SSA values.
        // entry:
        //   v1 = stackalloc u32 1
        //   bcond u1 v0, block_0, block_1
        // 
        // block_0:
        //   v2 = u32 1
        //   store u32* v1, u32 v2
        //   branch exit
        //
        // block_1:
        //   v3 = u32 3
        //   store u32* v1, u32 v3
        //   branch exit
        //
        // exit:
        //   v4 = load u32* v1
        //   ret u32 v4
        //
        // Will get rewritten to:
        // entry:
        //   bcond u1 v0, block_0, block_1
        //
        // block_0:
        //   v2 = u32 1
        //   branch exit
        //
        // block_1:
        //   v3 = u32 3
        //   branch exit
        //
        // exit:
        //   v4 = phi u32 [block_0: v2, block_1: v3]
        //   ret u32 v4

        let labels        = function.reachable_labels();
        let flow_incoming = function.flow_graph_incoming();

        'main_loop: loop {
            // Go through every `stackalloc` and try to find candidate to rewrite
            // it to use SSA values.
            'skip: for (pointer, location) in function.find_stackallocs(Some(1)) {
                // Make sure that this is actually stackallocs (locations may have shifted).
                assert!(matches!(function.instruction(location),
                                 Instruction::StackAlloc { .. }));

                // We can only rewrite `stackallocs` which are just loaded and stored to.
                let uses = function.find_uses(pointer);
                if  uses.is_empty() {
                    continue;
                }

                for location in uses {
                    match function.instruction(location) {
                        Instruction::Store { ptr, value } => {
                            // Make sure that we are actually storing TO `pointer`, not
                            // storing `pointer`.
                            if *ptr != pointer || *value == pointer {
                                continue 'skip;
                            }
                        }
                        Instruction::Load { .. } => {}
                        _                        => continue 'skip,
                    }
                }

                // Remove `stackalloc` instruction.
                *function.instruction_mut(location) = Instruction::Nop;

                // Get type of value which we are rewriting.
                let ty = function.value_type(pointer).strip_ptr().unwrap();

                // Write empty PHI instruction at the beginning of every block except entry one.
                for &label in &labels {
                    // We cannot put PHI instructions in the entry block.
                    if label == Label(0) {
                        continue;
                    }

                    // Allocate PHI output value with proper type.
                    let output = function.allocate_typed_value(ty);

                    // Insert new empty PHI instruction at the beginning of the block.
                    function.blocks.get_mut(&label).unwrap().insert(0, Instruction::Phi {
                        dst:      output,
                        incoming: Vec::new(),
                    });
                }

                // Because we have inserted PHIs, `location.index()`, won't be correct anymore.
                // But label will be still right.
                let stackalloc_label = location.label();
                let undef            = function.undefined_value(ty);

                // Perform the rewrite.
                rewrite_memory_to_ssa(function, pointer, stackalloc_label, &flow_incoming, undef);

                // We are done, clean up all the mess that we have done.
                for &label in &labels {
                    // We cannot put PHI instructions in entry block.
                    if label == Label(0) {
                        continue;
                    }

                    let body = function.blocks.get_mut(&label).unwrap();

                    // Get the first instruction which must be our inserted PHI.
                    if let Instruction::Phi { incoming, .. } = &body[0] {
                        // If this PHI isn't used then just remove it.
                        if incoming.is_empty() {
                            body.remove(0);
                        }
                    } else {
                        panic!("First instruction must be our inserted PHI.");
                    }
                }

                did_something = true;

                // Reenter loop because we have modified stackalloc locations.
                continue 'main_loop;
            }

            // Nothing is left to be done.
            break 'main_loop;
        }

        did_something
    }
}
