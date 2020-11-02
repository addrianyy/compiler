use crate::{FunctionData, Instruction, Location, Label, Value, Map, FlowGraph};

pub struct MemoryToSsaPass;

type LoadAliases = Vec<(Location, Value, Value)>;
type DeadStores  = Vec<Location>;

impl MemoryToSsaPass {
    fn rewrite_memory_to_ssa(
        &self,
        function:         &mut FunctionData,
        pointer:          Value,
        stackalloc_label: Label,
        flow_incoming:    &FlowGraph,
    ) -> Option<(LoadAliases, DeadStores)> 
    {
        let mut load_aliases = Vec::new();
        let mut dead_stores  = Vec::new();
        let mut block_values = Map::default();

        let mut phi_updates = Vec::new();

        // Go through every reachable label from `stackalloc_label` (including itself).
        for label in function.traverse_bfs(stackalloc_label, true) {
            let body = &function.blocks[&label];

            // Try to get our inserted PHI output value. Maybe it will be used
            // as an initial value in the current block.
            let phi_value = if let Instruction::Phi { dst, .. } = &body[0] {
                Some(*dst)
            } else {
                None
            };

            let mut used_phi = false;

            // Current value that is present in `pointer`.
            let mut value = None;

            // Go through every instruction to rewrite all load and stores related
            // to `stackallocs`.
            for (inst_id, instruction) in body.iter().enumerate() {
                let location = Location::new(label, inst_id);

                match instruction {
                    Instruction::Load { dst, ptr } => {
                        if *ptr == pointer {
                            if value.is_none() {
                                // `pointer` wasn't written to in this block. We will need to
                                // take `value` from PHI instruction.
                                value    = Some(phi_value.unwrap());
                                used_phi = true;
                            }

                            // This load will use currently known value.
                            load_aliases.push((location, *dst, value.unwrap()));
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

            let beginning = label == stackalloc_label;

            // Make sure that if this is our first label PHI instruction wasn't used.
            assert!(!(used_phi && beginning));

            // If we are not at the beginning and value wasn't used than assume that
            // we need PHI instruction for the successors.
            // TODO: Add it to some list and verify if we actually need this PHI.
            if !beginning && value.is_none() {
                value    = Some(phi_value.unwrap());
                used_phi = true;
            }

            // Insert value which `pointer` is equal to at the and of block `label`.
            if let Some(value) = value {
                assert!(block_values.insert(label, value).is_none());
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
                let value = block_values[&predecessor];

                incoming.push((predecessor, value));
            }

            // Replace PHI with new incoming values.
            *function.instruction_mut(Location::new(label, 0)) = Instruction::Phi {
                dst: phi_value,
                incoming,
            };
        }

        Some((load_aliases, dead_stores))
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

        // Go through every `stackalloc` and try to rewrite it to use SSA values.
        'skip: for (pointer, location) in function.find_stackallocs(Some(1)) {
            // We can only rewrite `stackallocs` which are just loaded and stored to.
            let uses = function.find_uses(pointer);
            if  uses.is_empty() {
                continue;
            }

            for location in uses {
                match function.instruction(location) {
                    Instruction::Store { ptr, value } => {
                        // Make sure that we are actually storing TO `value`, not
                        // storing `value`.
                        if *ptr != pointer || *value == pointer {
                            continue 'skip;
                        }
                    }
                    Instruction::Load { .. } => {}
                    _                        => continue 'skip,
                }
            }

            // Write empty PHI instruction at the beginning of every block except entry one.
            for &label in &labels {
                // We cannot put PHI instructions in the entry block.
                if label == Label(0) {
                    continue;
                }

                // Allocate PHI output value and get its type.
                let output = function.allocate_value();
                let ty     = function.value_type(pointer).strip_ptr().unwrap();

                // Because we have allocated a new value we need to set its type.
                if let Some(type_info) = function.type_info.as_mut() {
                    assert!(type_info.insert(output, ty).is_none(),
                            "Newly created value already had type info.");
                }

                // Insert new empty PHI instruction to the beginning of the block.
                function.blocks.get_mut(&label).unwrap().insert(0, Instruction::Phi {
                    dst:      output,
                    incoming: Vec::new(),
                });
            }

            // Because we have inserted PHIs location.index() won't be correct anymore. But
            // label will be still right.
            let stackalloc_label = location.label();

            // Try to rewrite `stackalloc`.
            let result = self.rewrite_memory_to_ssa(function, pointer, stackalloc_label,
                                                    &flow_incoming);
            let success = result.is_some();

            if let Some((load_aliases, dead_stores)) = result {
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

                did_something = true;
            }

            // We are done, clean up all the mess that we have done.
            for &label in &labels {
                // We cannot put PHI instructions in entry block.
                if label == Label(0) {
                    continue;
                }

                // Get the first instruction which must be our inserted PHI.
                let instruction = function.instruction_mut(Location::new(label, 0));

                if let Instruction::Phi { incoming, .. } = instruction {
                    // If this PHI isn't used or we failed rewriting then just remove it.
                    if incoming.is_empty() || !success {
                        *instruction = Instruction::Nop;
                    }
                } else {
                    panic!("First instruction must be our inserted PHI.");
                }
            }
        }

        did_something
    }
}
