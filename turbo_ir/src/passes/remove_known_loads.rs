use crate::{FunctionData, Instruction, Map, Location, ValidationCache, analysis::KillTarget};

fn remove_known_loads_precise(function: &mut FunctionData) -> bool {
    let pointer_analysis = function.analyse_pointers();
    let dominators       = function.dominators();
    let labels           = function.reachable_labels();

    let mut vcache = ValidationCache::default();
    let mut loads  = Vec::new();
    let mut stores = Map::default();

    // Create a database of all loads and stores in the function.
    function.for_each_instruction_with_labels(&labels, |location, instruction| {
        match instruction {
            Instruction::Load { dst, ptr } => {
                // Add load to a linear list of loads which we will try to optimize.
                loads.push((location, *dst, *ptr));
            }
            Instruction::Store { ptr, value } => {
                // Add store instance for this pointer.
                stores.entry(*ptr)
                    .or_insert_with(Vec::new)
                    .push((location, *value));
            }
            _ => {}
        }
    });

    let mut did_something = false;

    // Go through all loads which we will try to optimize.
    for (load_location, load_dst, load_ptr) in loads {
        // Get all stores to a given pointer.
        if let Some(stores) = stores.get(&load_ptr) {
            // Recalculate `phi_used` here because added aliases may have changed it.
            // We may have sourced loaded pointer from store.
            let phi_used = function.phi_used_values(&labels);

            let mut best_replacement = None;
            let mut best_icount      = None;

            // Go through all stores to find the best store to source load from.
            for &(store_location, store_value) in stores {
                let start = store_location;
                let end   = load_location;

                // If both locations are in different blocks and value
                // is used in PHI then `validate_path_memory` cannot reason about
                // it. TODO: Fix this.
                if start.label() != end.label() && phi_used.contains(load_ptr) {
                    continue;
                }

                // Check if we actually can source load from this store.
                let result = function.validate_path_memory(&dominators, start, end,
                                                           KillTarget::End, &mut vcache,
                                                           |instruction| {
                    !function.can_store_pointer(instruction, &pointer_analysis, load_ptr)
                });

                if let Some(instruction_count) = result {
                    // If it's a valid candidate, check if it's closer then the
                    // best one. If it is then set it as current best.
                    let better = match best_icount {
                        Some(icount) => instruction_count < icount,
                        None         => true,
                    };

                    if better {
                        best_replacement = Some(store_value);
                        best_icount      = Some(instruction_count);
                    }
                }
            }

            if let Some(best_replacement) = best_replacement {
                // We have a valid candidate to source load from.
                // Perform the replacement.
                *function.instruction_mut(load_location) = Instruction::Alias {
                    dst:   load_dst,
                    value: best_replacement,
                };

                did_something = true;
            }
        }
    }

    did_something
}

fn remove_known_loads_fast(function: &mut FunctionData) -> bool {
    let pointer_analysis = function.analyse_pointers();

    let mut stores        = Map::default();
    let mut did_something = false;

    for label in function.reachable_labels() {
        stores.clear();

        let mut body = &function.blocks[&label];
        let body_len = body.len();

        'next_instruction: for inst_id in 0..body_len {
            let instruction = &body[inst_id];

            match instruction {
                Instruction::Store { ptr, value } => {
                    // `ptr` newest known value is now `value`.
                    stores.insert(*ptr, (inst_id, *value));
                }
                Instruction::Load { dst, ptr } => {
                    if let Some((store_id, store_value)) = stores.get(ptr).copied() {
                        // Make sure that nothing inbetween can modify `ptr`.
                        for instruction in &body[store_id + 1..inst_id] {
                            if function.can_store_pointer(instruction, &pointer_analysis, *ptr) {
                                continue 'next_instruction;
                            }
                        }

                        // Replace `load` with `alias` to the latest stored value.

                        let location = Location::new(label, inst_id);
                        let dst      = *dst;

                        *function.instruction_mut(location) = Instruction::Alias {
                            dst,
                            value: store_value,
                        };

                        body          = &function.blocks[&label];
                        did_something = true;
                    }
                }
                _ => {}
            }
        }
    }

    did_something
}

// If a pointer is stored to and loaded afterwards, we will try to avoid
// load and just return value recently stored. We need to make sure that
// inbetween store and load there are no instructions that could affect loaded value.
//
// store v1, v0
// v2 = load v1
// v3 = neg v2
//
// Will get optimized to:
// store v1, v0
// v3 = neg v0

pub struct RemoveKnownLoadsFastPass;

impl super::Pass for RemoveKnownLoadsFastPass {
    fn name(&self) -> &str {
        "fast known load elimination"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        remove_known_loads_fast(function)
    }
}

pub struct RemoveKnownLoadsPrecisePass;

impl super::Pass for RemoveKnownLoadsPrecisePass {
    fn name(&self) -> &str {
        "precise known load elimination"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        remove_known_loads_precise(function)
    }
}
