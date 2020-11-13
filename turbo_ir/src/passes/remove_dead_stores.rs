use crate::{FunctionData, Instruction, Map, Location, analysis::KillTarget};

fn remove_dead_stores_precise(function: &mut FunctionData) -> bool {
    let dominators       = function.dominators();
    let pointer_analysis = function.analyse_pointers();
    let phi_used         = function.phi_used_values();

    let mut stores        = Map::default();
    let mut did_something = false;

    // Create a database of all stores in the function.
    function.for_each_instruction(|location, instruction| {
        if let Instruction::Store { ptr, .. } = instruction {
            // Add store instance for this pointer.
            stores.entry(*ptr)
                .or_insert_with(Vec::new)
                .push(location);
        }
    });

    for (&pointer, stores) in &mut stores {
        // Keep removing until there is nothing more to remove.
        'next: loop {
            // If there is only one store we need to stop removing. If we won't code
            // below will delete a single store to the pointer.
            if stores.len() <= 1 {
                break;
            }

            // Go through all stores and find which one can be removed.
            for &to_remove in stores.iter() {
                // Find complementary store.
                for &other_location in stores.iter() {
                    // We don't care about ourselves.
                    if to_remove == other_location {
                        continue;
                    }

                    let start = to_remove;
                    let end   = other_location;

                    // If both locations are in different blocks and value
                    // is used in PHI then `validate_path_memory` cannot reason about
                    // it. TODO: Fix this.
                    if start.label() != end.label() && phi_used.contains(&pointer) {
                        continue;
                    }

                    // Path will go from `to_remove` to `other_location`. Make
                    // sure that there is nothing inbetween that can load our pointer.
                    // If there is something, we can't eliminate the store.
                    let result = function.validate_path_memory(&dominators, start, end,
                                                               KillTarget::Start,
                                                               |instruction| {
                        !function.can_load_pointer(instruction, &pointer_analysis, pointer)
                    });

                    if result.is_some() {
                        // We have found a store to remove. Replace it with a nop.
                        *function.instruction_mut(to_remove) = Instruction::Nop;

                        // Delete removed store from a list of stores to check.
                        let index = stores.iter().position(|x| *x == to_remove).unwrap();
                        stores.remove(index);

                        did_something = true;

                        // Maybe there is another store to remove. Continue looping.
                        continue 'next;
                    }
                }
            }

            // We haven't found any store to remove. Exit the loop.
            break;
        }
    }

    did_something
}

fn remove_dead_stores_fast(function: &mut FunctionData) -> bool {
    let pointer_analysis = function.analyse_pointers();

    let mut stores        = Map::default();
    let mut did_something = false;

    for label in function.reachable_labels() {
        stores.clear();

        let mut body = &function.blocks[&label];
        let body_len = body.len();

        'next_instruction: for inst_id in 0..body_len {
            let instruction = &body[inst_id];

            if let Instruction::Store { ptr, .. } = instruction {
                if let Some(prev_store_id) = stores.get(ptr).copied() {
                    // Update latest store.
                    stores.insert(*ptr, inst_id);

                    // Make sure that nothing inbetween can load `ptr`.
                    for instruction in &body[prev_store_id + 1..inst_id] {
                        if function.can_load_pointer(instruction, &pointer_analysis, *ptr) {
                            continue 'next_instruction;
                        }
                    }

                    // Remove `prev_store` as it is dead.

                    let location = Location::new(label, prev_store_id);

                    *function.instruction_mut(location) = Instruction::Nop;

                    body          = &function.blocks[&label];
                    did_something = true;
                } else {
                    stores.insert(*ptr, inst_id);
                }
            }
        }
    }

    did_something
}

// If there are two stores to the same pointer and nothing inbetween them
// can observe pointer value then the first store can be removed.
//
// store v4, v5
// store v4, v6
//
// Will get optimized to:
// store v4, v6

pub struct RemoveDeadStoresFastPass;

impl super::Pass for RemoveDeadStoresFastPass {
    fn name(&self) -> &str {
        "fast dead store elimination"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        remove_dead_stores_fast(function)
    }
}

pub struct RemoveDeadStoresPrecisePass;

impl super::Pass for RemoveDeadStoresPrecisePass {
    fn name(&self) -> &str {
        "precise dead store elimination"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        remove_dead_stores_precise(function)
    }
}
