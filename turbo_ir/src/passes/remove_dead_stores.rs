use crate::{FunctionData, Instruction, Map, analysis::KillTarget};

pub struct RemoveDeadStoresPass;

impl super::Pass for RemoveDeadStoresPass {
    fn name(&self) -> &str {
        "dead store elimination"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let dominators       = function.dominators();
        let pointer_analysis = function.analyse_pointers();
        let phi_used         = function.phi_used_values();

        let mut stores        = Map::default();
        let mut did_something = false;

        // If there are two stores to the same pointer and nothing inbetween them
        // can observe pointer value then the first store can be removed.
        //
        // store %4, %5
        // store %4, %6
        //
        // Will get optimized to:
        // store %4, %6

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

                        // If both locations are in different blocks and value
                        // is used in PHI then `validate_path_memory` cannot reason about
                        // it.  TODO: Fix this.
                        if to_remove.label() != other_location.label() &&
                            phi_used.contains(&pointer) {
                            continue;
                        }

                        let start = to_remove;
                        let end   = other_location;

                        // Path will go from `removed_location` to `other_location`. Make
                        // sure that there is nothing inbetween that can load our pointer.
                        // If there is something, we can't eliminate the store.
                        let result = function.validate_path_memory(&dominators, start, end,
                                                                   KillTarget::Start,
                                                                   |instruction| {
                            match instruction {
                                Instruction::Load { ptr, .. } => {
                                    // If pointers alias than this load can see ths pointer
                                    // value and we cannot eliminate the store.

                                    !pointer_analysis.can_alias(pointer, *ptr)
                                }
                                Instruction::Call { .. } => {
                                    // If a function can access the pointer than it can
                                    // see its value and we cannot eliminate the store.

                                    !function.can_call_access_pointer(&pointer_analysis,
                                                                      instruction,
                                                                      pointer)
                                }
                                _ => true,
                            }
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

        // If there are pointers which are only written to once and never accessed and they come
        // from safely used stackallocks, single write can be removed.

        let usage_counts = function.usage_counts();

        for (pointer, stores) in stores {
            // Check if the only instruction that touches pointer is a store.
            let single_store = stores.len() == 1 && usage_counts[pointer.index()] == 1;

            // Check if single-store pointer comes from safely used safalloc.
            if single_store && pointer_analysis.get_stackalloc(pointer) == Some(true) {
                // Remove unneeded store.
                *function.instruction_mut(stores[0]) = Instruction::Nop;
            }
        }

        did_something
    }
}
