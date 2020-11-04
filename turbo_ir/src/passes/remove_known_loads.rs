use crate::{FunctionData, Instruction, Map};

pub struct RemoveKnownLoadsPass;

impl super::Pass for RemoveKnownLoadsPass {
    fn name(&self) -> &str {
        "known load elimination"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let pointer_analysis = function.analyse_pointers();
        let dominators       = function.dominators();
        let phi_used         = function.phi_used_values();

        // If a pointer is stored to and loaded afterwards, we will try to avoid
        // load and just return value recently stored. We need to make sure that
        // inbetween store and load there are no instructions that could affect loaded value.
        // 
        // store %1, %0
        // %2 = load %1
        // %3 = neg %2
        //
        // Will get optimized to:
        // store %1, %0
        // %3 = neg %0

        let mut loads  = Vec::new();
        let mut stores = Map::default();

        // Create a database of all loads and stores in the function.
        function.for_each_instruction(|location, instruction| {
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
                let mut best_replacement = None;
                let mut best_icount      = None;

                // Go through all stores to find the best store to source load from.
                for &(store_location, store_value) in stores {
                    let start = store_location;
                    let end   = load_location;

                    // If both locations are in different blocks and value
                    // is used in PHI then `validate_path_memory` cannot reason about
                    // it.  TODO: Fix this.
                    if load_location.label() != store_location.label() &&
                        phi_used.contains(&load_ptr) {
                        continue;
                    }

                    // Check if we actually can source load from this store.
                    let result = function.validate_path_memory(&dominators, start, end,
                                                               |instruction| {
                        match instruction {
                            Instruction::Call { .. } => {
                                // If call can affect this pointer we cannot continue further.

                                !function.can_call_access_pointer(&pointer_analysis,
                                                                  instruction, load_ptr)
                            }
                            Instruction::Store { ptr, .. } => {
                                // If pointers alias then something can possibly affect loaded
                                // pointer. We can't source load from this store.

                                !pointer_analysis.can_alias(load_ptr, *ptr)
                            }
                            _ => true,
                        }
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
}
