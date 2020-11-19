use crate::{FunctionData, Instruction, Location, ValidationCache};

pub struct ReorderPass;

impl super::Pass for ReorderPass {
    fn name(&self) -> &str {
        "reordering"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::reorder()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let mut vcache        = ValidationCache::default();
        let dominators        = function.dominators();

        // Reorder instructions so they are executed just before first
        // instruction that needs them. This reduces register pressure and makes
        // IR easier to follow. Deduplication pass may create values which
        // are far away from first use.
        // Limitation is that we can reorder things to a different block then current one.
        // This is because of a few reasons:
        // 1. It doesn't collide with x86 reorder pass.
        // 2. It avoids infinite loops.
        //    v10 = add v0, v1
        //    v11 = add v2, v3
        //    v12 = add v10, v11
        //    In this case v10 and v11 will be swapped each pass and optimization will never
        //    finish.

        for label in function.reachable_labels() {
            let size = function.blocks[&label].len();

            for inst_id in 0..size {
                let instruction = &function.blocks[&label][inst_id];

                // Loads, PHIs and volatile instructions cannot be reordered.
                if !instruction.can_be_reordered() {
                    continue;
                }

                if let Some(value) = instruction.created_value() {
                    let creator = Location::new(label, inst_id);

                    let uses              = function.find_uses(value);
                    let mut best_location = None;
                    let mut best_count    = None;

                    // Go through all uses to find the best location to reorder creator.
                    'next_location: for &location in &uses {
                        // We don't bother reordering within the same block.
                        // It can cause infinite optimization loops so we better avoid it.
                        // If creator is in the same block as one use ordering isn't that bad.
                        // Don't touch it.
                        if location.label() == creator.label() {
                            best_location = None;
                            break;
                        }

                        // Don't reorder anything that is used as incoming value in PHI.
                        if function.instruction(location).is_phi() {
                            best_location = None;
                            break;
                        }

                        let mut instruction_count = 0;

                        // Make sure that we actually can reorder creator and retain
                        // SSA properties. Basically check that new creator location dominates
                        // all other uses. Also count number of instructions.
                        for &other_location in &uses {
                            // We don't care about ourselves.
                            if location == other_location {
                                continue;
                            }

                            // Make sure that with reordered creator this use will be still valid.
                            // Also count number of instructions.
                            // Because we sum them up, it's not a perfect measure.
                            // TODO: Find better way of determining the best reorder.
                            let result = function.validate_path_count(&dominators, location,
                                                                      other_location, &mut vcache);

                            if let Some(count) = result {
                                instruction_count += count;
                            } else {
                                continue 'next_location;
                            }
                        }

                        // It's a valid candidate, check if it's better than current best.
                        let better = match best_count {
                            Some(best_count) => instruction_count < best_count,
                            None             => true,
                        };

                        if better {
                            best_location = Some(location);
                            best_count    = Some(instruction_count);
                        }
                    }

                    if let Some(best_location) = best_location {
                        // We have found the best location to reorder instruction.

                        assert_ne!(creator.label(), best_location.label(),
                                   "It's illegal to reorder within the same block.");

                        // Remove creator instruction.
                        let creator = std::mem::replace(&mut function.blocks
                                                        .get_mut(&creator.label())
                                                        .unwrap()[creator.index()],
                                                        Instruction::Nop);

                        // Place creator instruction in the new location.
                        function.blocks.get_mut(&best_location.label())
                            .unwrap()
                            .insert(best_location.index(), creator);

                        did_something = true;
                    }
                }
            }
        }

        did_something
    }
}
