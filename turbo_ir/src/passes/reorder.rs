use super::{FunctionData, Instruction, Pass};
use super::super::Location;

pub struct ReorderPass;

impl Pass for ReorderPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let creators          = function.value_creators();
        let dominators        = function.dominators();

        // Reorder instructions so they are executed just before first 
        // instruction that needs them. This reduces register pressure and makes
        // IR easier to follow. Deduplication pass may create values which
        // are far away from first use.
        // Limitation is that we can reorder things to a different block then current one.
        // This is because of a few reasons:
        // 1. It doesn't collide x86 reorder pass.
        // 2. It avoids infinite loops.
        //    %10 = add %0, %1
        //    %11 = add %2, %3
        //    %12 = add %10, %11
        //    In this case %10 and %11 will be swapped each pass and optimization will never
        //    finish.

        for (value, creator) in creators {
            let body            = &function.blocks[&creator.0];
            let mut new_creator = None;

            // It is very likely that creator location is now incorrect.
            // The label is always correct, so just search for what instruction created 
            // this particular value in specified block.
            for (inst_id, instruction) in body.iter().enumerate() {
                if let Some(created_value) = instruction.created_value() {
                    if value == created_value {
                        new_creator = Some(Location(creator.0, inst_id));

                        break;
                    }
                }
            }

            // We must be able to get creator position.
            let creator = new_creator.expect("Something is broken.");

            // Loads and volatile instructions cannot be reordered.
            if !body[creator.1].can_be_reordered() {
                continue;
            }

            let uses              = function.find_uses(value);
            let mut best_location = None;
            let mut best_count    = None;

            // Go through all uses and find the best location to reorder creator.
            'next_location: for &location in &uses {
                // We don't bother reordering within the same block. Also it can cause infinite
                // optimization loops so we better avoid it. If creator is in the same
                // block as one use ordering isn't that bad. Don't touch it.
                if location.0 == creator.0 {
                    best_location = None;

                    break;
                }

                let mut instruction_count = 0;

                // Make sure that we actually can reorder creator and retain SSA properties.
                // Basically check that new creator location dominates all other uses.
                // Also count number of instructions.
                for &other_location in &uses {
                    // We don't dominate ourselves.
                    if location == other_location {
                        continue;
                    }

                    // Make sure that with reordered creator this use will be still valid.
                    // Also count number of instructions. 
                    // Because we sum them up, it's not a perfect measure.
                    // TODO: Find better way of determining the best reorder.
                    let result = function.validate_path_ex(&dominators, location,
                                                           other_location, |_| true);

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
                // Check if the location isn't the same as current one.
                if Location(creator.0, creator.1 + 1) == best_location {
                    continue;
                }

                // Remove creator instruction.
                let creator = std::mem::replace(&mut function.blocks
                                                .get_mut(&creator.0)
                                                .unwrap()[creator.1],
                                                Instruction::Nop);

                // Place creator instruction in the new location.
                function.blocks.get_mut(&best_location.0)
                    .unwrap()
                    .insert(best_location.1, creator);

                did_something = true;
            }
        }

        did_something
    }
}
