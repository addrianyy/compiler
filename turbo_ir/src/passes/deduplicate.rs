use crate::{FunctionData, Instruction, Location, LargeKeyMap};

pub struct DeduplicatePass;

impl super::Pass for DeduplicatePass {
    fn name(&self) -> &str {
        "deduplication"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let pointer_analysis  = function.analyse_pointers();

        // Find two or more non-volatile instructions with the same operands and try to 
        // reuse their output values.
        //
        // %5 = add u32 %1, %2
        // %6 = add u32 %1, %2
        // %7 = neg u32 %6
        //
        // Will get optimized to:
        // %5 = add u32 %1, %2
        // %7 = neg %5

        let mut dedup_list: LargeKeyMap<_, Vec<Location>> = LargeKeyMap::default();

        // Create a list of all deduplication candidates for a given instruction key.
        function.for_each_instruction(|location, instruction| {
            // Skip instructions which cannot be deduplicated.
            match instruction {
                Instruction::Nop               => return,
                Instruction::Alias      { .. } => return,
                Instruction::Phi        { .. } => return,
                Instruction::StackAlloc { .. } => return,
                x if x.is_volatile()           => return,
                _                              => {}
            }

            // Create a unique key that will describe instruction type and its input operands.
            let key = (std::mem::discriminant(instruction), instruction.input_parameters());

            // Get deduplication candidates for this instruction key.
            let candidates = dedup_list.entry(key)
                .or_insert_with(Vec::new);

            // Add current instruction as a candidate.
            candidates.push(location);
        });

        let dominators = function.dominators();
        let phi_used   = function.phi_used_values();

        for label in function.reachable_labels() {
            let mut body = &function.blocks[&label];
            let body_len = body.len();

            for inst_id in 0..body_len {
                let instruction = &body[inst_id];

                // Create a unique key that will describe instruction type and input operands.
                let key = (std::mem::discriminant(instruction), instruction.input_parameters());

                let mut deduplication = None;
                let mut best_icount   = None;

                // Get candidates for deduplication. If this instruction
                // cannot be deduplicated it will always return None.
                if let Some(candidates) = dedup_list.get(&key) {
                    // Find the best candidate for deduplication.
                    'skip: for &candidate in candidates {
                        let location = Location::new(label, inst_id);

                        let result = if let Instruction::Load { ptr, .. } = instruction {
                            let load_ptr = *ptr;

                            // If both locations are in different blocks and value
                            // is used in PHI then `validate_path_memory` cannot reason about
                            // it.  TODO: Fix this.
                            if candidate.label() != location.label() &&
                                phi_used.contains(&load_ptr) {
                                continue 'skip;
                            }

                            function.validate_path_memory(&dominators, candidate, location, 
                                                          |instruction| {
                                // Special care needs to be taken if we want to deduplicate
                                // load. Something inbetween two instructions may have
                                // modified loaded ptr and output value will be different.

                                match instruction {
                                    Instruction::Call  { .. } => {
                                        // If call can affect this pointer we cannot
                                        // continue further.

                                        !function.can_call_access_pointer(&pointer_analysis,
                                                                          instruction,
                                                                          load_ptr)
                                    }
                                    Instruction::Store { ptr, .. } => {
                                        // Make sure that stored pointer can't
                                        // alias a pointer loaded by candidate to
                                        // deduplicate.

                                        !pointer_analysis.can_alias(load_ptr, *ptr)
                                    }
                                    _ => true,
                                }
                            })
                        } else {
                            function.validate_path_count(&dominators, candidate, location)
                        };

                        if let Some(instruction_count) = result {
                            // If it's a valid candidate, check if it's closer then the
                            // best one. If it is then set it as current best.
                            let better = match best_icount {
                                Some(icount) => instruction_count < icount,
                                None         => true,
                            };

                            if better {
                                deduplication = Some(candidate);
                                best_icount   = Some(instruction_count);
                            }
                        }
                    }
                }

                if let Some(deduplication) = deduplication {
                    // We have found a valid candidate for deduplication.

                    // All values which can be deduplicated must create values.
                    let output = body[inst_id].created_value().unwrap();
                    let alias  = function.blocks[&deduplication.label()][deduplication.index()]
                        .created_value().unwrap();

                    // Get mutable reference to function body.
                    let mut_body = function.blocks.get_mut(&label).unwrap();

                    // Alias output value of current instruction to output value
                    // of deduplication candidate.
                    mut_body[inst_id] = Instruction::Alias {
                        dst:   output,
                        value: alias,
                    };

                    body          = &function.blocks[&label];
                    did_something = true;
                }
            }
        }

        did_something
    }
}
