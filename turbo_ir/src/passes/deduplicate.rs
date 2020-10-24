use std::collections::{HashMap, HashSet};

use super::{FunctionData, Instruction, Pass};
use super::super::{Value, Location};

struct LoadInfo {
    loaded_ptr:  Value,
    is_safe_ptr: bool,
}

pub struct DeduplicatePass;

impl Pass for DeduplicatePass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let mut safe_ptrs     = HashSet::new();

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

        // Create a list of safe pointers. Safe pointers are known to not alias other pointers.
        // Safe pointers are ones coming from stackallocs which are used only by load and
        // store instructions.
        'skip: for (value, _) in function.find_stackallocs(None) {
            for location in function.find_uses(value) {
                match function.instruction(location) {
                    Instruction::Store { ptr, value: stored_value } => {
                        // Make sure that we are actually storing TO the pointer, not
                        // storing the pointer.
                        if *ptr != value || *stored_value == value {
                            continue 'skip;
                        }
                    }
                    Instruction::Load { .. } => {},
                    _                        => continue 'skip,
                }
            }

            safe_ptrs.insert(value);
        }

        let mut dedup_list: HashMap<_, Vec<Location>> = HashMap::new();

        // Create a list of all deduplication candidates for a given instruction key.
        function.for_each_instruction(|location, instruction| {
            // Skip instructions which cannot be deduplicated.
            match instruction {
                Instruction::Nop          => return,
                Instruction::Alias { .. } => return,
                x if x.is_volatile()      => return,
                _                         => {}
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
                    for &candidate in candidates {
                        let location = Location(label, inst_id);

                        // Deduplicating loads is a special case. Get information about the load.
                        let load_info = match instruction {
                            Instruction::Load { ptr, .. } => {
                                Some(LoadInfo {
                                    loaded_ptr: *ptr,
                                    is_safe_ptr: safe_ptrs.contains(ptr),
                                })
                            }
                            _ => None,
                        };

                        let mut instruction_count = 0;

                        // Check if the path from candidate location to current location is
                        // valid. This will also count all hit instructions.
                        let valid = function.validate_path_ex(&dominators, candidate, location,
                            |instruction| {
                                // Count instructions hit when validating path. This will be
                                // used to determine which deduplication candidate is the best.
                                instruction_count += 1;

                                if let Some(load_info) = &load_info {
                                    // Special care needs to be taken if we want to deduplicate
                                    // load. Something inbetween two instructions may have
                                    // modified loaded ptr and output value will be different.

                                    match instruction {
                                        Instruction::Call  { .. } => {
                                            // It's hard to reason about calls so
                                            // they are always deduplication barrier for loads.

                                            false
                                        }
                                        Instruction::Store { ptr, .. } => {
                                            // Make sure that this store didn't actually affect
                                            // pointer loaded by candidate to deduplicate.
                                            if *ptr == load_info.loaded_ptr {
                                                return false;
                                            }

                                            // This isn't a safe pointer and we don't know
                                            // if two pointer don't alias.
                                            // We cannot deduplicate it.
                                            // TODO: Use more sophisticated pointer origin
                                            // analysis to make sure they don't alias.
                                            if !load_info.is_safe_ptr {
                                                return false;
                                            }

                                            // Stored pointer for sure doesn't
                                            // alias loaded pointer.
                                            true
                                        }
                                        _ => true,
                                    }
                                } else {
                                    // Instruction is always valid if deduplicated instruction
                                    // isn't a load.
                                    true
                                }
                            }
                        );

                        if valid {
                            // If it's a valid candidate, check if it's closer then the
                            // best one. If it is then set it as current best.
                            let better = match best_icount {
                                Some(icount) => instruction_count < icount,
                                None         => true
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
                    let alias  = function.blocks[&deduplication.0][deduplication.1]
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
