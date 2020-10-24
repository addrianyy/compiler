use std::collections::{HashMap, HashSet};

use super::{FunctionData, Instruction, Pass};

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

        for label in function.reachable_labels() {
            // TODO: Currently deduplication works on blocks. Make it work on whole 
            // function.

            let mut dedup_list: HashMap<_, usize> = HashMap::new();
            let body = function.blocks.get_mut(&label).unwrap();

            'skip_dedup: for inst_id in 0..body.len() {
                let inst = &body[inst_id];

                // Skip instructions which cannot be deduplicated.
                match inst {
                    Instruction::Nop          => continue,
                    Instruction::Alias { .. } => continue,
                    x if x.is_volatile()      => continue,
                    _                         => {}
                }

                // Create a unique key that will describe instruction type and input operands.
                let key = (std::mem::discriminant(inst), inst.input_parameters());

                // Get a candidate for deduplication.
                if let Some(&prev_index) = dedup_list.get(&key) {
                    if let Instruction::Load { ptr, .. } = inst {
                        // Special care needs to be taken if we want to deduplicate load.
                        // Something inbetween two instructions may have modified loaded ptr
                        // and output value will be different.

                        let loaded_ptr = *ptr;
                        let safe       = safe_ptrs.contains(&loaded_ptr);

                        // Go through every instruction inbetween and make sure
                        // that nothing stored to this pointer.
                        for inst in &body[prev_index + 1..inst_id] {
                            match inst {
                                Instruction::Call  { .. }      => continue 'skip_dedup,
                                Instruction::Store { ptr, .. } => {
                                    // Make sure that this store didn't actually affect
                                    // pointer loaded by candidate to deduplicate.
                                    if *ptr == loaded_ptr {
                                        continue 'skip_dedup;
                                    }

                                    // This isn't a safe pointer and we don't know
                                    // if two pointer don't alias. We cannot deduplicate it.
                                    // TODO: Use more sophisticated pointer origin
                                    // analysis to make sure they don't alias.
                                    if !safe {
                                        continue 'skip_dedup;
                                    }
                                }
                                _ => {},
                            }
                        }
                    }

                    // This is a valid candidate for deduplication.

                    // All values which can be deduplicated must create values.
                    let value        = body[prev_index].created_value().unwrap();
                    let target_value = body[inst_id].created_value().unwrap();

                    // Alias output value of current instruction to output value
                    // of deduplication candidate.
                    body[inst_id] = Instruction::Alias {
                        dst: target_value,
                        value,
                    };

                    did_something = true;
                } else {
                    // We haven't seen this instruction before, add it to deduplication list.
                    dedup_list.insert(key, inst_id);
                }
            }
        }

        did_something
    }
}
