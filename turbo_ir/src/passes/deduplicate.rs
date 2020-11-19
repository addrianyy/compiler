use crate::{FunctionData, Instruction, Location, LargeKeyMap, Map,
            ValidationCache, analysis::KillTarget};

type DeduplicationKey = (std::mem::Discriminant<Instruction>, Vec<crate::instruction::Param>);

fn can_be_deduplicated(instruction: &Instruction) -> bool {
    match instruction {
        Instruction::Nop               => false,
        Instruction::Alias      { .. } => false,
        Instruction::Phi        { .. } => false,
        Instruction::StackAlloc { .. } => false,
        x if x.is_volatile()           => false,
        _                              => true,
    }
}

fn deduplication_key(instruction: &Instruction) -> DeduplicationKey {
    (std::mem::discriminant(instruction), instruction.input_parameters())
}

fn deduplicate(function: &mut FunctionData, source: Location, target: Location) {
    // All values which can be deduplicated must create values.
    let source_value = function.instruction(source).created_value().unwrap();
    let target_value = function.instruction(target).created_value().unwrap();

    // Get mutable reference to block body.
    let mut_body = function.blocks.get_mut(&target.label()).unwrap();

    // Alias output value of current instruction to output value
    // of deduplication candidate.
    mut_body[target.index()] = Instruction::Alias {
        dst:   target_value,
        value: source_value,
    };
}

/// Precise deduplication that can deduplicate values across blocks.
fn deduplicate_precise(function: &mut FunctionData) -> bool {
    let mut did_something = false;
    let mut vcache        = ValidationCache::default();
    let pointer_analysis  = function.analyse_pointers();
    let dominators        = function.dominators();
    let labels            = function.reachable_labels();

    let mut dedup_list: LargeKeyMap<_, Vec<Location>> = LargeKeyMap::default();

    // Create a list of all deduplication candidates for a given instruction key.
    function.for_each_instruction_with_labels(&labels, |location, instruction| {
        // Skip instructions which cannot be deduplicated.
        if !can_be_deduplicated(instruction) {
            return;
        }

        // Create a unique key that will describe instruction type and its input operands.
        let key = deduplication_key(instruction);

        // Get deduplication candidates for this instruction key and add current instruction
        // as a candiate.
        dedup_list.entry(key)
            .or_insert_with(Vec::new)
            .push(location);
    });

    let mut fast_dedup: Map<Location, &[Location]> = Map::default();

    // Build map that allows for faster queries.
    for locations in dedup_list.values() {
        fast_dedup.reserve(locations.len());

        for &location in locations {
            assert!(fast_dedup.insert(location, locations).is_none(),
                    "Deduplication entry added multiple times.");
        }
    }

    for &label in &labels {
        let mut body = &function.blocks[&label];
        let body_len = body.len();

        for inst_id in 0..body_len {
            let location    = Location::new(label, inst_id);
            let instruction = &body[inst_id];

            let mut deduplication = None;
            let mut best_icount   = None;

            // Skip instructions which cannot be deduplicated.
            if !can_be_deduplicated(instruction) {
                continue;
            }

            // Try to get possible instructions which we can deduplicate this instruction from.
            if let Some(sources) = fast_dedup.get(&location) {
                // Recalculate `phi_used` here because added aliases may have changed it.
                let phi_used = function.phi_used_values(&labels);

                // Find the best source for deduplication.
                for &source in *sources {
                    if location == source {
                        continue;
                    }

                    // It's possible that we may source this instruction from
                    // already deduplicated instruction. This is fine.

                    let result = if let Instruction::Load { ptr, .. } = instruction {
                        let load_ptr = *ptr;

                        // If both locations are in different blocks and value
                        // is used in PHI then `validate_path_memory` cannot reason about
                        // it. TODO: Fix this.
                        if source.label() != location.label() && phi_used.contains(load_ptr) {
                            continue;
                        }

                        // Special care needs to be taken if we want to deduplicate
                        // load. Something inbetween two instructions may have
                        // modified loaded ptr and output value will be different.
                        function.validate_path_memory(&dominators, source, location,
                                                      KillTarget::End, &mut vcache, |instruction| {
                            !function.can_store_pointer(instruction, &pointer_analysis, load_ptr)
                        })
                    } else {
                        function.validate_path_count(&dominators, source, location, &mut vcache)
                    };

                    if let Some(instruction_count) = result {
                        // If it's a valid source, check if it's closer then the
                        // best one. If it is then set it as current best.
                        let better = match best_icount {
                            Some(icount) => instruction_count < icount,
                            None         => true,
                        };

                        if better {
                            deduplication = Some(source);
                            best_icount   = Some(instruction_count);
                        }
                    }
                }
            }

            if let Some(deduplication) = deduplication {
                // We have found a valid source for deduplication.
                deduplicate(function, deduplication, Location::new(label, inst_id));

                body          = &function.blocks[&label];
                did_something = true;
            }
        }
    }

    did_something
}

/// Fast deduplication that can only deduplicate values within one block.
fn deduplicate_fast(function: &mut FunctionData) -> bool {
    let mut did_something                     = false;
    let mut dedup_list: LargeKeyMap<_, usize> = LargeKeyMap::default();

    let pointer_analysis = function.analyse_pointers();

    for label in function.reachable_labels() {
        dedup_list.clear();

        let mut body = &function.blocks[&label];
        let body_len = body.len();

        'next_instruction: for inst_id in 0..body_len {
            let instruction = &body[inst_id];

            // Skip instructions which cannot be deduplicated.
            if !can_be_deduplicated(instruction) {
                continue;
            }

            let key = deduplication_key(instruction);

            // Try to get instruction which we can deduplicate this instruction from.
            if let Some(&source_id) = dedup_list.get(&key) {
                if let Instruction::Load { ptr, .. } = &body[source_id] {
                    // Go through every instruction inbetween and make sure
                    // that nothing affected value of this pointer.
                    for instruction in &body[source_id + 1..inst_id] {
                        if function.can_store_pointer(instruction, &pointer_analysis, *ptr) {
                            // Make this `load` source for another deduplication.
                            dedup_list.insert(key, inst_id);

                            continue 'next_instruction;
                        }
                    }
                }

                // We have found a valid source for deduplication.
                deduplicate(function, Location::new(label, source_id),
                            Location::new(label, inst_id));

                body          = &function.blocks[&label];
                did_something = true;
            } else {
                // We haven't seen this instruction before, add it to the deduplication list.
                dedup_list.insert(key, inst_id);
            }
        }
    }

    did_something
}

// Find two or more non-volatile instructions with the same operands and try to
// reuse their output values.
//
// v5 = add u32 v1, v2
// v6 = add u32 v1, v2
// v7 = neg u32 v6
//
// Will get optimized to:
// v5 = add u32 v1, v2
// v7 = neg v5

pub struct DeduplicateFastPass;

impl super::Pass for DeduplicateFastPass {
    fn name(&self) -> &str {
        "fast deduplication"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::deduplicate()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        deduplicate_fast(function)
    }
}

pub struct DeduplicatePrecisePass;

impl super::Pass for DeduplicatePrecisePass {
    fn name(&self) -> &str {
        "precise deduplication"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::deduplicate()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        deduplicate_precise(function)
    }
}
