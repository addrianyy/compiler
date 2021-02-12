use crate::{FunctionData, Instruction, Map};

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

        // Try to reorder instructions to create patterns which are matched by x86 backend
        // to create more efficient machine code.
        //
        // For now this optimization pass will only try to move cmps just above select/bcond
        // instructions.

        for label in function.reachable_labels() {
            let mut compares  = Map::default();
            let mut skip_next = false;

            let body = function.blocks.get_mut(&label).unwrap();

            'next_instruction: for inst_id in 0.. {
                // Because size changes dynamically we need to check it manually.
                if inst_id >= body.len() {
                    break;
                }

                // If previous iteration inserted instruction this iteration is at position
                // of already visited instruction. Skip it.
                if skip_next {
                    skip_next = false;
                    continue;
                }

                match &body[inst_id] {
                    Instruction::IntCompare { dst, .. } => {
                        // Record information about instruction which can be a
                        // candidate for reordering.
                        assert!(compares.insert(*dst, inst_id).is_none(),
                                "Compares create multiple same values.");
                    }
                    Instruction::Select     { cond, .. } |
                    Instruction::BranchCond { cond, .. } => {
                        // We found `select`/`bcond` and we want to move corresponding `cmp`
                        // just above it.
                        if let Some(&cmp_id) = compares.get(cond) {
                            // Check if `cmp` is actually just above us. In this case
                            // we have nothing to do.
                            let inbetween = inst_id - cmp_id - 1;
                            if  inbetween == 0 {
                                continue 'next_instruction;
                            }

                            // We want to move `cmp` down. We need to make sure that
                            // no instruction so far read its output value. If that's the
                            // case, moving `cmp` would violate SSA properites.
                            for instruction in &body[cmp_id + 1..inst_id] {
                                for value in instruction.read_values() {
                                    if value == *cond {
                                        continue 'next_instruction;
                                    }
                                }
                            }

                            // We are able to move `cmp` instruction.

                            // This `cmp` instruction is non-movable from now.
                            compares.remove(cond);

                            // Move `cmp` instruction down so it's just above us.
                            // We are only updating indices under us.
                            let compare = std::mem::replace(&mut body[cmp_id],
                                                            Instruction::Nop);
                            body.insert(inst_id, compare);

                            // Next index will be this instruction so we need to skip it.
                            skip_next     = true;
                            did_something = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        did_something
    }
}
