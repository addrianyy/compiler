use crate::{FunctionData, Instruction, Map};

pub struct X86ReorderPass;

impl super::Pass for X86ReorderPass {
    fn name(&self) -> &str {
        "x86 reordering"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        // Try to reorder instructions to create patterns which are matched by x86 backend
        // to create more efficient machine code.
        // 
        // For now this optimization pass will only try to move icmps just above select/bcond
        // instructions.

        for label in function.reachable_labels() {
            let mut compares = Map::default();

            let body = function.blocks.get_mut(&label).unwrap();

            'next_instruction: for inst_id in 0..body.len() {
                let instruction = &body[inst_id];

                match instruction {
                    Instruction::IntCompare { dst, .. } => {
                        // Record information about instruction which can be a 
                        // candidate for reordering.
                        assert!(compares.insert(*dst, inst_id).is_none(),
                                "Compares create multiple same values.");
                    }
                    Instruction::Select     { cond, .. } |
                    Instruction::BranchCond { cond, .. } => {
                        // We found select/bcond and we want to move corresponding icmp
                        // just above it.
                        if let Some(&cmp_id) = compares.get(cond) {
                            // Check if icmp is actually just above us. In this case
                            // we have nothing to do.
                            let inbetween = inst_id - cmp_id - 1;
                            if  inbetween == 0 {
                                continue;
                            }

                            // We want to move icmp down. We need to make sure that
                            // no instruction so far read its output value. If that's the
                            // case, moving icmp would violate SSA properites.
                            for instruction in &body[cmp_id + 1..inst_id] {
                                for value in instruction.read_values() {
                                    if value == *cond {
                                        continue 'next_instruction;
                                    }
                                }
                            }

                            // We are able to move icmp instruction.

                            // This icmp instruction is non-movable from now.
                            compares.remove(cond);

                            // Move icmp instruction down so it's just above us.
                            let compare = std::mem::replace(&mut body[cmp_id],
                                                            Instruction::Nop);

                            body.insert(inst_id, compare);
                            body.remove(cmp_id);

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
