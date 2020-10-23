use std::collections::HashMap;

use super::{FunctionData, Instruction, Pass};

pub struct X86ReorderPass;

impl Pass for X86ReorderPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        
        // Try to create patterns which are matched by X86 backend to create more efficient
        // machine code.
        
        // Handled patterns:
        // icmp; select/bcond

        for label in function.reachable_labels() {
            let mut compares = HashMap::new();

            let body = function.blocks.get_mut(&label).unwrap();

            'next_instruction: for inst_id in 0..body.len() {
                let instruction = &body[inst_id];

                match instruction {
                    Instruction::IntCompare { dst, .. } => {
                        assert!(compares.insert(*dst, inst_id).is_none(),
                                "Compares create multiple same values.");
                    }
                    Instruction::Select     { cond, .. } |
                    Instruction::BranchCond { value: cond, .. } => {
                        if let Some(&cmp_id) = compares.get(cond) {
                            let inbetween = inst_id - cmp_id - 1;
                            if  inbetween == 0 {
                                continue;
                            }

                            for instruction in &body[cmp_id + 1..inst_id] {
                                for value in instruction.read_values() {
                                    if value == *cond {
                                        continue 'next_instruction;
                                    }
                                }
                            }

                            compares.remove(cond);

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
