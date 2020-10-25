use super::{FunctionData, Instruction, Pass};
use super::super::Location;

pub struct RemoveKnownLoadsPass;

impl Pass for RemoveKnownLoadsPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let pointer_analysis = function.analyse_pointers();
        let mut replacements = Vec::new();

        for label in function.reachable_labels() {
            let body = &function.blocks[&label];

            'next_instruction: for inst_id in 0..body.len() {
                let instruction = &body[inst_id];

                if let Instruction::Load { dst, ptr } = *instruction {
                    let mut load_value = None;

                    for instruction in body[0..inst_id].iter().rev() {
                        match instruction {
                            Instruction::Store { ptr: stored_ptr, value } => {
                                if *stored_ptr == ptr {
                                    load_value = Some(*value);

                                    break;
                                } else if pointer_analysis.can_alias(ptr, *stored_ptr) {
                                    continue 'next_instruction;
                                }
                            }
                            Instruction::Call { .. } => continue 'next_instruction,
                            _                        => {}
                        }
                    }

                    if let Some(load_value) = load_value {
                        let replacement = Instruction::Alias {
                            dst,
                            value: load_value,
                        };

                        replacements.push((Location(label, inst_id), replacement));
                    }
                }
            }
        }

        let did_something = !replacements.is_empty();

        // Actually perform the replacements.
        for (location, replacement) in replacements {
            *function.instruction_mut(location) = replacement;
        }

        did_something
    }
}
