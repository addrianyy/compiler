use crate::{FunctionData, Instruction};

pub struct UndefinedPropagatePass;

impl super::Pass for UndefinedPropagatePass {
    fn name(&self) -> &str {
        "undefined propagation"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut replacements = Vec::new();

        // Propagate undefined values.
        //
        // v5 = select u1 v4, u32 v2, undefined
        // Becomes:
        // v5 = alias v2
        //
        // v3 = add u32 v1, undefined
        // Becomes:
        // v3 = undefined

        function.for_each_instruction(|location, instruction| {
            let mut replacement = None;

            match instruction {
                Instruction::ArithmeticUnary { .. } | Instruction::ArithmeticBinary { .. } => {
                    // If any input is undefined then whole result is undefined.
                    for input in instruction.read_values() {
                        if function.is_value_undefined(input) {
                            replacement = Some(input);
                            break;
                        }
                    }
                }
                Instruction::Select { on_true, on_false, .. } => {
                    // If there is a single non-undefined value then select
                    // becomes alias to that non-undefined value.

                    if function.is_value_undefined(*on_true) {
                        replacement = Some(*on_false);
                    }

                    if function.is_value_undefined(*on_false) {
                        replacement = Some(*on_true);
                    }
                }
                _ => {}
            }

            if let Some(replacement) = replacement {
                let created_value = instruction.created_value().unwrap();
                let instruction   = Instruction::Alias {
                    dst:   created_value,
                    value: replacement,
                };

                replacements.push((location, instruction));
            }
        });

        let did_something = !replacements.is_empty();

        // Actually perform the replacements.
        for (location, replacement) in replacements {
            *function.instruction_mut(location) = replacement;
        }

        did_something
    }
}
