use crate::{FunctionData, Instruction, Value, Location, Set};

enum Prop {
    Value(Value),
    Undef,
    Nop,
    None,
}

pub struct UndefinedPropagatePass;

impl super::Pass for UndefinedPropagatePass {
    fn name(&self) -> &str {
        "undefined propagation"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::undefined_propagate()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let mut undefined     = Set::default();

        // Propagate undefined values.
        //
        // v5 = select u1 v4, u32 v2, undefined
        // Becomes:
        // v5 = alias v2
        //
        // v3 = add u32 v1, undefined
        // Becomes:
        // v3 = undefined

        macro_rules! is_undefined {
            ($value: expr) => {
                function.is_value_undefined($value) || undefined.contains(&$value)
            }
        }

        for label in function.reachable_labels() {
            let mut body = &function.blocks[&label];
            let body_len = body.len();

            for inst_id in 0..body_len {
                let instruction = &body[inst_id];
                let mut prop    = Prop::None;

                match instruction {
                    Instruction::ArithmeticUnary { .. } | Instruction::ArithmeticBinary { .. } |
                    Instruction::IntCompare      { .. } | Instruction::Load             { .. } |
                    Instruction::GetElementPtr   { .. } | Instruction::Cast             { .. } => {
                        // If any input is undefined then whole result is undefined.
                        for input in instruction.read_values() {
                            if is_undefined!(input) {
                                prop = Prop::Undef;
                                break;
                            }
                        }
                    }
                    Instruction::Store { .. } => {
                        // If any input is undefined then remove the store.
                        for input in instruction.read_values() {
                            if is_undefined!(input) {
                                prop = Prop::Nop;
                                break;
                            }
                        }
                    }
                    Instruction::Select { on_true, on_false, .. } => {
                        // If there is a single non-undefined value then select
                        // becomes alias to that non-undefined value.

                        if is_undefined!(*on_true) {
                            prop = Prop::Value(*on_false);
                        }

                        if is_undefined!(*on_false) {
                            prop = Prop::Value(*on_true);
                        }
                    }
                    _ => {}
                }

                let replacement = match prop {
                    Prop::None => None,
                    Prop::Nop  => Some(Instruction::Nop),
                    Prop::Value(value) => {
                        let output = instruction.created_value().unwrap();

                        Some(Instruction::Alias {
                            dst: output,
                            value,
                        })
                    }
                    Prop::Undef => {
                        let output = instruction.created_value().unwrap();
                        let ty     = function.value_type(output);
                        let undef  = function.undefined_value(ty);

                        undefined.insert(output);

                        body = &function.blocks[&label];

                        Some(Instruction::Alias {
                            dst:   output,
                            value: undef,
                        })
                    }
                };

                if let Some(replacement) = replacement {
                    let location = Location::new(label, inst_id);

                    *function.instruction_mut(location) = replacement;

                    body          = &function.blocks[&label];
                    did_something = true;
                }
            }
        }

        did_something
    }
}
