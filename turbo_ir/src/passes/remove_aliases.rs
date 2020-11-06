use crate::{FunctionData, Instruction};

pub struct RemoveAliasesPass;

impl super::Pass for RemoveAliasesPass {
    fn name(&self) -> &str {
        "alias elimination"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let     labels        = function.reachable_labels();

        // Some optimization passess will create alias instruction.
        // If v1 is aliased to v0 that means that v1 has always exact value as v0.
        // This optimization pass will actually remove alias instruction and change
        // all uses of its return value to its operand.
        //
        // v2 = alias v1
        // v3 = add u32 v2, v0
        //
        // This will get optimized to:
        // v3 = add u32 v1, v0

        loop {
            let mut alias = None;

            // Go through every instruction in every block to find alias instruction.
            'alias_search: for &label in &labels {
                let body = function.blocks.get_mut(&label).unwrap().iter_mut();

                for instruction in body {
                    if let Instruction::Alias { dst, value } = instruction {
                        // Record replacement information for this alias.
                        alias = Some((*dst, *value));

                        // Remove alias instruction.
                        *instruction = Instruction::Nop;

                        // Break out to perform the replacement.
                        break 'alias_search;
                    }
                }
            }

            if let Some((old, new)) = alias {
                for &label in &labels {
                    let body = function.blocks.get_mut(&label).unwrap().iter_mut();

                    for instruction in body {
                        // Replace all uses of alias output value to alias operand.
                        instruction.transform_inputs(|value| {
                            if *value == old {
                                *value = new;
                            }
                        });
                    }
                }

                did_something = true;

                // Maybe there are more aliases to handle. Continue to the next iteration.
                continue;
            }

            // No alias was found, we can stop searching.
            break;
        }

        did_something
    }
}
