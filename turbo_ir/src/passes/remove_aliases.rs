use super::{FunctionData, Instruction, Pass};

pub struct RemoveAliasesPass;

impl Pass for RemoveAliasesPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let     labels        = function.reachable_labels();

        // Some optimization passess will create alias instruction.
        // If %1 is aliased to %0 that means that %1 has always exact value as %0.
        // This optimization pass will actually remove alias instruction and change
        // all uses of its return value to its operand.
        //
        // %2 = alias %1
        // %3 = add u32 %2, %0
        //
        // This will get optimized to:
        // %3 = add u32 %1, %0

        loop {
            let mut alias = None;

            // Go through every instruction in every block to find alias instruction.
            'alias_search: for &label in &labels {
                for inst in function.blocks.get_mut(&label).unwrap().iter_mut() {
                    if let Instruction::Alias { dst, value } = inst {
                        // Record replacement information for alias.
                        alias = Some((*dst, *value));

                        // Remove alias instruction.
                        *inst = Instruction::Nop;

                        // Break out to perform the replacement.
                        break 'alias_search;
                    }
                }
            }

            if let Some(alias) = alias {
                did_something = true;

                for &label in &labels {
                    for inst in function.blocks.get_mut(&label).unwrap().iter_mut() {
                        // Replace all uses of alias output value to alias operand.
                        inst.transform_inputs(|reg| {
                            if *reg == alias.0 { 
                                *reg = alias.1;
                            }
                        });
                    }
                }

                // Maybe there are more aliases to handle. Continue to the next iteration.
                continue;
            }

            // No alias was found, we can stop searching.
            break;
        }

        did_something
    }
}
