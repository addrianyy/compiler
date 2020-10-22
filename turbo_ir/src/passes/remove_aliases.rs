use super::{FunctionData, Instruction, Pass};

pub struct RemoveAliasesPass;

impl Pass for RemoveAliasesPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let     labels        = function.reachable_labels();

        loop {
            let mut alias = None;

            'alias_search: for &label in &labels {
                for inst in function.blocks.get_mut(&label).unwrap().iter_mut() {
                    if let Instruction::Alias { dst, value } = inst {
                        alias = Some((*dst, *value));
                        *inst = Instruction::Nop;

                        break 'alias_search;
                    }
                }
            }

            if let Some(alias) = alias {
                did_something = true;

                for &label in &labels {
                    for inst in function.blocks.get_mut(&label).unwrap().iter_mut() {
                        inst.transform_inputs(|reg| {
                            if *reg == alias.0 { 
                                *reg = alias.1;
                            }
                        });
                    }
                }

                continue;
            }

            break;
        }

        did_something
    }
}
