use std::collections::HashMap;

use super::{FunctionData, Instruction, Pass};
use super::super::Cast;

pub struct RemoveIneffectiveOperationsPass;

impl Pass for RemoveIneffectiveOperationsPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        // Sign extensions only for now.
        let mut extensions = HashMap::new();

        function.for_each_instruction(|_, instruction| {
            if let Instruction::Cast { dst, cast: Cast::SignExtend, value, .. } = instruction {
                extensions.insert(*dst, *value);
            }
        });


        for label in function.reachable_labels() {
            let body = function.blocks.get_mut(&label).unwrap();

            for inst in body {
                if let Instruction::GetElementPtr { dst, source, index } = inst {
                    // GEP sign extends index by default.
                    if let Some(index) = extensions.get(index) {
                        *inst = Instruction::GetElementPtr {
                            dst:    *dst,
                            source: *source,
                            index:  *index,
                        };
                    }
                }
            }
        }

        false
    }
}
