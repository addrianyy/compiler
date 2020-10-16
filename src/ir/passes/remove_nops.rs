use super::{FunctionData, Instruction, Pass};

pub struct RemoveNopsPass;

impl Pass for RemoveNopsPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        for label in function.reachable_labels() {
            function.blocks.get_mut(&label)
                .unwrap()
                .retain(|inst| !matches!(inst, Instruction::Nop));
        }

        // This optimization pass shouldn't change anything so just return false.
        false
    }
}
