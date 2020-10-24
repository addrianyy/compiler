use super::{FunctionData, Instruction, Pass};

pub struct RemoveNopsPass;

impl Pass for RemoveNopsPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        // Nops are created by optimization passes to eliminate unneeded instructions.
        // This pass will go through every block and remove nops from it.

        for label in function.reachable_labels() {
            function.blocks.get_mut(&label)
                .unwrap()
                .retain(|instruction| !matches!(instruction, Instruction::Nop));
        }

        // This optimization pass shouldn't change anything so just return false.
        false
    }
}
