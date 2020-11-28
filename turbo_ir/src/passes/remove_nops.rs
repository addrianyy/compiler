use crate::FunctionData;

pub struct RemoveNopsPass;

impl super::Pass for RemoveNopsPass {
    fn name(&self) -> &str {
        "nop elimination"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::remove_nops()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        // Nops are created by optimization passes to eliminate unneeded instructions.
        // This pass will go through every block and remove nops from it.

        for label in function.reachable_labels() {
            function.blocks.get_mut(&label)
                .unwrap()
                .retain(|instruction| !instruction.is_nop());
        }

        // This optimization pass shouldn't change anything so just return false.
        false
    }
}
