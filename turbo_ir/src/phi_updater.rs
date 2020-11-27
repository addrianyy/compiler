use super::{FunctionData, Label, Instruction};

#[derive(Default)]
pub(super) struct PhiUpdater {
    removed: Vec<(Label, Label)>,
}

impl PhiUpdater {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn removed_branch(&mut self, branch: Label, target: Label) {
        self.removed.push((branch, target));
    }

    pub fn apply(self, function: &mut FunctionData) {
        // TODO: Actually use the removed data.
        let flow_incoming = function.flow_graph_incoming();

        function.for_each_instruction_mut(|location, instruction| {
            if let Instruction::Phi { incoming, .. } = instruction {
                let predecessors = &flow_incoming[&location.label()];

                // Remove all incoming values with labels which are not predecessors.
                incoming.retain(|(label, _)| predecessors.contains(label));
            }
        });
    }
}
