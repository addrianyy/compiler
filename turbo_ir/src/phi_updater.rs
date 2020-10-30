use super::{FunctionData, Label, Instruction, Set};

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
        let labels: Set<Label> = function.reachable_labels()
            .into_iter()
            .collect();

        function.for_each_instruction_mut(|_location, instruction| {
            if let Instruction::Phi { incoming, .. } = instruction {
                // Remove all incoming value with unreachable labels.
                incoming.retain(|(label, _)| labels.contains(label));
            }
        });
    }
}
