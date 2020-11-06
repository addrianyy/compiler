use crate::{FunctionData, Instruction};

pub struct RemoveDeadCodePass;

impl super::Pass for RemoveDeadCodePass {
    fn name(&self) -> &str {
        "dead code elimination"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something  = false;
        let mut used_values    = vec![false; function.value_count()];
        let     creators       = function.value_creators();

        // Remove instructions without side effects which results aren't used.
        //
        // v3 = add u32 v1, v2
        //
        // If v3 isn't used anywhere it will be removed.

        // Go through every instruction every input value to determine which values are used
        // and which are not.
        function.for_each_instruction(|_location, instruction| {
            for value in instruction.read_values() {
                // Handle self-referential PHI instructions.
                if instruction.created_value() != Some(value) {
                    used_values[value.index()] = true;
                }
            }
        });

        // Go through every instruction that creates a value.
        for (value, creator) in creators {
            let creator = function.instruction_mut(creator);

            // If value isn't used and its creator isn't volatile then creator can be safely
            // removed.
            if !creator.is_volatile() && !used_values[value.index()] {
                *creator      = Instruction::Nop;
                did_something = true;
            }
        }

        did_something
    }
}
