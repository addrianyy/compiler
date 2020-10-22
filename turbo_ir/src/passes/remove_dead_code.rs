use super::{FunctionData, Instruction, Pass};

pub struct RemoveDeadCodePass;

impl Pass for RemoveDeadCodePass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something  = false;
        let mut used_values    = vec![false; function.value_count()];
        let     creators       = function.value_creators();

        function.for_each_instruction(|_location, instruction| {
            for value in instruction.read_values() {
                used_values[value.0] = true;
            }
        });

        for (value, creator) in creators {
            let creator = function.instruction_mut(creator);

            if !creator.is_volatile() && !used_values[value.0] {
                *creator      = Instruction::Nop;
                did_something = true;
            }
        }

        did_something
    }
}
