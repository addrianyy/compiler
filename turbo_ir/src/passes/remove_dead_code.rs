use crate::{FunctionData, Instruction, Map, Value, Location};

fn try_to_dce(function: &mut FunctionData, location: Location,
              creators: &Map<Value, Location>, value_uses: &mut [u32],
              work_list: &mut Vec<Location>) -> bool {
    let instruction = function.instruction_mut(location);

    // Skip if this instruction was already removed.
    if instruction.is_nop() {
        return false;
    }

    let value = instruction.created_value().expect("Tried to DCE instruction \
                                                    which doesn't return value.");

    // Check if this instruction can be removed (it must have no uses and be non-volatile).
    if !instruction.is_volatile() && value_uses[value.index()] == 0 {
        let inputs = instruction.read_values();

        // Remove instruction.
        *instruction = Instruction::Nop;

        // Removing this instruction may have caused other instructions to become dead.
        // Check all inputs to removed instruction.
        for input in inputs {
            // Ignore self reference in PHI.
            if input == value {
                continue;
            }

            // Remove one use.
            let uses = value_uses[input.index()];
            let uses = uses.checked_sub(1).expect("Uses underflow.");

            value_uses[input.index()] = uses;

            // Add instruction to the work list if input value is not used anymore.
            if uses == 0 {
                if let Some(creator) = creators.get(&input) {
                    work_list.push(*creator);
                }
            }
        }

        return true;
    }

    false
}

pub struct RemoveDeadCodePass;

impl super::Pass for RemoveDeadCodePass {
    fn name(&self) -> &str {
        "dead code elimination"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::remove_dead_code()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let mut value_uses    = vec![0; function.value_count()];
        let mut work_list     = Vec::new();
        let     labels        = function.reachable_labels();
        let     creators      = function.value_creators_with_labels(&labels);

        // Remove instructions without side effects which results aren't used.
        //
        // v3 = add u32 v1, v2
        //
        // If v3 isn't used anywhere it will be removed.

        // Go through every instruction and every input value to determine use counts
        // of every value.
        function.for_each_instruction_with_labels(&labels, |_location, instruction| {
            let created_value = instruction.created_value();

            for value in instruction.read_values() {
                // Don't count self reference in PHI as use.
                if created_value != Some(value) {
                    value_uses[value.index()] += 1;
                }
            }
        });

        // Remove all instructions that return value that is not used.
        for &creator in creators.values() {
            did_something |= try_to_dce(function, creator, &creators, &mut value_uses,
                                        &mut work_list);
        }

        // Removing instructions may have caused other instructions to become dead.
        while let Some(location) = work_list.pop() {
            did_something |= try_to_dce(function, location, &creators, &mut value_uses,
                                        &mut work_list);
        }

        did_something
    }
}
