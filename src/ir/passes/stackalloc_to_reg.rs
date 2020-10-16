use super::{FunctionData, Instruction, Pass};

pub struct StackallocToRegPass;

impl Pass for StackallocToRegPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        let stackallocs = function.find_stackallocs(Some(1));
        let dominators  = function.dominators();

        'skip: for (value, location) in stackallocs {
            let uses = function.find_uses(value);

            let mut store = None;
            let mut loads = Vec::new();

            for &location in &uses {
                match function.instruction(location) {
                    Instruction::Store { ptr, value: stored_value } => {
                        if *ptr != value || *stored_value == value {
                            continue 'skip;
                        }

                        if store.is_some() {
                            continue 'skip;
                        }

                        store = Some((location, *stored_value));
                    }
                    Instruction::Load { ptr, .. } => {
                        if *ptr == value {
                            loads.push(location);
                        }
                    }
                    _ => continue 'skip,
                }
            }

            if let Some((store_location, stored_value)) = store {
                for &load_location in &loads {
                    if !function.validate_path(&dominators, store_location, load_location) {
                        println!("WARNING: Possibly uninitialized use of {}.", value);
                        continue 'skip;
                    }
                }

                for &load_location in &loads {
                    let instruction = function.instruction_mut(load_location);

                    match instruction {
                        Instruction::Load { dst, .. } => {
                            *instruction = Instruction::Alias { 
                                dst:   *dst, 
                                value: stored_value,
                            };
                        }
                        _ => unreachable!(),
                    }
                }

                *function.instruction_mut(store_location) = Instruction::Nop;
                *function.instruction_mut(location)       = Instruction::Nop;

                did_something = true;
            }
        }

        did_something
    }
}

