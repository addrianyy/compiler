use super::{FunctionData, Instruction, Pass};

pub struct StackallocToRegPass;

impl Pass for StackallocToRegPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        // It is often the case that variables are located on the stack and not as a value.
        // Give a stackalloc, if its result is only used by one store and N loads it's possible
        // to move it out of memory.
        //
        // %1 = stackalloc u32
        // %2 = store %2, %0
        // %3 = load %2
        // %4 = neg %3
        //
        // Will get optimized to:
        // %4 = neg %0

        // Find all non-array stackallocs.
        let stackallocs = function.find_stackallocs(Some(1));
        let dominators  = function.dominators();

        'skip: for (value, location) in stackallocs {
            // Get every use of pointer returned by stackalloc.
            let uses = function.find_uses(value);

            let mut store = None;
            let mut loads = Vec::new();

            // Collect store and load information from stackalloc. If any other instruction
            // uses stackalloc than we can't reason about it.
            for &location in &uses {
                match function.instruction(location) {
                    Instruction::Store { ptr, value: stored_value } => {
                        // Make sure that we are actually storing TO `value`, not
                        // storing `value`.
                        if *ptr != value || *stored_value == value {
                            continue 'skip;
                        }

                        // Skip it if there is more then 1 store.
                        if store.is_some() {
                            continue 'skip;
                        }

                        // Save store information.
                        store = Some((location, *stored_value));
                    }
                    Instruction::Load { .. } => {
                        loads.push(location);
                    }
                    _ => continue 'skip,
                }
            }

            if let Some((store_location, stored_value)) = store {
                // Check for uninitialized load UB.
                for &load_location in &loads {
                    // If there is only one store instruction and it doesn't dominate all
                    // load instructions that means that uninitialized memory is being read.
                    // That is undefined behaviour, but if we move that value from memory to 
                    // register we will not have a way of maintaining SSA properties and therefore
                    // we will not be able to generate any code. So let's be nice
                    // and leave it as it is.
                    if !function.validate_path(&dominators, store_location, load_location) {
                        println!("WARNING: Uninitialized use of {}.", value);
                        continue 'skip;
                    }
                }

                // We found a valid candidate for moving out of memory to register.
                // Modify all spots where our candidate is loaded.
                for &load_location in &loads {
                    let instruction = function.instruction_mut(load_location);

                    // Everytime this value is loaded we will alias load result to value
                    // stored there.
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

                // Remove store of value to stackalloc and stackalloc itself.
                *function.instruction_mut(store_location) = Instruction::Nop;
                *function.instruction_mut(location)       = Instruction::Nop;

                // If there are no loads then DCE will optimize everything out.

                did_something = true;
            }
        }

        did_something
    }
}

