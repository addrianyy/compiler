use super::{FunctionData, Location, Value, Instruction};

pub(super) trait Pass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool;
}

pub(super) struct TestPass;

impl TestPass {
    fn find_stackallocs(&self, function: &FunctionData) -> Vec<(Value, Location)> {
        let mut results = Vec::new();

        function.for_each_instruction(|location, inst| {
            if let Instruction::StackAlloc { dst, size, .. } = inst {
                if *size == 1 {
                    results.push((*dst, location));
                }
            }
        });

        results
    }

    fn find_uses(&self, function: &FunctionData, value: Value) -> Vec<Location> {
        let mut uses = Vec::new();

        function.for_each_instruction(|location, inst| {
            if inst.read_values().iter().any(|x| *x == value) {
                uses.push(location);
            }
        });

        uses
    }
}

impl Pass for TestPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        let stackallocs = self.find_stackallocs(function);
        let dominators  = function.dominators();

        'skip: for (value, location) in stackallocs {
            let uses = self.find_uses(function, value);

            let mut store = None;
            let mut loads = Vec::new();

            for &location in &uses {
                match function.instruction(location) {
                    Instruction::Store { ptr, value: stored_value } => {
                        if *ptr == value {
                            if store.is_some() {
                                continue 'skip;
                            }

                            store = Some((location, *stored_value));
                        }
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

pub(super) struct RemoveAliasesPass;

impl Pass for RemoveAliasesPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let     labels        = function.reachable_labels();

        loop {
            let mut alias = None;

            'alias_search: for &label in &labels {
                for inst in function.blocks.get_mut(&label).unwrap().iter_mut() {
                    if let Instruction::Alias { dst, value } = inst {
                        alias = Some((*dst, *value));
                        *inst = Instruction::Nop;

                        break 'alias_search;
                    }
                }
            }

            if let Some(alias) = alias {
                did_something = true;

                for &label in &labels {
                    for inst in function.blocks.get_mut(&label).unwrap().iter_mut() {
                        inst.transform_inputs(|reg| {
                            if *reg == alias.0 { 
                                *reg = alias.1;
                            }
                        });
                    }
                }

                continue;
            }

            break;
        }

        did_something
    }
}

pub(super) struct RemoveNopsPass;

impl Pass for RemoveNopsPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        for label in function.reachable_labels() {
            function.blocks.get_mut(&label)
                .unwrap()
                .retain(|inst| !matches!(inst, Instruction::Nop));
        }

        // TODO
        false
    }
}

pub(super) struct RemoveDeadCodePass;

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
