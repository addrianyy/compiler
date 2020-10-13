use std::collections::BTreeMap;

use super::{FunctionData, Value, Location, Label};

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Place {
    Argument(usize),
    StackSlot(usize),
    Register(usize),
}

pub struct RegisterAllocation {
    pub allocation: BTreeMap<Location, BTreeMap<Value, Place>>,
    pub arguments:  BTreeMap<Value, Place>,
    pub slots:      usize,
}

impl RegisterAllocation {
    pub fn get(&self, location: Location, value: Value) -> Place {
        if let Some(place) = self.arguments.get(&value) {
            return *place;
        }

        self.allocation[&location][&value]
    }
}

impl FunctionData {
    fn lifetimes(&self) -> BTreeMap<Location, Vec<bool>> {
        let mut lifetimes = BTreeMap::new();
        let creators      = self.value_creators();

        for label in self.reachable_labels() {
            let mut used = vec![false; self.next_value.0];

            for target_label in self.traverse_bfs(label, false) {
                for inst in &self.blocks[&target_label] {
                    for input in inst.read_values() {
                        if creators[&input].0 != target_label {
                            used[input.0] = true;
                        }
                    }
                }
            }
            
            let block = &self.blocks[&label];

            for (inst_id, _) in block.iter().enumerate() {
                let mut used = used.clone();

                for inst in &block[inst_id + 1..] {
                    for input in inst.read_values() {
                        used[input.0] = true;
                    }
                }

                lifetimes.insert(Location(label, inst_id), used);
            }
        }

        lifetimes
    }

    pub(super) fn allocate_registers(&self, hardware_registers: usize) -> RegisterAllocation {
        #[derive(Default, Clone)]
        struct FreePlaces {
            registers:   Vec<usize>,
            stack_slots: Vec<usize>,
        }

        let mut block_alloc_state:
            BTreeMap<Label, (BTreeMap<Value, Place>, FreePlaces)> =
                BTreeMap::new();

        let mut inst_alloc_state:
            BTreeMap<Location, BTreeMap<Value, Place>> =
                BTreeMap::new();

        {
            let entry_state = block_alloc_state
                .entry(Label(0))
                .or_insert_with(Default::default);

            for index in (0..hardware_registers).rev() {
                entry_state.1.registers.push(index);
            }
        }

        let labels     = self.reachable_labels();
        let dominators = self.dominators();
        let lifetimes  = self.lifetimes();

        let mut next_slot = 0;

        for label in labels {
            if !block_alloc_state.contains_key(&label) {
                let idom   = dominators[&label];
                let allocs = block_alloc_state[&idom].clone();

                block_alloc_state.insert(label, allocs);
            }

            let block_allocs = block_alloc_state.get_mut(&label).unwrap();
            let block        = &self.blocks[&label];

            for (inst_id, inst) in block.iter().enumerate() {
                let location = Location(label, inst_id);

                let mut inst_allocs                  = block_allocs.0.clone();
                let mut to_free: Vec<(Value, Place)> = Vec::new();

                for (&value, &place) in block_allocs.0.iter() {
                    if !lifetimes[&location][value.0] {
                        to_free.push((value, place));
                    }
                }

                for (value, place) in to_free {
                    block_allocs.0.remove(&value);

                    match place {
                        Place::StackSlot(value) => {
                            block_allocs.1.stack_slots.push(value);
                        }
                        Place::Register(value) => {
                            block_allocs.1.registers.push(value);
                        }
                        Place::Argument(_) => {
                        }
                    }
                }

                if let Some(output) = inst.created_value() {
                    let place = if let Some(register) = block_allocs.1.registers.pop() {
                        Place::Register(register)
                    } else {
                        Place::StackSlot(block_allocs.1.stack_slots.pop().unwrap_or_else(|| {
                            let slot = next_slot;

                            next_slot += 1;

                            slot
                        }))
                    };

                    block_allocs.0.insert(output, place);
                    inst_allocs.insert(output, place);

                    println!("Allocated {} to {:?}", output, place);
                }

                assert!(inst_alloc_state.insert(location, inst_allocs).is_none(), 
                        "Multiple instruction allocation states.");
            }
        }

        let mut arguments = BTreeMap::new();

        for (index, argument) in self.argument_values.iter().enumerate() {
            arguments.insert(*argument, Place::Argument(index));
        }

        RegisterAllocation {
            allocation: inst_alloc_state,
            slots: next_slot,
            arguments,
        }
    }
}
