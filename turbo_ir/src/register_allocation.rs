use super::{FunctionData, Value, Location, Label, Map, Set};

type RegallocMap<K, V> = Map<K, V>;
type RegallocSet<K>    = Set<K>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Place {
    Argument(usize),
    StackSlot(usize),
    Register(usize),
}

pub struct RegisterAllocation {
    pub allocation: RegallocMap<Location, RegallocMap<Value, Place>>,
    pub arguments:  RegallocMap<Value, Place>,
    pub used_regs:  RegallocSet<usize>,
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

fn stack_pop_prefer(stack: &mut Vec<usize>, prefer: Option<usize>) -> Option<usize> {
    if let Some(prefer) = prefer {
        if let Some(idx) = stack.iter().position(|x| *x == prefer) {
            stack.remove(idx);

            return Some(prefer);
        }
    }

    stack.pop()
}

impl FunctionData {
    fn lifetimes(&self) -> RegallocMap<Location, Vec<bool>> {
        let mut lifetimes = RegallocMap::default();
        let creators      = self.value_creators();

        for label in self.reachable_labels() {
            let mut used = vec![false; self.value_count()];

            for target_label in self.traverse_bfs(label, false) {
                for inst in &self.blocks[&target_label] {
                    for input in inst.read_values() {
                        // Make sure to not include arguments.
                        if !self.is_value_argument(input) && creators[&input].0 != target_label {
                            used[input.index()] = true;
                        }
                    }
                }
            }
            
            let block = &self.blocks[&label];

            for (inst_id, _) in block.iter().enumerate() {
                let mut used = used.clone();

                for inst in &block[inst_id + 1..] {
                    for input in inst.read_values() {
                        used[input.index()] = true;
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
            RegallocMap<Label, (RegallocMap<Value, Place>, FreePlaces)> =
                RegallocMap::default();

        let mut inst_alloc_state:
            RegallocMap<Location, RegallocMap<Value, Place>> =
                RegallocMap::default();

        {
            // At first all hardware registers are usable.

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
        let mut used_regs = RegallocSet::default();

        for label in labels {
            // If there is not register allocation state for this block then take one
            // from immediate dominator (as we can only use values originating from it).
            #[allow(clippy::map_entry)]
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
                    if !lifetimes[&location][value.index()] {
                        to_free.push((value, place));
                    }
                }

                for (value, place) in to_free {
                    if !matches!(place, Place::Argument(_)) {
                        block_allocs.0.remove(&value);
                    }

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
                    // We will try to allocate output value at the same register as 
                    // first input. This will help to generate better code by backend.
                    let first_input = inst.read_values().get(0).and_then(|value| {
                        // Fix for arguments.
                        inst_allocs.get(&value).cloned()
                    });

                    let preg = if let Some(Place::Register(register)) = first_input {
                        Some(register)
                    } else {
                        None
                    };

                    let pslot = if let Some(Place::StackSlot(slot)) = first_input {
                        Some(slot)
                    } else {
                        None
                    };

                    let register = stack_pop_prefer(&mut block_allocs.1.registers, preg);

                    let place = if let Some(register) = register {
                        used_regs.insert(register);

                        Place::Register(register)
                    } else {
                        let slot = stack_pop_prefer(&mut block_allocs.1.stack_slots, pslot);

                        Place::StackSlot(slot.unwrap_or_else(|| {
                            let slot = next_slot;

                            next_slot += 1;

                            slot
                        }))
                    };

                    block_allocs.0.insert(output, place);
                    inst_allocs.insert(output, place);
                }

                assert!(inst_alloc_state.insert(location, inst_allocs).is_none(), 
                        "Multiple instruction allocation states.");
            }
        }

        let mut arguments = RegallocMap::default();

        for (index, argument) in self.argument_values.iter().enumerate() {
            arguments.insert(*argument, Place::Argument(index));
        }

        RegisterAllocation {
            allocation: inst_alloc_state,
            slots:      next_slot,
            arguments,
            used_regs,
        }
    }
}
