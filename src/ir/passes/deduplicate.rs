use std::collections::{HashMap, HashSet};

use super::{FunctionData, Instruction, Pass};

pub struct DeduplicatePass;

impl Pass for DeduplicatePass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let mut safe_ptrs     = HashSet::new();

        'skip: for (value, _) in function.find_stackallocs(None) {
            for location in function.find_uses(value) {
                match function.instruction(location) {
                    Instruction::Store { ptr, value: stored_value } => {
                        if *ptr != value || *stored_value == value {
                            continue 'skip;
                        }
                    }
                    Instruction::Load { .. } => {
                    }
                    _ => continue 'skip,
                }
            }

            safe_ptrs.insert(value);
        }

        for label in function.reachable_labels() {
            let mut dedup_list: HashMap<_, usize> = HashMap::new();

            let body = function.blocks.get_mut(&label).unwrap();

            'skip_dedup: for inst_id in 0..body.len() {
                let inst = &body[inst_id];

                match inst {
                    Instruction::Nop          => continue,
                    Instruction::Alias { .. } => continue,
                    x if x.is_volatile()      => continue,
                    _                         => {}
                }

                let key = (std::mem::discriminant(inst), inst.input_parameters());

                if let Some(&prev_index) = dedup_list.get(&key) {
                    if let Instruction::Load { ptr, .. } = inst {
                        let loaded_ptr = *ptr;
                        let safe       = safe_ptrs.contains(&loaded_ptr);

                        for inst in &body[prev_index + 1..inst_id] {
                            match inst {
                                Instruction::Call  { .. }      => continue 'skip_dedup,
                                Instruction::Store { ptr, .. } => {
                                    if *ptr == loaded_ptr {
                                        continue 'skip_dedup;
                                    }

                                    if !safe {
                                        continue 'skip_dedup;
                                    }
                                }
                                _ => {},
                            }
                        }
                    }

                    did_something = true;

                    let value        = body[prev_index].created_value().unwrap();
                    let target_value = body[inst_id].created_value().unwrap();

                    body[inst_id] = Instruction::Alias {
                        dst: target_value,
                        value,
                    };
                } else {
                    dedup_list.insert(key, inst_id);
                }
            }
        }

        did_something
    }
}
