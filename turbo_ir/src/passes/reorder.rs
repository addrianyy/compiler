use crate::{BinaryOp, FunctionData, Instruction, Map};

pub struct ReorderPass;

impl super::Pass for ReorderPass {
    fn name(&self) -> &str {
        "reordering"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::reorder()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        let mut compares = Map::default();
        let mut geps     = Map::default();
        let mut divmods  = Map::default();

        // Try to reorder instructions to create patterns which can be matched by the backend
        // to create more efficient machine code.
        //
        // For now this optimization pass will only try to move cmps just above select/bcond
        // instructions.

        for label in function.reachable_labels() {
            compares.clear();
            geps.clear();
            divmods.clear();

            let mut skip_next = false;

            let body = function.blocks.get_mut(&label).unwrap();

            'next_instruction: for inst_id in 0.. {
                // Because size changes dynamically we need to check it manually.
                if inst_id >= body.len() {
                    break;
                }

                // If previous iteration inserted instruction this iteration is at position
                // of already visited instruction. Skip it.
                if skip_next {
                    skip_next = false;
                    continue;
                }

                let mut other_instruction = None;

                match &body[inst_id] {
                    Instruction::IntCompare { dst, .. } => {
                        // Record information about instruction which can be a
                        // candidate for reordering.
                        assert!(compares.insert(*dst, inst_id).is_none(),
                                "Compares create multiple same values.");
                    }
                    Instruction::GetElementPtr { dst, .. } => {
                        // Record information about instruction which can be a
                        // candidate for reordering.
                        assert!(geps.insert(*dst, inst_id).is_none(),
                                "GEPs create multiple same values.");
                    }
                    Instruction::ArithmeticBinary { a, op, b, .. } => {
                        if matches!(op, BinaryOp::ModU | BinaryOp::DivU |
                                        BinaryOp::ModS | BinaryOp::DivS) {
                            let a  = *a;
                            let b  = *b;
                            let op = *op;

                            let corresponding = crate::analysis::corresponding_divmod(op);

                            if let Some(&other_id) = divmods.get(&(a, corresponding, b)) {
                                divmods.remove(&(a, corresponding, b));
                                divmods.remove(&(a, op,            b));

                                let inbetween = inst_id - other_id - 1;
                                if  inbetween == 0 {
                                    continue 'next_instruction;
                                }

                                // Remove this instruction from current position.
                                let instruction = std::mem::replace(&mut body[inst_id],
                                                                    Instruction::Nop);

                                // Move this instruction just above corresponding `div`/`mod`.
                                body.insert(other_id, instruction);

                                // We have moved down all instructions with index >= `other_id`.
                                // Adjust the maps.
                                macro_rules! adjust {
                                    ($map: expr) => {
                                        for location in $map.values_mut() {
                                            if *location >= other_id { *location += 1; }
                                        }
                                    }
                                }

                                adjust!(compares);
                                adjust!(geps);
                                adjust!(divmods);

                                // Next index will be this instruction so we need to skip it.
                                skip_next     = true;
                                did_something = true;
                            } else {
                                divmods.insert((a, op, b), inst_id);
                            }
                        }
                    }
                    Instruction::Select     { cond, .. } |
                    Instruction::BranchCond { cond, .. } => {
                        // We found `select`/`bcond` and we want to move corresponding `cmp`
                        // just above it.
                        other_instruction = compares.get(cond).map(|location| (*location, *cond));
                    }
                    Instruction::Load  { ptr, .. } |
                    Instruction::Store { ptr, .. } => {
                        // We found `load`/`store` and we want to move corresponding `gep`
                        // just above it.
                        other_instruction = geps.get(ptr).map(|location| (*location, *ptr));
                    }
                    _ => {}
                }

                if let Some((other_id, other_value)) = other_instruction {
                    // Check if other instruction is actually just above us. In this case
                    // we have nothing to do.
                    let inbetween = inst_id - other_id - 1;
                    if  inbetween == 0 {
                        continue 'next_instruction;
                    }

                    // We want to move other instruction down. We need to make sure that
                    // no instruction so far read its output value. If that's the
                    // case, moving other instruction would violate SSA properites.
                    for instruction in &body[other_id + 1..inst_id] {
                        for value in instruction.read_values() {
                            if value == other_value {
                                continue 'next_instruction;
                            }
                        }
                    }

                    // We are able to move other instruction.

                    // This other instruction is non-movable from now.
                    compares.remove(&other_value);
                    geps.remove(&other_value);

                    // Move other instruction instruction down so it's just above us.
                    // We are only updating indices under us.
                    let instruction = std::mem::replace(&mut body[other_id],
                                                        Instruction::Nop);
                    body.insert(inst_id, instruction);

                    // Next index will be this instruction so we need to skip it.
                    skip_next     = true;
                    did_something = true;
                }
            }
        }

        did_something
    }
}
