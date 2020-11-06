use crate::{FunctionData, Instruction};

pub struct BranchToSelectPass;

impl super::Pass for BranchToSelectPass {
    fn name(&self) -> &str {
        "branch to select"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        // Find branches which only purpose is to select value and change them to `select`
        // instruction. This can be only done if there are no volatile operations in
        // branch arms and memory accesses.
        //
        // entry:
        //   v2 = u32 4
        //   v4 = icmp eq u32 v0, v2
        //   bcond u1 v4, block_2, block_3
        // 
        // block_2:
        //   v10 = u32 555
        //   branch block_1
        // 
        // block_3:
        //   v11 = u32 823
        //   branch block_1
        // 
        // block_1:
        //   v15 = phi u32 [block_3: v11, block_2: v10]
        //   ret u32 v15
        //
        // Will get optimized to:
        // entry:
        //   v11 = u32 823
        //   v10 = u32 555
        //   v2 = u32 4
        //   v4 = icmp eq u32 v0, v2
        //   v15 = select u1 v4, u32 v10, v11
        //   ret u32 v15

        'main_loop: loop {
            // Recalculate data as we have altered the CFG.
            let labels        = function.reachable_labels();
            let flow_incoming = function.flow_graph_incoming();

            'next_label: for label in labels {
                let bcond = function.last_instruction(label);

                // Check if this can be entry in diamond pattern in CFG.
                if let Instruction::BranchCond { cond, on_true, on_false } = *bcond {
                    // Skip conditional branches with both labels equal and skip loops.
                    if on_true == on_false || on_true == label || on_false == label {
                        continue 'next_label;
                    }

                    // We cannot optimize this branch if `on_true` or `on_false` label is
                    // reachable from somewhere else then from `label`.
                    if flow_incoming[&on_true].len() != 1 || flow_incoming[&on_false].len() != 1 {
                        continue 'next_label;
                    }

                    // Get exit label if there is a common one. Otherwise we cannot optimize
                    // branch out so we continue.
                    let exit = match (function.last_instruction(on_true),
                                      function.last_instruction(on_false)) {
                        (Instruction::Branch { target: true_target  },
                         Instruction::Branch { target: false_target }) => {
                            if true_target == false_target {
                                *true_target
                            } else {
                                continue 'next_label;
                            }
                        }
                        _ => continue 'next_label,
                    };

                    // We cannot optimize this branch if `exit` can be reached from
                    // somewhere else then `on_true` or `on_false`.
                    if flow_incoming[&exit].len() != 2 {
                        continue 'next_label;
                    }

                    // Skip loops.
                    if exit == label || exit == on_true || exit == on_false {
                        continue 'next_label;
                    }

                    // We have now detected following pattern in the CFG:
                    //
                    //   A
                    //  / \
                    // B   C
                    //  \ /
                    //   D
                    //
                    // Where A is `label`, B is `on_true`, C is `on_false` and D is `exit`.
                    // If B and C don't contain non-reorderable instructions we can optimize
                    // the branch out.

                    let mut total_instructions = 0;

                    // Check both `on_true` and `on_false` blocks if they can be reordered
                    // and count total number of instructions.
                    for &checked_label in &[on_true, on_false] {
                        let body = &function.blocks[&checked_label];
                        let size = body.len();

                        // Ignore last instruction (branch) as it will be removed anyway.
                        for instruction in &body[..size - 1] {
                            if !instruction.can_be_reordered() {
                                continue 'next_label;
                            }
                        }

                        total_instructions += size - 1;
                    }

                    // Check if changing branch to select is worth it.
                    if total_instructions > 8 {
                        continue 'next_label;
                    }

                    // We can change branch to select. We will make A jump directly to D,
                    // copy everything except branches from B and C to D and change
                    // all PHIs to `select`s.

                    {
                        let parent_body = function.blocks.get_mut(&label).unwrap();
                        let body_size   = parent_body.len();

                        // Make `label` enter `exit` directly. This will unlink `on_true` and
                        // `on_false` from the CFG.
                        parent_body[body_size - 1] = Instruction::Branch {
                            target: exit,
                        };
                    }

                    // Move everything (except last branch)  from `on_true` and `on_false`
                    // to the beginning of `exit`. We may put things before PHIs but that
                    // doesn't matter as we will change PHIs to `select`s.
                    for &move_label in &[on_true, on_false] {
                        // Remove all body of this label as it's unlinked from CFG anyway.
                        let mut body = function.blocks.remove(&move_label).unwrap();

                        // Remove the last branch.
                        body.pop();

                        let exit_body = function.blocks.get_mut(&exit).unwrap();

                        // Move all instruction from this label to the beginning
                        // of `exit`.
                        for instruction in body.into_iter().rev() {
                            exit_body.insert(0, instruction);
                        }
                    }

                    let exit_body = function.blocks.get_mut(&exit).unwrap();

                    // Rewrite all PHIs in `exit` to `select`s.
                    for instruction in exit_body {
                        if let Instruction::Phi { dst, incoming } = instruction {
                            assert!(incoming.len() == 2, "Number of incoming values \
                                    doesn't match block predecessor count.");

                            let mut true_value  = None;
                            let mut false_value = None;

                            // Get value which is returned when we enter from true label and
                            // value which is returned when we enter from false label.
                            for &mut (label, value) in incoming {
                                if label == on_true {
                                    true_value = Some(value);
                                }

                                if label == on_false {
                                    false_value = Some(value);
                                }
                            }

                            let true_value  = true_value.unwrap();
                            let false_value = false_value.unwrap();

                            // Rewrite:
                            // v5 = phi [on_true: v4; on_false: v5]
                            // To:
                            // v5 = select cond, v4, v5
                            *instruction = Instruction::Select {
                                dst: *dst,
                                cond,
                                on_true:  true_value,
                                on_false: false_value,
                            };
                        }
                    }

                    did_something = true;

                    // As we have altered CFG we cannot continue this loop so
                    // we go directly to the main loop.
                    continue 'main_loop;
                }
            }

            // We haven't done anything this iteration so don't continue trying.
            break;
        }

        did_something
    }
}
