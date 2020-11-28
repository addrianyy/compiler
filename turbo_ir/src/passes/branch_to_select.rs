use crate::{FunctionData, Instruction, Label, Value};

struct SkewedCFGInfo {
    skew:       Label,
    exit:       Label,
    true_pred:  Label,
    false_pred: Label,
}

fn make_unconditional_branch(function: &mut FunctionData, from: Label, to: Label) {
    let body      = function.blocks.get_mut(&from).unwrap();
    let body_size = body.len();

    body[body_size - 1] = Instruction::Branch {
        target: to,
    };
}

fn move_instructions(function: &mut FunctionData, treshold: usize,
                     from: &[Label], to: Label) -> bool {
    let mut total_instructions = 0;

    for &label in from {
        let body = &function.blocks[&label];
        let size = body.len();

        // Ignore last instruction (branch) as it will be removed anyway.
        for instruction in &body[..size - 1] {
            if !instruction.can_be_reordered() {
                return false;
            }

            if !instruction.is_nop() {
                total_instructions += 1;
            }
        }
    }

    if total_instructions > treshold {
        return false;
    }

    for &from in from {
        // Remove all body of this label as it's unlinked from CFG anyway.
        let mut body = function.blocks.remove(&from).unwrap();

        // Remove the last branch.
        body.pop();

        let to_body = function.blocks.get_mut(&to).unwrap();

        // Move all instruction from this label to the beginning
        // of `exit`.
        for instruction in body.into_iter().rev() {
            to_body.insert(0, instruction);
        }
    }

    true
}

fn rewrite_phis_to_selects(function: &mut FunctionData, condition: Value, label: Label,
                           true_label: Label, false_label: Label) {
    let body = function.blocks.get_mut(&label).unwrap();

    for instruction in body {
        if let Instruction::Phi { dst, incoming } = instruction {
            assert_eq!(incoming.len(), 2, "Number of incoming values \
                       doesn't match block predecessor count.");

            let mut true_value  = None;
            let mut false_value = None;

            // Get value which is returned when we enter from true label and
            // value which is returned when we enter from false label.
            for &mut (label, value) in incoming {
                if label == true_label {
                    true_value = Some(value);
                }

                if label == false_label {
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
                dst:      *dst,
                cond:     condition,
                on_true:  true_value,
                on_false: false_value,
            };
        }
    }
}

pub struct BranchToSelectPass;

impl super::Pass for BranchToSelectPass {
    fn name(&self) -> &str {
        "branch to select"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::branch_to_select()
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

        const COPY_TRESHOLD: usize = 8;

        'main_loop: loop {
            // Recalculate data as we have altered the CFG.
            let labels        = function.reachable_labels();
            let flow_incoming = function.flow_graph_incoming();

            'next_label: for label in labels {
                let bcond = function.last_instruction(label);

                if let Instruction::BranchCond { cond, on_true, on_false } = *bcond {
                    // Skip conditional branches with both labels equal and skip loops.
                    if on_true == on_false || on_true == label || on_false == label {
                        continue 'next_label;
                    }

                    // Get unconditional branch target for `on_true`.
                    let mut true_exit = None;
                    if let Instruction::Branch { target } = function.last_instruction(on_true) {
                        true_exit = Some(*target);
                    }

                    // Get unconditional branch target for `on_false`.
                    let mut false_exit = None;
                    if let Instruction::Branch { target } = function.last_instruction(on_false) {
                        false_exit = Some(*target);
                    }

                    let mut skew_info = None;

                    //   A
                    //  / \
                    // B   |
                    //  \ /
                    //   D

                    // Try to detect both left-skew and right-skew in the CFG.
                    if false_exit == Some(on_true) {
                        // B - `on_false`.
                        // D - `on_true`.
                        skew_info = Some(SkewedCFGInfo {
                            skew:       on_false,
                            exit:       on_true,
                            true_pred:  label,
                            false_pred: on_false,
                        });
                    } else if true_exit == Some(on_false) {
                        // B - `on_true`.
                        // D - `on_false`.
                        skew_info = Some(SkewedCFGInfo {
                            skew:       on_true,
                            exit:       on_false,
                            true_pred:  on_true,
                            false_pred: label,
                        });
                    }

                    if let Some(skew_info) = skew_info {
                        let SkewedCFGInfo {
                            skew,
                            exit,
                            true_pred,
                            false_pred,
                        } = skew_info;

                        // Skew should be only reachable from `label` and `exit` should be
                        // reachable from `label` and `skew`.
                        if flow_incoming[&skew].len() != 1 ||
                           flow_incoming[&exit].len() != 2 {
                            continue 'next_label;
                        }

                        // Avoid loops.
                        if skew == exit || skew == label || exit == label {
                            continue 'next_label;
                        }

                        // Try to copy all instructions from `skew` to `exit`.
                        if !move_instructions(function, COPY_TRESHOLD, &[skew], exit) {
                            continue 'next_label;
                        }

                        // Make `label` jump directly to `exit`. This will unlink `skew` from
                        // CFG.
                        make_unconditional_branch(function, label, exit);

                        rewrite_phis_to_selects(function, cond, exit, true_pred, false_pred);

                        // As we have altered CFG we cannot continue this loop so
                        // we go directly to the main loop.
                        continue 'main_loop;
                    }

                    // To continue, both `on_true` and `on_false` must end with unconditional
                    // branch.
                    if true_exit.is_none() || false_exit.is_none() {
                        continue 'next_label;
                    }

                    let true_exit  = true_exit.unwrap();
                    let false_exit = false_exit.unwrap();

                    // We cannot optimize this branch if `on_true` or `on_false` label is
                    // reachable from somewhere else then from `label`.
                    if flow_incoming[&on_true].len() != 1 || flow_incoming[&on_false].len() != 1 {
                        continue 'next_label;
                    }

                    // Get exit label if there is a common one. Otherwise we cannot optimize
                    // branch out so we continue.
                    let exit = if true_exit == false_exit {
                        true_exit
                    } else {
                        continue 'next_label;
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

                    // Try to copy everything from `on_true` and `on_false` to `exit`.
                    if !move_instructions(function, COPY_TRESHOLD, &[on_true, on_false], exit) {
                        continue 'next_label;
                    }

                    // Make `label` enter `exit` directly. This will unlink `on_true` and
                    // `on_false` from the CFG.
                    make_unconditional_branch(function, label, exit);

                    // Rewrite all PHIs in `exit` to `select`s.
                    rewrite_phis_to_selects(function, cond, exit, on_true, on_false);

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
