use crate::{FunctionData, Instruction, Map, Location};

pub struct SimplifyCFGPass;

impl super::Pass for SimplifyCFGPass {
    fn name(&self) -> &str {
        "CFG simplification"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::simplify_cfg()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        // Find blocks which are reachable only from one block by non-conditional branch
        // instruction and merge them with their parent.
        //
        // label_0:
        // branch label_1
        //
        // label_1:
        // ... body ...
        //
        // If label_1 is reachable only from label_0 this will get optimized to:
        // label_0:
        // ... body ...

        'merge_loop: loop {
            let incoming = function.flow_graph_incoming();

            for (&target, predecessors) in &incoming {
                // Don't do anything if it's entry block or if it has more than 1 entry point.
                if target == function.entry() || predecessors.len() != 1 {
                    continue;
                }

                // Get the parent of the current block and make sure it's not a loop.
                let dominator = *predecessors.iter().next().unwrap();
                if  dominator == target {
                    continue;
                }

                // We can only merge if current block is entered to by a non-conditional branch.
                if !matches!(function.last_instruction(dominator), Instruction::Branch { .. }) {
                    continue;
                }

                // Merged block shouldn't contain PHIs. If it does, another optimization pass
                // will remove it and we will be able to merge it later.
                if function.block_contains_phi(target) {
                    continue;
                }

                // All conditions met: we can merge target into dominator.

                // Successors' PHI nodes should now refer to `dominator` instead of `target`.
                for successor in function.targets(target) {
                    function.replace_phi_incoming(successor, target, dominator);
                }

                let mut target_insts = function.blocks.remove(&target).unwrap();
                let dominator_insts  = function.blocks.get_mut(&dominator).unwrap();

                // Remove branch to target in the dominator.
                dominator_insts.pop().unwrap();

                // Move all instructions from target to the end of the dominator.
                dominator_insts.append(&mut target_insts);

                did_something = true;

                // We have modified CFG, reenter the loop.
                continue 'merge_loop;
            }

            break;
        }

        // Flatten control flow. If some instruction branches to a block which only contains
        // non-conditional branch then we can get rid of that intermediate jump.
        //
        // label_0:
        //  bcond v0, label_1, label_2
        //
        // label_1:
        //  branch label_3
        //
        // label_2:
        //  ...
        //
        // label_3:
        //  ...
        //
        // Will get optimized to:
        // label_0:
        //  bcond v0, label_3, label_2
        //
        // ......

        let mut branch_labels = Map::default();

        let labels = function.reachable_labels();

        // Do the first pass to identify all blocks which contain a single instruction:
        // non-conditional branch.
        for &label in &labels {
            let body = &function.blocks[&label];

            let nops  = body.iter().filter(|instruction| instruction.is_nop()).count();
            let count = body.len() - nops;

            // Only 1 instruction is allowed.
            if count != 1 {
                continue;
            }

            if let Instruction::Branch { target } = body[body.len() - 1] {
                // If we have found an infinite loop then ignore it.
                if target != label {
                    // Insert a candidate block for flattening CFG.
                    branch_labels.insert(label, target);
                }
            }
        }

        // Do a second pass to actually flatten CFG.
        for &label in &labels {
            // Skip intermediate labels themselves.
            if branch_labels.get(&label).is_some() {
                continue;
            }

            let body    = &function.blocks[&label];
            let inst_id = body.len() - 1;

            let mut phi_updates = Vec::new();
            let mut replacement = None;

            // Find branch instructions which target intermediate blocks and change their
            // target to real destination.
            match body[inst_id] {
                Instruction::Branch { target } => {
                    if let Some(&new_target) = branch_labels.get(&target) {
                        // Check if PHI instruction depends on the control flow.
                        if !function.depends_on_predecessors(new_target, &[label, target]) {
                            replacement = Some(Instruction::Branch {
                                target: new_target,
                            });

                            phi_updates.push((target, new_target));
                        }
                    }
                }
                Instruction::BranchCond { cond, on_true, on_false } => {
                    let mut changed_true  = on_true;
                    let mut changed_false = on_false;

                    if let Some(&new_true) = branch_labels.get(&on_true) {
                        // Check if PHI instruction depends on the control flow.
                        if !function.depends_on_predecessors(new_true, &[label, on_true]) {
                            changed_true = new_true;
                            phi_updates.push((on_true, new_true));
                        }
                    }

                    // It's hard to reason about incoming PHI values because our changes are
                    // deferred. If we have changed `on_true` then we will try to optimize
                    // `on_false` next time.
                    if changed_true == on_true {
                        if let Some(&new_false) = branch_labels.get(&on_false) {
                            // Check if PHI instruction depends on the control flow.
                            if !function.depends_on_predecessors(new_false, &[label, on_false]) {
                                changed_false = new_false;
                                phi_updates.push((on_false, new_false));
                            }
                        }
                    }

                    // Create replacement instruction if we have changed anything.
                    if changed_true != on_true || changed_false != on_false {
                        replacement = Some(Instruction::BranchCond {
                            cond,
                            on_true:  changed_true,
                            on_false: changed_false,
                        });
                    }
                }
                _ => {}
            }

            if let Some(replacement) = replacement {
                // Fixup PHI incoming values.
                for (before, after) in phi_updates {
                    function.replace_phi_incoming(after, before, label);
                }

                // Replace instruction with our new one.
                *function.instruction_mut(Location::new(label, inst_id)) = replacement;

                did_something = true;
            }
        }

        did_something
    }
}
