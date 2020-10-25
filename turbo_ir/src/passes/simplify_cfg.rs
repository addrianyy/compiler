use crate::{FunctionData, Instruction, Label, Map};

pub struct SimplifyCFGPass;

impl super::Pass for SimplifyCFGPass {
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
        //
        // label_0:
        // ... body ...

        'merge_loop: loop {
            let incoming = function.flow_graph_incoming();

            for (&target, predecessors) in &incoming {
                // Don't do anything if it's entry block or if it has more then 1 entry point.
                if target == Label(0) || predecessors.len() != 1 {
                    continue;
                }

                // Get the parent of current block and make sure it's actually predecessor.
                let dominator = *predecessors.iter().next().unwrap();
                if  dominator == target {
                    continue;
                }

                // We can only merge if current block is entered by a non-conditional branch.
                if !matches!(function.last_instruction(dominator), Instruction::Branch { .. }) {
                    continue;
                }

                // All conditions met: we can merge target into dominator.

                let mut target_insts = function.blocks.remove(&target).unwrap();
                let dominator_insts  = function.blocks.get_mut(&dominator).unwrap();

                // Remove branch to target in dominator.
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
        //  bcond %0, label_1, label_2
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
        //  bcond %0, label_3, label_2
        // 
        // ......

        let mut branch_labels = Map::default();

        let labels = function.reachable_labels();

        // Do the first pass to identify all blocks which contain a single instruction:
        // non-conditional branch.
        for &label in &labels {
            let body = &function.blocks[&label];

            // Only 1 instruction is allowed.
            if body.len() != 1 {
                continue;
            }

            if let Instruction::Branch { target } = body[0] {
                // If we have found an infinite loop then ignore it.
                if target != label {
                    // Insert a candidate block for flattening CFG.
                    branch_labels.insert(label, target);
                }
            }
        }

        // Do a second pass to actually flatten CFG.
        function.for_each_instruction_mut(|_, instruction| {
            // Find branch instructions which target intermediate blocks and change their
            // target to true destination.

            match instruction {
                Instruction::Branch { target } => {
                    if let Some(&new_target) = branch_labels.get(&target) {
                        *target       = new_target;
                        did_something = true;
                    }
                }
                Instruction::BranchCond { on_true, on_false, .. } => {
                    if let Some(&new_true) = branch_labels.get(&on_true) {
                        *on_true      = new_true;
                        did_something = true;
                    }

                    if let Some(&new_false) = branch_labels.get(&on_false) {
                        *on_false     = new_false;
                        did_something = true;
                    }
                }
                _ => {}
            }
        });

        did_something
    }
}
