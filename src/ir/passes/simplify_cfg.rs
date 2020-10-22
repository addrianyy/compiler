use super::{FunctionData, Instruction, Pass};
use super::super::Label;

pub struct SimplifyCFGPass;

impl Pass for SimplifyCFGPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        'merge_loop: loop {
            let incoming = function.flow_graph_incoming();

            for (&target, predecessors) in &incoming {
                if target == Label(0) || predecessors.len() != 1 {
                    continue;
                }

                let dominator = *predecessors.iter().next().unwrap();
                if  dominator == target {
                    continue;
                }

                if !matches!(function.last_instruction(dominator), Instruction::Branch { .. }) {
                    continue;
                }

                let mut target_insts = function.blocks.remove(&target).unwrap();
                let dominator_insts  = function.blocks.get_mut(&dominator).unwrap();

                dominator_insts.pop().unwrap();
                dominator_insts.append(&mut target_insts);

                did_something = true;

                continue 'merge_loop;
            }

            break;
        }

        did_something
    }
}
