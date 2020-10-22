use super::{FunctionData, Instruction, Pass};
use super::super::IntPredicate;

pub struct SimplifyComparesPass;

impl Pass for SimplifyComparesPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let creators = function.value_creators();
        let consts   = function.constant_values();

        let mut replacements = Vec::new();

        // Try to optimize icmp, select, icmp to single icmp.
        //
        // %2 = u32 0
        // %4 = icmp eq u32 %0, %2
        // %5 = u8 0
        // %6 = u8 1
        // %7 = select u1 %4, u8 %6, %5
        // %9 = icmp ne u8 %7, %5
        // bcond u1 %9, label_2, label_3
        //
        // %2 = u32 0
        // %4 = icmp eq u32 %0, %2
        // bcond u1 %4, label_2, label_3

        function.for_each_instruction(|location, instruction| {
            if let Instruction::IntCompare { dst, a, pred, b } = instruction {
                let mut a = a;
                let mut b = b;

                for _ in 0..2 {
                    let aa = creators.get(&a).map(|location| function.instruction(*location));
                    let bb = consts.get(&b);

                    if let (Some(Instruction::Select { cond, on_true, on_false, .. }),
                            Some((_, value))) = (aa, bb) {
                        let new_on_true;
                        let new_on_false;

                        if let (Some((_, on_true)), Some((_, on_false))) = (consts.get(on_true),
                                                                            consts.get(on_false)) {
                            new_on_true  = on_true;
                            new_on_false = on_false;
                        } else {
                            return;
                        }

                        let on_true  = new_on_true;
                        let on_false = new_on_false;

                        if on_true == on_false {
                            return;
                        }

                        let result = match *pred {
                            IntPredicate::Equal => {
                                if on_true == value {
                                    Some(false)
                                } else if on_false == value {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            IntPredicate::NotEqual => {
                                if on_false == value {
                                    Some(false)
                                } else if on_true == value {
                                    Some(true)
                                } else {
                                    None
                                }
                            }
                            _ => return,
                        };

                        let mut new_instruction = None;

                        if let Some(inverted) = result {
                            if !inverted {
                                new_instruction = Some(Instruction::Alias { 
                                    dst:   *dst,
                                    value: *cond,
                                });
                            } else {
                                let parent_compare = creators.get(&cond).map(|location| {
                                    function.instruction(*location)
                                });

                                if let Some(&Instruction::IntCompare { a, pred, b, .. })
                                    = parent_compare
                                {
                                    let mut a = a;
                                    let mut b = b;

                                    let (new_pred, needs_swap) = match pred {
                                        IntPredicate::Equal    => (IntPredicate::NotEqual, false),
                                        IntPredicate::NotEqual => (IntPredicate::Equal,    false),
                                        _                      => (pred, true),
                                    };

                                    if needs_swap {
                                        std::mem::swap(&mut a, &mut b);
                                    }

                                    new_instruction = Some(Instruction::IntCompare {
                                        dst: *dst,
                                        a,
                                        pred: new_pred,
                                        b,
                                    });
                                }
                            }
                        }

                        if let Some(new_instruction) = new_instruction {
                            replacements.push((location, new_instruction));
                        }
                    } else {
                        std::mem::swap(&mut a, &mut b);

                        continue;
                    }

                    break;
                }
            }
        });

        let did_something = !replacements.is_empty();

        for (location, replacement) in replacements {
            *function.instruction_mut(location) = replacement;
        }

        did_something
    }
}
