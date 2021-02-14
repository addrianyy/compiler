use crate::{FunctionData, Instruction, IntPredicate};

pub struct SimplifyComparesPass;

impl super::Pass for SimplifyComparesPass {
    fn name(&self) -> &str {
        "compare simplification"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::simplify_compares()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let labels   = function.reachable_labels();
        let creators = function.value_creators_with_labels(&labels);
        let consts   = function.constant_values_with_labels(&labels);

        let mut replacements = Vec::new();

        // Code generators will often emit sequence of `cmp`, `select`, `cmp`.
        // This pass will try to detect it and optimize it to a single `cmp` if possible.
        //
        // v2 = u32 0
        // v4 = cmp eq u32 v0, v2
        // v5 = u8 0
        // v6 = u8 1
        // v7 = select u1 v4, u8 v6, v5
        // v9 = cmp ne u8 v7, v5
        // bcond u1 v9, label_2, label_3
        //
        // Gets optimized to:
        // v2 = u32 0
        // v4 = cmp eq u32 v0, v2
        // bcond u1 v4, label_2, label_3

        function.for_each_instruction_with_labels(&labels, |location, instruction| {
            // Try to match on SECOND `cmp` of `cmp`, `select`, `cmp` sequence.
            if let Instruction::IntCompare { dst, a, pred, b } = instruction {
                let mut a = a;
                let mut b = b;

                // Try this optimization two times. First time with operands (A, B),
                // second time with operands (B, A). Because we only do this on EQ and NE,
                // order doesn't matter.

                for _ in 0..2 {
                    // Left side of `cmp` must be a value created by `select` instruction.
                    // Right side of `cmp` must be a known constant.
                    let aa = creators.get(&a).map(|location| function.instruction(*location));
                    let bb = consts.get(&b);

                    // Check if requirements above are actually met.
                    if let (Some(Instruction::Select { cond, on_true, on_false, .. }),
                            Some((_, value))) = (aa, bb) {
                        let new_on_true;
                        let new_on_false;

                        // `select` operands must be known constants too.
                        if let (Some((_, on_true)), Some((_, on_false))) = (consts.get(on_true),
                                                                            consts.get(on_false)) {
                            new_on_true  = on_true;
                            new_on_false = on_false;
                        } else {
                            return;
                        }

                        let on_true  = new_on_true;
                        let on_false = new_on_false;

                        // If select true value is the same as false value then `select`
                        // instruction can be optimized out. Other optimization pass
                        // will take care of it.
                        if on_true == on_false {
                            return;
                        }

                        // Get the corelation betwen first `cmp` and second `cmp`.
                        // There can be 3 cases:
                        // 1. second `cmp` result ==  first `cmp` result.
                        // 2. second `cmp` result == !first `cmp` result.
                        // 3. `cmps` are not corelated (in this case we exit).
                        // For simplicity we only handle EQ and NE predicates in the second `cmp`.

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

                        // We know that both `cmps` are corelated with each other.

                        let mut new_instruction = None;

                        if let Some(inverted) = result {
                            if !inverted {
                                // If second `cmp` result == first `cmp` result than
                                // we will just alias second `cmp` result to first one's result.

                                new_instruction = Some(Instruction::Alias {
                                    dst:   *dst,
                                    value: *cond,
                                });
                            } else {
                                // If `cmp` results are inverted than we want to replace second
                                // `cmp` with inverted copy of the first one.
                                let parent_compare = creators.get(&cond).map(|location| {
                                    function.instruction(*location)
                                });

                                if let Some(&Instruction::IntCompare { a, pred, b, .. })
                                    = parent_compare
                                {
                                    // Change this instruction to inverted version of the
                                    // first `cmp`.
                                    new_instruction = Some(Instruction::IntCompare {
                                        dst: *dst,
                                        a,
                                        pred: pred.invert(),
                                        b,
                                    });
                                }
                            }
                        }

                        if let Some(new_instruction) = new_instruction {
                            replacements.push((location, new_instruction));
                        }
                    } else {
                        // First try failed, swap operands and try again.
                        std::mem::swap(&mut a, &mut b);

                        continue;
                    }

                    // Optimization succeded.
                    break;
                }
            }
        });

        let did_something = !replacements.is_empty();

        // Actually perform the replacements.
        for (location, replacement) in replacements {
            *function.instruction_mut(location) = replacement;
        }

        did_something
    }
}
