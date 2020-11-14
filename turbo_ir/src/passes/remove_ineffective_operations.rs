use std::cmp::Ordering;
use crate::{FunctionData, Instruction, Cast, Value, ConstType, IntPredicate, Type,
            BinaryOp, UnaryOp};

pub struct RemoveIneffectiveOperationsPass;

impl super::Pass for RemoveIneffectiveOperationsPass {
    fn name(&self) -> &str {
        "ineffective operation elimination"
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let labels   = function.reachable_labels();
        let consts   = function.constant_values_with_labels(&labels);
        let creators = function.value_creators_with_labels(&labels);

        // Simplify operations with known outputs.
        //
        // v2 = u32 0
        // v3 = add u32 v1, v2
        //
        // Will be optimized to:
        // v3 = alias u32 v1
        //
        // RemoveAliasesPass will take care of that and further transform the code.

        let values_equal = |a: Value, b: Value| {
            // If these values have the same ID they are always equal.
            if a == b {
                return true;
            }

            // We can also check for their equality if they are both known constants.
            let a = consts.get(&a);
            let b = consts.get(&b);

            a.is_some() && a == b
        };

        let mut replacements = Vec::new();

        function.for_each_instruction_with_labels(&labels, |location, instruction| {
            let mut replacement = None;

            // Go through every instruction, match patterns with known results
            // to simplify the instruction.
            match *instruction {
                Instruction::GetElementPtr { dst, source, index } => {
                    let creator = creators.get(&index).map(|location| {
                        function.instruction(*location)
                    });

                    if let Some(Instruction::Cast { cast: Cast::SignExtend, value, .. })
                        = creator
                    {
                        // GEP sign extends index internally so source the index
                        // from non-sign-extended value. This gives DCE an opportunity
                        // to eliminate unneeded `sext` instruction.
                        replacement = Some(Instruction::GetElementPtr {
                            dst,
                            source,
                            index: *value,
                        });
                    } else if let Some((_, 0)) = consts.get(&index) {
                        // GEP with index of 0 always returns input value.
                        replacement = Some(Instruction::Alias {
                            dst,
                            value: source,
                        });
                    }
                }
                Instruction::BranchCond { on_true, on_false, .. } => {
                    // If both targets of the `bcond` instruction are the same, we can
                    // convert it to non-conditional branch. As we don't really modify
                    // control flow we don't need to update PHIs.
                    if on_true == on_false {
                        replacement = Some(Instruction::Branch {
                            target: on_true,
                        });
                    }
                }
                Instruction::Select { dst, on_true, on_false, .. } => {
                    // If both values of the select instruction are the same we can
                    // alias output value to one of the values.
                    if values_equal(on_true, on_false) {
                        replacement = Some(Instruction::Alias {
                            dst,
                            value: on_true,
                        });
                    }
                }
                Instruction::IntCompare { dst, a, pred, b } => {
                    // If both operands to int comapare instruction are the same we can
                    // calculate the result at compile time.
                    if values_equal(a, b) {
                        let result = match pred {
                            IntPredicate::Equal    => true,
                            IntPredicate::NotEqual => false,
                            IntPredicate::GtS      => false,
                            IntPredicate::GteS     => true,
                            IntPredicate::GtU      => false,
                            IntPredicate::GteU     => true,
                        };

                        replacement = Some(Instruction::Const {
                            dst,
                            imm: result as u64,
                            ty:  Type::U1,
                        });
                    }
                }
                Instruction::ArithmeticUnary { dst, op, value } => {
                    let creator = creators.get(&value).map(|location| {
                        function.instruction(*location)
                    });

                    // Check if input of unary instruction was created by another unary
                    // instruction.
                    if let Some(Instruction::ArithmeticUnary { op: p_op, value: p_value, .. })
                        = creator
                    {
                        // 2 the same unary operations cancel out.
                        // --x == x
                        // !!x == x
                        if *p_op == op {
                            replacement = Some(Instruction::Alias {
                                dst,
                                value: *p_value,
                            });
                        }
                    }
                }
                Instruction::Cast { dst, ty, value, cast } => {
                    let creator = creators.get(&value).map(|location| {
                        function.instruction(*location)
                    });

                    // Check if input of cast instruction was created by another cast
                    // instruction.
                    if let Some(Instruction::Cast { cast: p_cast, value: p_value, .. }) = creator {
                        // Two casts of the same type can be optimized out to only one.
                        // For example `zext` from u16 to u32 and `zext` from u32 to u64
                        // can be converted to `zext` from u16 to u64.
                        if *p_cast == cast {
                            replacement = Some(Instruction::Cast {
                                dst,
                                cast,
                                value: *p_value,
                                ty,
                            });
                        } else if cast == Cast::Truncate && (*p_cast == Cast::ZeroExtend ||
                                                             *p_cast == Cast::SignExtend) {
                            // v1 = zext u16 v0 to u64
                            // v2 = trunc u64 v1 to u32
                            //
                            // to:
                            // v1 = zext u16 v0 to u32

                            let start_ty = function.value_type(*p_value);

                            // Pick correct replacement.
                            match ty.size().cmp(&start_ty.size()) {
                                Ordering::Greater => {
                                    replacement = Some(Instruction::Cast {
                                        dst,
                                        cast:  *p_cast,
                                        value: *p_value,
                                        ty,
                                    });
                                }
                                Ordering::Less => {
                                    replacement = Some(Instruction::Cast {
                                        dst,
                                        cast:  Cast::Truncate,
                                        value: *p_value,
                                        ty,
                                    });
                                }
                                Ordering::Equal => {
                                    replacement = Some(Instruction::Alias {
                                        dst,
                                        value: *p_value,
                                    });
                                }
                            }
                        }
                    }
                }
                Instruction::ArithmeticBinary { dst, a, op, b } => {
                    // Try to extract constants from binary instruction operands.
                    let ca = consts.get(&a).copied();
                    let cb = consts.get(&b).copied();

                    // If any operand is constant then get its type.
                    let ty       = function.value_type(dst);
                    let const_ty = match (ca, cb) {
                        (Some((ty, _)), _) => Some(ty),
                        (_, Some((ty, _))) => Some(ty),
                        _                  => None,
                    };

                    // Create a bit pattern of only ones for a given type.
                    let ones = const_ty.map(|ty| {
                        match ConstType::new(ty) {
                            ConstType::U1  => panic!("U1 in arithmetic instruction."),
                            ConstType::U8  => u8::MAX  as u64,
                            ConstType::U16 => u16::MAX as u64,
                            ConstType::U32 => u32::MAX as u64,
                            ConstType::U64 => u64::MAX as u64,
                        }
                    }).unwrap_or(u64::MAX);

                    // Strip the type information from the constants. We don't need it anymore.
                    let ca = ca.map(|(_, value)| value);
                    let cb = cb.map(|(_, value)| value);

                    macro_rules! alias {
                        ($value: expr) => {
                            Some(Instruction::Alias {
                                dst,
                                value: $value,
                            })
                        }
                    }

                    macro_rules! constant {
                        ($value: expr) => {
                            Some(Instruction::Const  {
                                dst,
                                imm: $value as u64,
                                ty,
                            });
                        }
                    }

                    // Match various binary operation patterns to simplify an instruction.
                    match op {
                        BinaryOp::Add => {
                            if ca == Some(0) {
                                replacement = alias!(b);
                            } else if cb == Some(0) {
                                replacement = alias!(a);
                            }
                        }
                        BinaryOp::Sub => {
                            if a == b {
                                replacement = constant!(0);
                            } else if cb == Some(0) {
                                replacement = alias!(a);
                            } else if ca == Some(0) {
                                let value = b;

                                // 0 - a = -a
                                replacement = Some(Instruction::ArithmeticUnary {
                                    dst,
                                    value,
                                    op: UnaryOp::Neg,
                                });
                            }
                        }
                        BinaryOp::And => {
                            if ca == Some(0) || cb == Some(0) {
                                replacement = constant!(0);
                            } else if cb == Some(ones) {
                                replacement = alias!(a);
                            } else if ca == Some(ones) {
                                replacement = alias!(b);
                            } else if a == b {
                                replacement = alias!(a);
                            }
                        }
                        BinaryOp::Or => {
                            if ca == Some(ones) || cb == Some(ones) {
                                replacement = constant!(ones);
                            } else if cb == Some(0) {
                                replacement = alias!(a);
                            } else if ca == Some(0) {
                                replacement = alias!(b);
                            } else if a == b {
                                replacement = alias!(a);
                            }
                        }
                        BinaryOp::Xor => {
                            if a == b {
                                replacement = constant!(0);
                            } else if cb == Some(0) {
                                replacement = alias!(a);
                            } else if ca == Some(0) {
                                replacement = alias!(b);
                            } else if ca == Some(ones) {
                                let value = b;

                                // a ^ ffffff... = !a
                                replacement = Some(Instruction::ArithmeticUnary {
                                    dst,
                                    value,
                                    op: UnaryOp::Not,
                                });
                            }  else if cb == Some(ones) {
                                let value = a;

                                // a ^ ffffff... = !a
                                replacement = Some(Instruction::ArithmeticUnary {
                                    dst,
                                    value,
                                    op: UnaryOp::Not,
                                });
                            }
                        }
                        BinaryOp::Mul => {
                            if ca == Some(0) || cb == Some(0) {
                                replacement = constant!(0);
                            } else if cb == Some(1) {
                                replacement = alias!(a);
                            } else if ca == Some(1) {
                                replacement = alias!(b);
                            } else if ca == Some(2) {
                                let value = b;

                                // a * 2 == a + a
                                replacement = Some(Instruction::ArithmeticBinary {
                                    dst,
                                    a:  value,
                                    op: BinaryOp::Add,
                                    b:  value,
                                });
                            } else if cb == Some(2) {
                                let value = a;

                                // a * 2 == a + a
                                replacement = Some(Instruction::ArithmeticBinary {
                                    dst,
                                    a:  value,
                                    op: BinaryOp::Add,
                                    b:  value,
                                });
                            }
                        }
                        BinaryOp::DivS | BinaryOp::DivU => {
                            if ca == Some(0) {
                                replacement = constant!(0);
                            } else if cb == Some(1) {
                                replacement = alias!(a);
                            } else if a == b {
                                replacement = constant!(1);
                            }
                        }
                        BinaryOp::ModS | BinaryOp::ModU => {
                            if ca == Some(0) || cb == Some(1) || a == b {
                                replacement = constant!(0);
                            }
                        }
                        BinaryOp::Shl | BinaryOp::Shr | BinaryOp::Sar => {
                            if ca == Some(0) {
                                replacement = constant!(0);
                            } else if cb == Some(0) {
                                replacement = alias!(a);
                            }
                        }
                    }
                }
                Instruction::Phi { dst, ref incoming } => {
                    let mut incoming_value = incoming[0].1;
                    let mut incoming_const = consts.get(&incoming_value)
                        .copied().map(|x| x.1);

                    let mut valid = true;

                    // If all incoming values are the same we can replace `phi` with `alias`.
                    // This will also handle PHIs with one incoming value.
                    for (_label, value) in &incoming[1..] {
                        let other_const = consts.get(&value).copied().map(|x| x.1);
                        let const_match = incoming_const.is_some() &&
                            incoming_const == other_const;

                        if *value != incoming_value && !const_match  {
                            valid = false;
                            break;
                        }
                    }

                    if !valid && incoming.len() == 2 {
                        // Reduce self-referential PHIs.
                        if incoming[0].1 == dst {
                            incoming_value = incoming[1].1;
                            valid          = true;
                            incoming_const = None;
                        } else if incoming[1].1 == dst {
                            incoming_value = incoming[0].1;
                            valid          = true;
                            incoming_const = None;
                        }
                    }

                    // Replace single incoming value with just `alias`.
                    if valid {
                        replacement = Some(match incoming_const {
                            Some(constant) => {
                                Instruction::Const {
                                    dst,
                                    imm: constant,
                                    ty:  function.value_type(dst),
                                }
                            }
                            None => {
                                Instruction::Alias {
                                    dst,
                                    value: incoming_value,
                                }
                            }
                        });
                    }
                }
                _ => {}
            }

            if let Some(replacement) = replacement {
                replacements.push((location, replacement));
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
