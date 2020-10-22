use std::collections::HashMap;

use super::{FunctionData, Instruction, Pass};
use super::super::{Cast, Value, ConstType, BinaryOp};

pub struct RemoveIneffectiveOperationsPass;

impl Pass for RemoveIneffectiveOperationsPass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut sign_extensions = HashMap::new();

        let consts   = function.constant_values();
        let creators = function.value_creators();

        function.for_each_instruction(|_, instruction| {
            if let Instruction::Cast { dst, cast: Cast::SignExtend, value, .. } = instruction {
                sign_extensions.insert(*dst, *value);
            }
        });

        let values_equal = |a: Value, b: Value| {
            if a == b {
                return true;
            }

            let a = consts.get(&a);
            let b = consts.get(&b);

            a.is_some() && a == b
        };

        let mut replacements = Vec::new();

        function.for_each_instruction(|location, instruction| {
            let mut replacement = None;

            match *instruction {
                Instruction::GetElementPtr { dst, source, index } => {
                    if let Some(&index) = sign_extensions.get(&index) {
                        replacement = Some(Instruction::GetElementPtr {
                            dst,
                            source,
                            index,
                        });
                    } else if let Some((_, 0)) = consts.get(&index) {
                        replacement = Some(Instruction::Alias {
                            dst,
                            value: source,
                        });
                    }
                }
                Instruction::BranchCond { on_true, on_false, .. } => {
                    if on_true == on_false {
                        replacement = Some(Instruction::Branch {
                            target: on_true,
                        });
                    }
                }
                Instruction::Select { dst, on_true, on_false, .. } => {
                    if values_equal(on_true, on_false) {
                        replacement = Some(Instruction::Alias {
                            dst,
                            value: on_true,
                        });
                    }
                }
                Instruction::ArithmeticUnary { dst, op, value } => {
                    let creator = creators.get(&value).map(|location| {
                        function.instruction(*location)
                    });

                    if let Some(Instruction::ArithmeticUnary { op: p_op, value: p_value, .. })
                        = creator
                    {
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

                    if let Some(Instruction::Cast { cast: p_cast, value: p_value, .. }) = creator {
                        if *p_cast == cast {
                            replacement = Some(Instruction::Cast {
                                dst,
                                cast,
                                value: *p_value,
                                ty,
                            });
                        }
                    }
                }
                Instruction::ArithmeticBinary { dst, a, op, b } => {
                    let ca = consts.get(&a).copied();
                    let cb = consts.get(&b).copied();

                    let ty       = function.value_type(dst);
                    let const_ty = match (ca, cb) {
                        (Some((ty, _)), _) => Some(ty),
                        (_, Some((ty, _))) => Some(ty),
                        _                  => None,
                    };

                    let ones = const_ty.map(|ty| {
                        match ty {
                            ConstType::U1  => panic!("U1 in arithmetic instruction."),
                            ConstType::U8  => u8::MAX  as u64,
                            ConstType::U16 => u16::MAX as u64,
                            ConstType::U32 => u32::MAX as u64,
                            ConstType::U64 => u64::MAX as u64,
                        }
                    }).unwrap_or(u64::MAX);

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

                                replacement = Some(Instruction::ArithmeticBinary {
                                    dst,
                                    a:  value,
                                    op: BinaryOp::Add,
                                    b:  value,
                                });
                            } else if cb == Some(2) {
                                let value = a;

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
                _ => {}
            }

            if let Some(replacement) = replacement {
                replacements.push((location, replacement));
            }
        });

        let did_something = !replacements.is_empty();

        for (location, replacement) in replacements {
            *function.instruction_mut(location) = replacement;
        }

        did_something
    }
}
