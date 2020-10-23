use super::{FunctionData, Instruction, Pass};
use super::super::{Type, BinaryOp, UnaryOp, Cast, IntPredicate, ConstType};

pub struct ConstPropagatePass;

impl Pass for ConstPropagatePass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let mut consts        = function.constant_values();

        macro_rules! propagate_unary {
            ($op: expr, $value: expr, $unsigned: ty) => {{
                let value = $value as $unsigned;

                let result = match $op {
                    UnaryOp::Neg => value.wrapping_neg(),
                    UnaryOp::Not => !value,
                };

                result as u64
            }}
        }

        macro_rules! propagate_binary {
            ($a: expr, $op: expr, $b: expr, $signed: ty, $unsigned: ty) => {{
                let a = $a as $unsigned;
                let b = $b as $unsigned;

                let result = match $op {
                    BinaryOp::Add  => a.wrapping_add(b),
                    BinaryOp::Sub  => a.wrapping_sub(b),
                    BinaryOp::Mul  => a.wrapping_mul(b),
                    BinaryOp::ModU => a % b,
                    BinaryOp::DivU => a / b,
                    BinaryOp::ModS => ((a as $signed) % (a as $signed)) as $unsigned,
                    BinaryOp::DivS => ((a as $signed) / (b as $signed)) as $unsigned,
                    BinaryOp::Shr  => a >> b,
                    BinaryOp::Shl  => a << b,
                    BinaryOp::Sar  => ((a as $signed) >> b) as $unsigned,
                    BinaryOp::And  => a & b,
                    BinaryOp::Or   => a | b,
                    BinaryOp::Xor  => a ^ b,
                };

                result as u64
            }}
        }

        macro_rules! propagate_compare {
            ($a: expr, $pred: expr, $b: expr, $signed: ty, $unsigned: ty) => {{
                let ua = $a as $unsigned;
                let ub = $b as $unsigned;

                let sa = $a as $signed;
                let sb = $b as $signed;

                let result = match $pred {
                    IntPredicate::Equal    => ua == ub,
                    IntPredicate::NotEqual => ua != ub,
                    IntPredicate::GtU      => ua >  ub,
                    IntPredicate::GteU     => ua >= ub,
                    IntPredicate::GtS      => sa >  sb,
                    IntPredicate::GteS     => sa >= sb,
                };

                result as u64
            }}
        }

        macro_rules! propagate_cast {
            (r, $from: expr, $cast: expr, $from_signed: ty,
                $from_unsigned: ty, $to_unsigned: ty) => {{

                let from = $from as $from_unsigned;

                let result = match $cast {
                    Cast::Truncate   => from as $to_unsigned,
                    Cast::ZeroExtend => from as $to_unsigned,
                    Cast::SignExtend => from as $from_signed as $to_unsigned,
                    Cast::Bitcast    => panic!("Bitcast is not supported here."),
                };

                result as u64
            }};
            ($from: expr, $cast: expr, $dst_ty: expr, $from_signed: ty, $from_unsigned: ty) => {{
                match *$dst_ty {
                    Type::U8  => propagate_cast!(r, $from, $cast, $from_signed,
                                                 $from_unsigned, u8),
                    Type::U16 => propagate_cast!(r, $from, $cast, $from_signed,
                                                 $from_unsigned, u16),
                    Type::U32 => propagate_cast!(r, $from, $cast, $from_signed,
                                                 $from_unsigned, u32),
                    Type::U64 => propagate_cast!(r, $from, $cast, $from_signed,
                                                 $from_unsigned, u64),
                    _ => panic!("Invalid {:?} cast to {:?}.", $cast, $dst_ty),
                }
            }};
        }

        function.for_each_instruction_mut(|_location, instruction| {
            let mut propagated = None;

            match instruction {
                Instruction::ArithmeticUnary { op, value, .. } => {
                    if let Some(&(ty, value)) = consts.get(value) {
                        let result = match ty {
                            ConstType::U1  => panic!("U1 not allowed in unary instruction."),
                            ConstType::U8  => propagate_unary!(op, value, u8),
                            ConstType::U16 => propagate_unary!(op, value, u16),
                            ConstType::U32 => propagate_unary!(op, value, u32),
                            ConstType::U64 => propagate_unary!(op, value, u64),
                        };

                        propagated = Some((ty.ir_type(), result));
                    }
                }
                Instruction::ArithmeticBinary { a, op, b, .. } => {
                    if let (Some(&(a_ty, a)), Some(&(b_ty, b))) = (consts.get(a), consts.get(b)) {
                        assert!(a_ty == b_ty, "Constprop: binary arihmetic instruction \
                                has different operand types.");

                        let result = match a_ty {
                            ConstType::U1  => panic!("U1 not allowed in binary instruction."),
                            ConstType::U8  => propagate_binary!(a, op, b, i8,  u8),
                            ConstType::U16 => propagate_binary!(a, op, b, i16, u16),
                            ConstType::U32 => propagate_binary!(a, op, b, i32, u32),
                            ConstType::U64 => propagate_binary!(a, op, b, i64, u64),
                        };

                        propagated = Some((a_ty.ir_type(), result));
                    }
                }
                Instruction::IntCompare { a, pred, b, .. } => {
                    if let (Some(&(a_ty, a)), Some(&(b_ty, b))) = (consts.get(a), consts.get(b)) {
                        assert!(a_ty == b_ty, "Constprop: int compare instruction \
                                has different operand types.");

                        let result = match a_ty {
                            ConstType::U1  => panic!("U1 not allowed in compare instruction."),
                            ConstType::U8  => propagate_compare!(a, pred, b, i8,  u8),
                            ConstType::U16 => propagate_compare!(a, pred, b, i16, u16),
                            ConstType::U32 => propagate_compare!(a, pred, b, i32, u32),
                            ConstType::U64 => propagate_compare!(a, pred, b, i64, u64),
                        };

                        propagated = Some((Type::U1, result));
                    }
                }
                Instruction::BranchCond { value, on_true, on_false } => {
                    if let Some(&(_, cond)) = consts.get(value) {
                        let target = match cond {
                            0 => *on_false,
                            1 => *on_true,
                            _ => panic!("Invalid U1 constant {}.", cond),
                        };

                        *instruction = Instruction::Branch {
                            target,
                        };

                        did_something = true;
                    }
                }
                Instruction::Cast { cast, value, ty: dst_ty, ..} => {
                    if let Some(&(ty, value)) = consts.get(value) {
                        if *cast == Cast::Bitcast {
                            propagated = Some((*dst_ty, value));
                        } else {
                            let result = match ty {
                                ConstType::U1  => panic!("U1 not allowed in cast instruction."),
                                ConstType::U8  => propagate_cast!(value, cast, dst_ty, i8,  u8),
                                ConstType::U16 => propagate_cast!(value, cast, dst_ty, i16, u16),
                                ConstType::U32 => propagate_cast!(value, cast, dst_ty, i32, u32),
                                ConstType::U64 => propagate_cast!(value, cast, dst_ty, i64, u64),
                            };

                            propagated = Some((*dst_ty, result));
                        }
                    }
                }
                Instruction::Select { dst, cond, on_true, on_false } => {
                    if let Some(&(_, cond)) = consts.get(cond) {
                        let value = match cond {
                            0 => *on_false,
                            1 => *on_true,
                            _ => panic!("Invalid U1 constant {}.", cond),
                        };

                        *instruction = Instruction::Alias {
                            dst: *dst,
                            value,
                        };

                        did_something = true;
                    }
                }
                _ => {}
            }

            if let Some((ty, propagated)) = propagated {
                let dst = instruction.created_value()
                    .expect("Propagated constant from instruction which doesn't create value?");

                if ty == Type::U1 {
                    assert!(propagated == 0 || propagated == 1,
                            "Invalid propagated U1 constant {}.", propagated);
                }

                if let Some(ty) = ConstType::from_ir_type(ty) {
                    assert!(consts.insert(dst, (ty, propagated)).is_none(),
                            "Propagated already constant value?");
                }

                *instruction = Instruction::Const {
                    dst,
                    ty,
                    imm: propagated,
                };

                did_something = true;
            }
        });

        did_something
    }
}