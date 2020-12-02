use crate::{FunctionData, Instruction, Type, BinaryOp, UnaryOp, Cast,
            IntPredicate, ConstType, PhiUpdater, Const, Value};

enum Replacement {
    Instruction(Instruction),
    Constant(Value, Type, Const),
}

pub struct ConstPropagatePass;

impl super::Pass for ConstPropagatePass {
    fn name(&self) -> &str {
        "constant propagation"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::const_propagate()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let labels          = function.reachable_labels();
        let mut consts      = function.constant_values_with_labels(&labels);
        let mut phi_updater = PhiUpdater::new();

        // Optimize instructions with constant operands.
        //
        // v1 = u32 0
        // v2 = u32 4
        // v3 = add u32 v1, v2
        //
        // v3 will be optimized to:
        // v3 = u32 4
        //
        // Dead code elimination then can remove v1 and v2 if they are not used anythere else.
        // Conditional branches with constant conditions will be optimized to normal branches.
        // Selects will be optimized to alias selected values.
        //
        // Optimization applies to unary instructions, binary instructions, compare instructions,
        // cast instructions and conditional instructions.

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

        let mut replacements = Vec::new();

        function.for_each_instruction_with_labels(&labels, |location, instruction| {
            let mut propagated = None;

            // Check all adequate instructions if they have constant operands. If they do,
            // compute result of their operation.
            match instruction {
                Instruction::ArithmeticUnary { op, value, .. } => {
                    if let Some(&(ty, value)) = consts.get(value) {
                        let result = match ConstType::new(ty) {
                            ConstType::U1  => panic!("U1 not allowed in unary instruction."),
                            ConstType::U8  => propagate_unary!(op, value, u8),
                            ConstType::U16 => propagate_unary!(op, value, u16),
                            ConstType::U32 => propagate_unary!(op, value, u32),
                            ConstType::U64 => propagate_unary!(op, value, u64),
                        };

                        propagated = Some(result);
                    }
                }
                Instruction::ArithmeticBinary { a, op, b, .. } => {
                    if let (Some(&(a_ty, a)), Some(&(_, b))) = (consts.get(a), consts.get(b)) {
                        let result = match ConstType::new(a_ty) {
                            ConstType::U1  => panic!("U1 not allowed in binary instruction."),
                            ConstType::U8  => propagate_binary!(a, op, b, i8,  u8),
                            ConstType::U16 => propagate_binary!(a, op, b, i16, u16),
                            ConstType::U32 => propagate_binary!(a, op, b, i32, u32),
                            ConstType::U64 => propagate_binary!(a, op, b, i64, u64),
                        };

                        propagated = Some(result);
                    }
                }
                Instruction::IntCompare { a, pred, b, .. } => {
                    if let (Some(&(a_ty, a)), Some(&(_, b))) = (consts.get(a), consts.get(b)) {
                        let result = match ConstType::new(a_ty) {
                            ConstType::U1  => panic!("U1 not allowed in compare instruction."),
                            ConstType::U8  => propagate_compare!(a, pred, b, i8,  u8),
                            ConstType::U16 => propagate_compare!(a, pred, b, i16, u16),
                            ConstType::U32 => propagate_compare!(a, pred, b, i32, u32),
                            ConstType::U64 => propagate_compare!(a, pred, b, i64, u64),
                        };

                        propagated = Some(result);
                    }
                }
                Instruction::BranchCond { cond, on_true, on_false } => {
                    if let Some(&(_, cond)) = consts.get(cond) {
                        // If condition is constant then only one branch will be taken.
                        // Convert instruction to simple branch instruction.

                        let (target, removed) = match cond {
                            0 => (*on_false, *on_true),
                            1 => (*on_true,  *on_false),
                            _ => panic!("Invalid U1 constant {}.", cond),
                        };

                        replacements.push((location, Replacement::Instruction(Instruction::Branch {
                            target,
                        })));

                        // We have modified the control flow. Queue update of PHI instructions.
                        phi_updater.removed_branch(location.label(), removed);
                    }
                }
                Instruction::Cast { cast, value, ty: dst_ty, ..} => {
                    if let Some(&(ty, value)) = consts.get(value) {
                        if *cast == Cast::Bitcast {
                            // Bitcasts don't affect value whatsoever.
                            propagated = Some(value);
                        } else {
                            let result = match ConstType::new(ty) {
                                ConstType::U1  => panic!("U1 not allowed in cast instruction."),
                                ConstType::U8  => propagate_cast!(value, cast, dst_ty, i8,  u8),
                                ConstType::U16 => propagate_cast!(value, cast, dst_ty, i16, u16),
                                ConstType::U32 => propagate_cast!(value, cast, dst_ty, i32, u32),
                                ConstType::U64 => propagate_cast!(value, cast, dst_ty, i64, u64),
                            };

                            propagated = Some(result);
                        }
                    }
                }
                Instruction::Select { dst, cond, on_true, on_false } => {
                    if let Some(&(_, cond)) = consts.get(cond) {
                        // If condition is constant then only one value will be selected.
                        // Convert select to alias of always selected value.

                        let value = match cond {
                            0 => *on_false,
                            1 => *on_true,
                            _ => panic!("Invalid U1 constant {}.", cond),
                        };

                        replacements.push((location, Replacement::Instruction(Instruction::Alias {
                            dst: *dst,
                            value,
                        })));
                    }
                }
                _ => {}
            }

            if let Some(propagated) = propagated {
                // If we constant propagated instruction then it must have output value.
                let dst = instruction.created_value()
                    .expect("Propagated constant from instruction which doesn't create value?");

                let ty = function.value_type(dst);
                if  ty == Type::U1 {
                    // U1s can be only true or false.
                    assert!(propagated == 0 || propagated == 1,
                            "Invalid propagated U1 constant {}.", propagated);
                }

                // Replace propagated instruction with computed constant.
                replacements.push((location, Replacement::Constant(dst, ty, propagated)));

                // Add propagated value to known constants database.
                assert!(consts.insert(dst, (ty, propagated)).is_none(),
                        "Propagated already constant value?");
            }
        });

        let did_something = !replacements.is_empty();

        // Actually perform the replacements.
        for (location, replacement) in replacements {
            let replacement = match replacement {
                Replacement::Instruction(i) => i,
                Replacement::Constant(dst, ty, constant) => {
                    let value = function.add_constant(ty, constant);

                    Instruction::Alias {
                        dst,
                        value,
                    }
                }
            };

            *function.instruction_mut(location) = replacement;
        }

        // Update PHI instructions.
        phi_updater.apply(function);

        did_something
    }
}
