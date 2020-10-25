use std::io::{self, Write};
use std::fmt;

use super::{FunctionData, Instruction, Value, Label, BinaryOp, UnaryOp, IntPredicate, 
            Type, Cast, ty::TypeKind};

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0 as i64)
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "label_{}", self.0)
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            UnaryOp::Neg => "neg",
            UnaryOp::Not => "not",
        };

        write!(f, "{}", name)
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            BinaryOp::Add  => "add",
            BinaryOp::Sub  => "sub",
            BinaryOp::Mul  => "mul",
            BinaryOp::ModS => "smod",
            BinaryOp::DivS => "sdiv",
            BinaryOp::ModU => "umod",
            BinaryOp::DivU => "udiv",
            BinaryOp::Shr  => "shr",
            BinaryOp::Shl  => "shl",
            BinaryOp::Sar  => "sar",
            BinaryOp::And  => "and",
            BinaryOp::Or   => "or",
            BinaryOp::Xor  => "xor",
        };

        write!(f, "{}", name)
    }
}

impl fmt::Display for IntPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            IntPredicate::Equal    => "eq", 
            IntPredicate::NotEqual => "ne", 
            IntPredicate::GtU      => "ugt", 
            IntPredicate::GteU     => "ugte", 
            IntPredicate::GtS      => "sgt", 
            IntPredicate::GteS     => "sgte", 
        };

        write!(f, "{}", name)
    }
}

impl fmt::Display for Cast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Cast::ZeroExtend => "zext",
            Cast::SignExtend => "sext",
            Cast::Truncate   => "trunc",
            Cast::Bitcast    => "bitcast",
        };

        write!(f, "{}", name)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self.kind {
            TypeKind::U1  => "u1",
            TypeKind::U8  => "u8",
            TypeKind::U16 => "u16",
            TypeKind::U32 => "u32",
            TypeKind::U64 => "u64",
        };

        write!(f, "{}", name)?;

        for _ in 0..self.indirection {
            write!(f, "*")?;
        }

        Ok(())
    }
}

impl FunctionData {
    fn display_type(&self, value: Value) -> String {
        match self.type_info.as_ref() {
            Some(type_info) => format!("{}", type_info[&value]),
            None            => String::from("unk"),
        }
    }

    pub(super) fn print_instruction<W: Write>(&self, w: &mut W, 
                                              instruction: &Instruction) -> io::Result<()> {
        match instruction {
            Instruction::ArithmeticUnary { dst, op, value } => {
                write!(w, "{} = {} {} {}", dst, op, self.display_type(*value), value)?;
            }
            Instruction::ArithmeticBinary { dst, a, op, b } => {
                write!(w, "{} = {} {} {}, {}", dst, op, self.display_type(*a), a, b)?;
            }
            Instruction::IntCompare { dst, a, pred, b } => {
                write!(w, "{} = icmp {} {} {}, {}", dst, pred, self.display_type(*a), a, b)?;
            }
            Instruction::Load { dst, ptr } => {
                write!(w, "{} = load {}, {} {}", dst, self.display_type(*dst),
                       self.display_type(*ptr), ptr)?;
            }
            Instruction::Store { ptr, value } => {
                write!(w, "store {} {}, {} {}", self.display_type(*ptr), ptr,
                       self.display_type(*value), value)?;
            }
            Instruction::Call { dst, func, args } => {
                let prototype   = self.function_prototype(*func);
                let return_type = match prototype.return_type {
                    Some(return_type) => format!("{}", return_type),
                    None              => String::from("void"),
                };

                if let Some(dst) = dst {
                    write!(w, "{} = ", dst)?;
                }

                write!(w, "call {} {}(", return_type, prototype.name)?;

                for (index, arg) in args.iter().enumerate() {
                    write!(w, "{} {}", self.display_type(*arg), arg)?;

                    if index != prototype.arguments.len() - 1 {
                        write!(w, ", ")?;
                    }
                }

                write!(w, ")")?;
            }
            Instruction::Branch { target } => {
                write!(w, "branch {}", target)?;
            }
            Instruction::BranchCond { cond, on_true, on_false } => {
                write!(w, "bcond {} {}, {}, {}", self.display_type(*cond),
                       cond, on_true, on_false)?;
            }
            Instruction::StackAlloc { dst, ty, size } => {
                write!(w, "{} = stackalloc {}", dst, ty)?;

                if *size != 1 {
                    write!(w, ", {}", size)?;
                }
            }
            Instruction::Return { value } => {
                match value {
                    Some(value) => write!(w, "ret {} {}", self.display_type(*value), value)?,
                    None        => write!(w, "ret void")?,
                }
            }
            Instruction::Const { dst, ty, imm } => {
                match *ty {
                    Type::U1 => {
                        match imm {
                            0 => write!(w, "{} = {} false", dst, ty)?,
                            1 => write!(w, "{} = {} true", dst, ty)?,
                            _ => panic!("Invalid U1 constant {}.", imm),
                        }
                    }
                    _ => {
                        let value = match *ty {
                            Type::U8  => *imm as u8  as i8  as i64,
                            Type::U16 => *imm as u16 as i16 as i64,
                            Type::U32 => *imm as u32 as i32 as i64,
                            Type::U64 => *imm as i64,
                            _         => *imm as i64,
                        };

                        write!(w, "{} = {} {}", dst, ty, value)?;
                    }
                }
            }
            Instruction::GetElementPtr { dst, source, index } => {
                write!(w, "{} = gep {} {}, {} {}", dst, self.display_type(*source),
                       source, self.display_type(*index), index)?;
            }
            Instruction::Cast { dst, cast, value, ty } => {
                write!(w, "{} = {} {} {} to {}", dst, cast, self.display_type(*value),
                       value, ty)?;
            }
            Instruction::Select { dst, cond, on_true, on_false } => {
                write!(w, "{} = select {} {}, {} {}, {}", dst, self.display_type(*cond),
                       cond, self.display_type(*on_true), on_true, on_false)?;
            }
            Instruction::Alias { dst, value } => {
                write!(w, "{} = alias {} {}", dst, self.display_type(*value), value)?;
            }
            Instruction::Nop => {
                write!(w, "nop")?;
            }
        }

        Ok(())
    }
}
