use std::io::{self, Write};
use std::fmt;

use super::{FunctionData, Instruction, Value, Label, BinaryOp, UnaryOp, IntPredicate, 
            Type, TypeKind};

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
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
            BinaryOp::Add => "add",
            BinaryOp::Sub => "sub",
            BinaryOp::Mul => "mul",
            BinaryOp::Mod => "mod",
            BinaryOp::Div => "div",
            BinaryOp::Shr => "shr",
            BinaryOp::Shl => "shl",
            BinaryOp::And => "and",
            BinaryOp::Or  => "or",
            BinaryOp::Xor => "xor",
        };

        write!(f, "{}", name)
    }
}

impl fmt::Display for IntPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            IntPredicate::Equal    => "equal", 
            IntPredicate::NotEqual => "not_equal", 
            IntPredicate::GtU      => "gt_u", 
            IntPredicate::GteU     => "gte_u", 
            IntPredicate::GtS      => "gt_s", 
            IntPredicate::GteS     => "gte_s", 
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
    pub(super) fn print_instruction<W: Write>(&self, w: &mut W, 
                                              instruction: &Instruction) -> io::Result<()> {
        match instruction {
            Instruction::ArithmeticUnary { dst, op, value } => {
                write!(w, "{} = {} {}", dst, op, value)?;
            }
            Instruction::ArithmeticBinary { dst, a, op, b } => {
                write!(w, "{} = {} {}, {}", dst, op, a, b)?;
            }
            Instruction::IntCompare { dst, a, pred, b } => {
                write!(w, "{} = icmp {}, {}, {}", dst, a, b, pred)?;
            }
            Instruction::Load { dst, ptr } => {
                write!(w, "{} = load {}", dst, ptr)?;
            }
            Instruction::Store { ptr, value } => {
                write!(w, "store {}, {}", ptr, value)?;
            }
            Instruction::Call { dst, func, args } => {
                let function_name = &self.function_info.as_ref()
                    .unwrap()[&func].name;

                write!(w, "call {}", function_name)?;
            }
            Instruction::Branch { target } => {
                write!(w, "branch {}", target)?;
            }
            Instruction::BranchCond { value, on_true, on_false } => {
                write!(w, "bcond {}, {}, {}", value, on_true, on_false)?;
            }
            Instruction::StackAlloc { dst, ty, size } => {
                write!(w, "{} = stackalloc {} {}", dst, ty, size)?;
            }
            Instruction::Return { value } => {
                match value {
                    Some(value) => write!(w, "ret {}", value)?,
                    None        => write!(w, "ret void")?,
                }
            }
            Instruction::Const { dst, ty, imm } => {
                write!(w, "{} = {} {}", dst, ty, imm)?;
            }
        }

        Ok(())
    }
}
