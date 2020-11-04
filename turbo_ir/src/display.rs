use std::io::{self, Write};
use std::fmt;

use super::{FunctionData, Instruction, Value, Label, BinaryOp, UnaryOp, IntPredicate, 
            Type, Cast, ty::TypeKind};

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0 as i64)
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            0 => write!(f, "entry"),
            _ => write!(f, "block_{}", self.0)
        }
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

pub trait IRFormatter {
    fn fmt_value(&self, value: Value) -> String;
    fn fmt_type(&self, name: String) -> String;
    fn fmt_inst(&self, name: String) -> String;
    fn fmt_label(&self, label: Label) -> String;
    fn fmt_literal(&self, literal: String) -> String;
    fn fmt_function(&self, name: &str) -> String;
}

impl FunctionData {
    fn display_type(&self, value: Value) -> String {
        match self.type_info.as_ref() {
            Some(type_info) => format!("{}", type_info[&value]),
            None            => String::from("unknown"),
        }
    }

    pub(super) fn print_instruction<W: Write, F: IRFormatter>(
        &self,
        w:           &mut W,
        instruction: &Instruction,
        formatter:   &F,
    ) -> io::Result<()> {
        macro_rules! fmt_type {
            ($value: expr) => { formatter.fmt_type(self.display_type($value)) }
        }

        macro_rules! fmt_raw_type {
            ($type: expr) => { formatter.fmt_type(format!("{}", $type)) }
        }

        macro_rules! fmt_value {
            ($value: expr) => {
                if self.undefined_set.contains(&$value) {
                    String::from("undefined")
                } else {
                    formatter.fmt_value($value) 
                }
            }
        }

        macro_rules! fmt_inst {
            ($name: expr) => { formatter.fmt_inst(format!("{}", $name)) }
        }

        macro_rules! fmt_label {
            ($label: expr) => { formatter.fmt_label($label) }
        }

        macro_rules! fmt_literal {
            ($literal: expr) => { formatter.fmt_literal(format!("{}", $literal)) }
        }

        macro_rules! fmt_function {
            ($name: expr) => { formatter.fmt_function($name) }
        }

        match instruction {
            Instruction::ArithmeticUnary { dst, op, value } => {
                write!(w, "{} = {} {} {}", fmt_value!(*dst), fmt_inst!(*op),
                       fmt_type!(*value), fmt_value!(*value))?;
            }
            Instruction::ArithmeticBinary { dst, a, op, b } => {
                write!(w, "{} = {} {} {}, {}", fmt_value!(*dst), fmt_inst!(*op),
                       fmt_type!(*a), fmt_value!(*a), fmt_value!(*b))?;
            }
            Instruction::IntCompare { dst, a, pred, b } => {
                write!(w, "{} = {} {} {} {}, {}", fmt_value!(*dst), fmt_inst!("icmp"), 
                       fmt_inst!(*pred), fmt_type!(*a), fmt_value!(*a), fmt_value!(*b))?;
            }
            Instruction::Load { dst, ptr } => {
                write!(w, "{} = {} {}, {} {}", fmt_value!(*dst), fmt_inst!("load"),
                       fmt_type!(*dst), fmt_type!(*ptr), fmt_value!(*ptr))?;
            }
            Instruction::Store { ptr, value } => {
                write!(w, "{} {} {}, {} {}", fmt_inst!("store"), fmt_type!(*ptr),
                       fmt_value!(*ptr), fmt_type!(*value), fmt_value!(*value))?;
            }
            Instruction::Call { dst, func, args } => {
                let prototype   = self.function_prototype(*func);
                let return_type = match prototype.return_type {
                    Some(return_type) => fmt_raw_type!(return_type),
                    None              => fmt_raw_type!("void"),
                };

                if let Some(dst) = dst {
                    write!(w, "{} = ", fmt_value!(*dst))?;
                }

                write!(w, "{} {} {}(", fmt_inst!("call"), return_type,
                       fmt_function!(&prototype.name))?;

                for (index, arg) in args.iter().enumerate() {
                    write!(w, "{} {}", fmt_type!(*arg), fmt_value!(*arg))?;

                    if index != prototype.arguments.len() - 1 {
                        write!(w, ", ")?;
                    }
                }

                write!(w, ")")?;
            }
            Instruction::Branch { target } => {
                write!(w, "{} {}", fmt_inst!("branch"), fmt_label!(*target))?;
            }
            Instruction::BranchCond { cond, on_true, on_false } => {
                write!(w, "{} {} {}, {}, {}", fmt_inst!("bcond"), fmt_type!(*cond),
                       fmt_value!(*cond), fmt_label!(*on_true), fmt_label!(*on_false))?;
            }
            Instruction::StackAlloc { dst, ty, size } => {
                write!(w, "{} = {} {}", fmt_value!(*dst), fmt_inst!("stackalloc"),
                       fmt_raw_type!(*ty))?;

                if *size != 1 {
                    write!(w, ", {}", fmt_literal!(*size))?;
                }
            }
            Instruction::Return { value } => {
                match value {
                    Some(value) => write!(w, "{} {} {}", fmt_inst!("ret"), fmt_type!(*value),
                                          fmt_value!(*value))?,
                    None => write!(w, "{} {}", fmt_inst!("ret"), fmt_raw_type!("void"))?,
                }
            }
            Instruction::Const { dst, ty, imm } => {
                match *ty {
                    Type::U1 => {
                        let value = match imm {
                            0 => "false",
                            1 => "true",
                            _ => panic!("Invalid U1 constant {}.", imm),
                        };

                        write!(w, "{} = {} {}", fmt_value!(*dst), fmt_raw_type!(ty),
                               fmt_literal!(value))?
                    }
                    _ => {
                        let value = match *ty {
                            Type::U8  => *imm as u8  as i8  as i64,
                            Type::U16 => *imm as u16 as i16 as i64,
                            Type::U32 => *imm as u32 as i32 as i64,
                            Type::U64 => *imm as i64,
                            _         => *imm as i64,
                        };

                        write!(w, "{} = {} {}", fmt_value!(*dst), fmt_raw_type!(*ty),
                               fmt_literal!(value))?;
                    }
                }
            }
            Instruction::GetElementPtr { dst, source, index } => {
                write!(w, "{} = {} {} {}, {} {}", fmt_value!(*dst), fmt_inst!("gep"),
                       fmt_type!(*source), fmt_value!(*source), fmt_type!(*index),
                       fmt_value!(*index))?;
            }
            Instruction::Cast { dst, cast, value, ty } => {
                write!(w, "{} = {} {} {} {} {}", fmt_value!(*dst), fmt_inst!(*cast),
                       fmt_type!(*value), fmt_value!(*value), fmt_inst!("to"),
                       fmt_raw_type!(*ty))?;
            }
            Instruction::Select { dst, cond, on_true, on_false } => {
                write!(w, "{} = {} {} {}, {} {}, {}", fmt_value!(*dst), fmt_inst!("select"),
                       fmt_type!(*cond), fmt_value!(*cond), fmt_type!(*on_true),
                       fmt_value!(*on_true), fmt_value!(*on_false))?;
            }
            Instruction::Phi { dst, incoming } => {
                if incoming.is_empty() {
                    write!(w, "{} = {} [invalid]", fmt_value!(*dst), fmt_inst!("phi"))?;
                } else {
                    write!(w, "{} = {} {} [", fmt_value!(*dst), fmt_inst!("phi"),
                        fmt_type!(incoming[0].1))?;

                    for (index, (label, value)) in incoming.iter().enumerate() {
                        write!(w, "{}: {}", fmt_label!(*label), fmt_value!(*value))?;

                        if index + 1 != incoming.len() {
                            write!(w, ", ")?;
                        }
                    }

                    write!(w, "]")?;
                }
            }
            Instruction::Alias { dst, value } => {
                write!(w, "{} = {} {} {}", fmt_value!(*dst), fmt_inst!("alias"), fmt_type!(*value),
                       fmt_value!(*value))?;
            }
            Instruction::Nop => {
                write!(w, "{}", fmt_inst!("nop"))?;
            }
        }

        Ok(())
    }
}
