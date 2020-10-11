use super::{Value, Function, Label, Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Mod,
    Div,
    Shr,
    Shl,
    Sar,
    And,
    Or,
    Xor,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntPredicate {
    Equal,
    NotEqual,
    GtU,
    GteU,
    GtS,
    GteS,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cast {
    ZeroExtend,
    SignExtend,
    Truncate,
    Bitcast,
}

#[derive(Debug)]
pub enum Instruction {
    ArithmeticUnary {
        dst:   Value, 
        op:    UnaryOp,
        value: Value,
    },
    ArithmeticBinary {
        dst: Value, 
        a:   Value,
        op:  BinaryOp,
        b:   Value
    },
    IntCompare {
        dst:  Value,
        a:    Value,
        pred: IntPredicate,
        b:    Value,
    },
    Load {
        dst: Value,
        ptr: Value,
    },
    Store {
        ptr:   Value,
        value: Value,
    },
    Call {
        dst:  Option<Value>,
        func: Function,
        args: Vec<Value>,
    },
    Branch {
        target: Label,
    },
    BranchCond {
        value:    Value,
        on_true:  Label,
        on_false: Label,
    },
    StackAlloc {
        dst:  Value,
        ty:   Type,
        size: usize,
    },
    Return {
        value: Option<Value>,
    },
    Const {
        dst: Value,
        ty:  Type,
        imm: u64,
    },
    GetElementPtr {
        dst:    Value,
        source: Value,
        index:  Value,
    },
    Cast {
        dst:   Value,
        cast:  Cast,
        value: Value,
        ty:    Type,
    },
    Select {
        dst:      Value,
        cond:     Value,
        on_true:  Value,
        on_false: Value,
    },
}

impl Instruction {
    pub fn created_value(&self) -> Option<Value> {
        match *self {
            Instruction::ArithmeticUnary  { dst, .. } => Some(dst),
            Instruction::ArithmeticBinary { dst, .. } => Some(dst),
            Instruction::IntCompare       { dst, .. } => Some(dst),
            Instruction::Load             { dst, .. } => Some(dst),
            Instruction::Store            { ..      } => None,
            Instruction::Call             { dst, .. } => dst,
            Instruction::Branch           { ..      } => None,
            Instruction::BranchCond       { ..      } => None,
            Instruction::StackAlloc       { dst, .. } => Some(dst),
            Instruction::Return           { ..      } => None,
            Instruction::Const            { dst, .. } => Some(dst),
            Instruction::GetElementPtr    { dst, .. } => Some(dst),
            Instruction::Cast             { dst, .. } => Some(dst),
            Instruction::Select           { dst, .. } => Some(dst),
        }
    }

    pub fn read_values(&self) -> Vec<Value> {
        match *self {
            Instruction::ArithmeticUnary  { value, ..         } => vec![value],
            Instruction::ArithmeticBinary { a, b, ..          } => vec![a, b],
            Instruction::IntCompare       { a, b, ..          } => vec![a, b],
            Instruction::Load             { ptr, ..           } => vec![ptr],
            Instruction::Store            { ptr, value        } => vec![ptr, value],
            Instruction::Call             { ref args, ..      } => args.clone(),
            Instruction::Branch           { ..                } => vec![],
            Instruction::BranchCond       { value, ..         } => vec![value],
            Instruction::StackAlloc       { ..                } => vec![],
            Instruction::Return           { value, ..         } => value.into_iter().collect(),
            Instruction::Const            { ..                } => vec![],
            Instruction::GetElementPtr    { source, index, .. } => vec![source, index],
            Instruction::Cast             { value, ..         } => vec![value],
            Instruction::Select { cond, on_true, on_false, .. } => {
                vec![cond, on_true, on_false]
            }
        }
    }

    pub fn targets(&self) -> Option<Vec<Label>> {
        match self {
            Instruction::Return     { .. }                    => Some(vec![]),
            Instruction::Branch     { target }                => Some(vec![*target]),
            Instruction::BranchCond { on_true, on_false, .. } => Some(vec![*on_true, *on_false]),
            _                                                 => None,
        }
    }
}
