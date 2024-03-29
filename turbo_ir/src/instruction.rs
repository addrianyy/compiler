use super::{Value, Function, Label, Type};
use smallvec::{SmallVec, smallvec};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    ModU,
    DivU,
    ModS,
    DivS,
    Shr,
    Shl,
    Sar,
    And,
    Or,
    Xor,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntPredicate {
    Equal,
    NotEqual,

    GtU,
    GteU,
    GtS,
    GteS,

    LtU,
    LteU,
    LtS,
    LteS,
}

impl IntPredicate {
    pub fn invert(self) -> Self {
        match self {
            IntPredicate::Equal    => IntPredicate::NotEqual,
            IntPredicate::NotEqual => IntPredicate::Equal,
            IntPredicate::GtS      => IntPredicate::LteS,
            IntPredicate::GteS     => IntPredicate::LtS,
            IntPredicate::GtU      => IntPredicate::LteU,
            IntPredicate::GteU     => IntPredicate::LtU,
            IntPredicate::LtS      => IntPredicate::GteS,
            IntPredicate::LteS     => IntPredicate::GtS,
            IntPredicate::LtU      => IntPredicate::GteU,
            IntPredicate::LteU     => IntPredicate::GtU,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
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
        cond:     Value,
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
    Phi {
        dst:      Value,
        incoming: Vec<(Label, Value)>,
    },
    Alias {
        dst:   Value,
        value: Value,
    },
    Nop,
}

#[derive(PartialEq, Eq, Hash)]
pub enum Param {
    UnaryOp(UnaryOp),
    BinaryOp(BinaryOp),
    IntPredicate(IntPredicate),
    Value(Value),
    Label(Label),
    Cast(Cast),
    Type(Type),
    Integer(usize),
    Function(Function),
}

impl BinaryOp {
    fn is_commutative_and_associative(&self) -> bool {
        match self {
            BinaryOp::Add | BinaryOp::Mul | BinaryOp::And |
            BinaryOp::Or  | BinaryOp::Xor => {
                true
            }
            _ => false,
        }
    }

    pub fn is_commutative(&self) -> bool {
        self.is_commutative_and_associative()
    }

    pub fn is_associative(&self) -> bool {
        self.is_commutative_and_associative()
    }
}

impl Instruction {
    pub fn input_parameters(&self) -> Vec<Param> {
        time!(input_parameters);

        match *self {
            Instruction::ArithmeticUnary { op, value, .. } => {
                vec![
                    Param::Value(value),
                    Param::UnaryOp(op),
                ]
            }
            Instruction::ArithmeticBinary { a, op, b, .. } => {
                let mut a = a;
                let mut b = b;

                // If operator is commutative than make sure that `op a, b` and `op b, a` will
                // be treated as having the same parameters.
                if op.is_commutative() && a.0 > b.0 {
                    std::mem::swap(&mut a, &mut b);
                }

                vec![
                    Param::Value(a),
                    Param::BinaryOp(op),
                    Param::Value(b),
                ]
            }
            Instruction::IntCompare { a, pred, b, .. } => {
                vec![
                    Param::Value(a),
                    Param::IntPredicate(pred),
                    Param::Value(b),
                ]
            }
            Instruction::Load { ptr, .. } => {
                vec![
                    Param::Value(ptr),
                ]
            }
            Instruction::Store { ptr, value, .. } => {
                vec![
                    Param::Value(ptr),
                    Param::Value(value),
                ]
            }
            Instruction::Call { func, ref args, .. } => {
                let mut params = Vec::with_capacity(args.len() + 1);

                params.push(Param::Function(func));

                for arg in args {
                    params.push(Param::Value(*arg));
                }

                params
            }
            Instruction::Branch { target } => {
                vec![
                    Param::Label(target),
                ]
            }
            Instruction::BranchCond { on_true, on_false, cond } => {
                vec![
                    Param::Label(on_true),
                    Param::Label(on_false),
                    Param::Value(cond),
                ]
            }
            Instruction::StackAlloc { ty, size, .. } => {
                vec![
                    Param::Type(ty),
                    Param::Integer(size),
                ]
            }
            Instruction::Return { value } => {
                if let Some(value) = value {
                    vec![Param::Value(value)]
                } else {
                    vec![]
                }
            }
            Instruction::GetElementPtr { source, index, .. } => {
                vec![
                    Param::Value(source),
                    Param::Value(index),
                ]
            }
            Instruction::Cast { cast, value, ty, .. } => {
                vec![
                    Param::Cast(cast),
                    Param::Value(value),
                    Param::Type(ty),
                ]
            }
            Instruction::Select { cond, on_true, on_false, .. } => {
                vec![
                    Param::Value(cond),
                    Param::Value(on_true),
                    Param::Value(on_false),
                ]
            }
            Instruction::Phi { ref incoming, .. } => {
                let mut params = Vec::with_capacity(incoming.len() * 2);

                for (label, value) in incoming {
                    params.push(Param::Label(*label));
                    params.push(Param::Value(*value));
                }

                params
            }
            Instruction::Alias { value, .. } => {
                vec![
                    Param::Value(value),
                ]
            }
            Instruction::Nop => {
                vec![]
            }
        }
    }

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
            Instruction::GetElementPtr    { dst, .. } => Some(dst),
            Instruction::Cast             { dst, .. } => Some(dst),
            Instruction::Select           { dst, .. } => Some(dst),
            Instruction::Phi              { dst, .. } => Some(dst),
            Instruction::Alias            { dst, .. } => Some(dst),
            Instruction::Nop                          => None,
        }
    }

    pub fn read_values(&self) -> SmallVec<[Value; 4]> {
        // Keep these values in proper order so register allocator can reuse some registers.
        // For example in %5 = add %0 %1, %5 and %0 may get allocated in the same register.

        match *self {
            Instruction::ArithmeticUnary  { value, ..         } => smallvec![value],
            Instruction::ArithmeticBinary { a, b, ..          } => smallvec![a, b],
            Instruction::IntCompare       { a, b, ..          } => smallvec![a, b],
            Instruction::Load             { ptr, ..           } => smallvec![ptr],
            Instruction::Store            { ptr, value        } => smallvec![ptr, value],
            Instruction::Call             { ref args, ..      } => args.clone().into(),
            Instruction::Branch           { ..                } => smallvec![],
            Instruction::BranchCond       { cond, ..          } => smallvec![cond],
            Instruction::StackAlloc       { ..                } => smallvec![],
            Instruction::Return           { value, ..         } => value.into_iter().collect(),
            Instruction::GetElementPtr    { source, index, .. } => smallvec![source, index],
            Instruction::Cast             { value, ..         } => smallvec![value],
            Instruction::Alias            { value, ..         } => smallvec![value],
            Instruction::Nop                                    => smallvec![],
            Instruction::Select { cond, on_true, on_false, .. } => {
                smallvec![cond, on_true, on_false]
            }
            Instruction::Phi { ref incoming, .. } => {
                incoming.iter()
                    .map(|(_label, value)| *value)
                    .collect()
            }
        }
    }

    pub fn transform_output(&mut self, mut f: impl FnMut(&mut Value)) {
        match self {
            Instruction::ArithmeticUnary  { dst, .. } => f(dst),
            Instruction::ArithmeticBinary { dst, .. } => f(dst),
            Instruction::IntCompare       { dst, .. } => f(dst),
            Instruction::Load             { dst, .. } => f(dst),
            Instruction::Store            { ..      } => {}
            Instruction::Call             { dst, .. } => {
                if let Some(dst) = dst {
                    f(dst);
                }
            }
            Instruction::Branch           { ..      } => {}
            Instruction::BranchCond       { ..      } => {}
            Instruction::StackAlloc       { dst, .. } => f(dst),
            Instruction::Return           { ..      } => {}
            Instruction::GetElementPtr    { dst, .. } => f(dst),
            Instruction::Cast             { dst, .. } => f(dst),
            Instruction::Select           { dst, .. } => f(dst),
            Instruction::Phi              { dst, .. } => f(dst),
            Instruction::Alias            { dst, .. } => f(dst),
            Instruction::Nop                          => {}
        }
    }

    pub fn transform_inputs(&mut self, mut f: impl FnMut(&mut Value)) {
        match self {
            Instruction::ArithmeticUnary  { value, ..         } => { f(value); }
            Instruction::ArithmeticBinary { a, b, ..          } => { f(a); f(b); }
            Instruction::IntCompare       { a, b, ..          } => { f(a); f(b); }
            Instruction::Load             { ptr, ..           } => { f(ptr); }
            Instruction::Store            { ptr, value        } => { f(ptr); f(value); }
            Instruction::Call             { ref mut args, ..  } => {
                for arg in args {
                    f(arg);
                }
            }
            Instruction::Branch           { ..                } => {},
            Instruction::BranchCond       { cond, ..          } => f(cond),
            Instruction::StackAlloc       { ..                } => {},
            Instruction::Return           { value, ..         } => {
                if let Some(value) = value {
                    f(value);
                }
            }
            Instruction::GetElementPtr    { source, index, .. } => { f(source); f(index); }
            Instruction::Cast             { value, ..         } => f(value),
            Instruction::Alias            { value, ..         } => f(value),
            Instruction::Nop                                    => {},
            Instruction::Select { cond, on_true, on_false, .. } => {
                f(cond); f(on_true); f(on_false);
            }
            Instruction::Phi { ref mut incoming, .. } => {
                for (_label, value) in incoming {
                    f(value);
                }
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

    pub fn is_volatile(&self) -> bool {
        match self {
            Instruction::Return { .. } | Instruction::Call   { .. } |
            Instruction::Store  { .. } | Instruction::Branch { .. } |
            Instruction::BranchCond { .. }  => {
                true
            }
            _ => false,
        }
    }

    pub fn can_be_reordered(&self) -> bool {
        !self.is_volatile() && !matches!(self, Instruction::Load { .. } | Instruction::Phi { .. })
    }

    pub fn is_phi(&self) -> bool {
        matches!(self, Instruction::Phi { .. })
    }

    pub fn is_nop(&self) -> bool {
        matches!(self, Instruction::Nop)
    }
}
