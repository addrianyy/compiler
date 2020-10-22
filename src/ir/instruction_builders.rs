use super::{Module, Instruction, Value, Label, Function, Type, UnaryOp, BinaryOp,
           IntPredicate, Cast};

macro_rules! implement_arithmetic_unary {
    ($name: ident, $op: expr) => {
        #[allow(unused)]
        pub fn $name(&mut self, value: Value) -> Value {
            self.arithmetic_unary($op, value)
        }
    }
}

macro_rules! implement_arithmetic_binary {
    ($name: ident, $op: expr) => {
        #[allow(unused)]
        pub fn $name(&mut self, a: Value, b: Value) -> Value {
            self.arithmetic_binary(a, $op, b)
        }
    }
}

macro_rules! implement_compare {
    ($name: ident, $predicate: expr) => {
        #[allow(unused)]
        pub fn $name(&mut self, a: Value, b: Value) -> Value {
            self.int_compare(a, $predicate, b)
        }
    }
}

macro_rules! implement_cast {
    ($name: ident, $cast: expr) => {
        #[allow(unused)]
        pub fn $name(&mut self, value: Value, ty: Type) -> Value {
            self.cast(value, ty, $cast)
        }
    }
}

impl Module {
    fn insert(&mut self, instruction: Instruction) {
        let active_point = self.active_point();

        self.function_mut(active_point.function)
            .insert(active_point.label, instruction);
    }

    fn with_output(&mut self, f: impl FnOnce(Value) -> Instruction) -> Value {
        let active_point = self.active_point();
        let function     = self.function_mut(active_point.function);
        let value        = function.allocate_value();
        let instruction  = f(value);

        function.insert(active_point.label, instruction);

        value
    }

    implement_arithmetic_unary!(neg, UnaryOp::Neg);
    implement_arithmetic_unary!(not, UnaryOp::Not);

    implement_arithmetic_binary!(add,  BinaryOp::Add);
    implement_arithmetic_binary!(sub,  BinaryOp::Sub);
    implement_arithmetic_binary!(mul,  BinaryOp::Mul);
    implement_arithmetic_binary!(umod, BinaryOp::ModU);
    implement_arithmetic_binary!(udiv, BinaryOp::DivU);
    implement_arithmetic_binary!(smod, BinaryOp::ModS);
    implement_arithmetic_binary!(sdiv, BinaryOp::DivS);
    implement_arithmetic_binary!(shr,  BinaryOp::Shr);
    implement_arithmetic_binary!(shl,  BinaryOp::Shl);
    implement_arithmetic_binary!(sar,  BinaryOp::Sar);
    implement_arithmetic_binary!(and,  BinaryOp::And);
    implement_arithmetic_binary!(or,   BinaryOp::Or);
    implement_arithmetic_binary!(xor,  BinaryOp::Xor);

    implement_compare!(compare_eq,   IntPredicate::Equal);
    implement_compare!(compare_ne,   IntPredicate::NotEqual);
    implement_compare!(compare_ugt,  IntPredicate::GtU);
    implement_compare!(compare_ugte, IntPredicate::GteU);
    implement_compare!(compare_sgt,  IntPredicate::GtS);
    implement_compare!(compare_sgte, IntPredicate::GteS);

    implement_cast!(zero_extend, Cast::ZeroExtend);
    implement_cast!(sign_extend, Cast::SignExtend);
    implement_cast!(truncate,    Cast::Truncate);
    implement_cast!(bitcast,     Cast::Bitcast);

    pub fn arithmetic_unary(&mut self, op: UnaryOp, value: Value) -> Value {
        self.with_output(|dst| Instruction::ArithmeticUnary { dst, op, value })
    }

    pub fn arithmetic_binary(&mut self, a: Value, op: BinaryOp, b: Value) -> Value {
        self.with_output(|dst| Instruction::ArithmeticBinary { dst, a, op, b })
    }

    pub fn int_compare(&mut self, a: Value, pred: IntPredicate, b: Value) -> Value {
        self.with_output(|dst| Instruction::IntCompare { dst, a, pred, b })
    }

    pub fn load(&mut self, ptr: Value) -> Value {
        self.with_output(|dst| Instruction::Load { dst, ptr })
    }

    pub fn store(&mut self, ptr: Value, value: Value) {
        self.insert(Instruction::Store { ptr, value });
    }

    pub fn call(&mut self, func: Function, args: Vec<Value>) -> Option<Value> {
        match self.function_prototype(func).return_type.is_some() {
            true => {
                Some(self.with_output(|dst| {
                    Instruction::Call { dst: Some(dst), func, args }
                }))
            }
            false => {
                self.insert(Instruction::Call { dst: None, func, args });
                None
            }
        }
    }

    pub fn branch(&mut self, target: Label) {
        self.insert(Instruction::Branch { target });
    }

    pub fn branch_cond(&mut self, value: Value, on_true: Label, on_false: Label) {
        self.insert(Instruction::BranchCond { value, on_true, on_false });
    }

    pub fn stack_alloc(&mut self, ty: Type, size: usize) -> Value {
        self.with_output(|dst| Instruction::StackAlloc { dst, ty, size })
    }

    pub fn ret(&mut self, value: Option<Value>) {
        self.insert(Instruction::Return { value });
    }

    pub fn iconst(&mut self, value: impl Into<u64>, ty: Type) -> Value {
        self.with_output(|dst| Instruction::Const { dst, imm: value.into(), ty })
    }

    pub fn get_element_ptr(&mut self, source: Value, index: Value) -> Value {
        self.with_output(|dst| Instruction::GetElementPtr { dst, source, index })
    }

    pub fn cast(&mut self, value: Value, ty: Type, cast: Cast) -> Value {
        self.with_output(|dst| Instruction::Cast { dst, cast, value, ty })
    }

    pub fn select(&mut self, cond: Value, on_true: Value, on_false: Value) -> Value {
        self.with_output(|dst| Instruction::Select { dst, cond, on_true, on_false })
    }
}
