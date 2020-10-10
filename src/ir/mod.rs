mod display;
mod graph;
mod dump;

use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::rc::Rc;

type Map<K, V> = BTreeMap<K, V>;
type Set<T>    = BTreeSet<T>;

use graph::FlowGraph;

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Value(usize);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Function(usize);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Label(usize);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum TypeKind {
    U1,
    U8,
    U16,
    U32,
    U64,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Type {
    kind:        TypeKind,
    indirection: usize,
}

macro_rules! type_constructor {
    ($name: ident, $kind: expr) => {
        pub fn $name() -> Self {
            Self {
                kind:        $kind,
                indirection: 0,
            }
        }
    }
}

impl Type {
    type_constructor!(make_u8,  TypeKind::U8);
    type_constructor!(make_u16, TypeKind::U16);
    type_constructor!(make_u32, TypeKind::U32);
    type_constructor!(make_u64, TypeKind::U64);

    pub fn ptr(self) -> Self {
        Self {
            kind:        self.kind,
            indirection: self.indirection + 1,
        }
    }

    pub fn strip_ptr(self) -> Option<Self> {
        Some(Self {
            kind:        self.kind,
            indirection: self.indirection.checked_sub(1)?,
        })
    }
}

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

enum Instruction {
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
}

type BasicBlock         = Vec<Instruction>;
type CrossFunctionInfo  = Rc<Map<Function, Rc<FunctionPrototype>>>;
type TypeInfo           = Map<Value, Type>;

struct FunctionPrototype {
    name:        String,
    return_type: Option<Type>,
    arguments:   Vec<Type>,
}

struct FunctionData {
    prototype:       Rc<FunctionPrototype>,
    argument_values: Vec<Value>,
    blocks:          Map<Label, BasicBlock>,
    next_value:      Value,
    next_label:      Label,
    function_info:   Option<CrossFunctionInfo>,
    type_info:       Option<TypeInfo>,
}

impl FunctionData {
    fn new(name: String, return_type: Option<Type>, arguments: Vec<Type>) -> Self {
        let argument_count = arguments.len();

        let prototype = Rc::new(FunctionPrototype {
            name,
            return_type,
            arguments,
        });

        let mut data = Self {
            prototype,
            argument_values: vec![Value(0); argument_count],
            blocks:          Map::new(),
            next_value:      Value(0),
            next_label:      Label(0),
            function_info:   None,
            type_info:       None,
        };

        let entry = data.allocate_label();

        for index in 0..argument_count {
            data.argument_values[index] = data.allocate_value();
        }

        data
    }

    fn allocate_label(&mut self) -> Label {
        let label = self.next_label;

        self.next_label = Label(label.0.checked_add(1)
                                .expect("Label IDs overflowed."));

        assert!(self.blocks.insert(label, Vec::new()).is_none(), 
                "Multiple labels with the same ID ({}).", label.0);

        label
    }

    fn allocate_value(&mut self) -> Value {
        let value = self.next_value;

        self.next_value = Value(value.0.checked_add(1)
                                .expect("Value IDs overflowed."));

        value
    }

    fn insert(&mut self, label: Label, instruction: Instruction) {
        self.blocks.get_mut(&label)
            .expect("Invalid insertion label.")
            .push(instruction);
    }

    fn targets(&self, label: Label) -> Vec<Label> {
        let block = &self.blocks[&label];

        match &block[block.len() - 1] {
            Instruction::Return     { .. }                    => vec![],
            Instruction::Branch     { target }                => vec![*target],
            Instruction::BranchCond { on_true, on_false, .. } => vec![*on_true, *on_false],
            _ => {
                panic!("Block {} doesn't end in terminator.", label);
            }
        }
    }

    fn finalize(&mut self) {
    }
}

#[derive(Copy, Clone)]
pub struct ActivePoint {
    function: Function,
    label:    Label,
}

pub struct Module {
    functions:     Map<Function, FunctionData>,
    active_point:  Option<ActivePoint>,
    next_function: Function,
    finalized:     bool,
}

impl Module {
    pub fn new() -> Self {
        Self {
            functions:     Map::new(),
            active_point:  None,
            next_function: Function(0),
            finalized:     false,
        }
    }

    pub fn create_function(&mut self, name: &str, return_type: Option<Type>,
                           arguments: Vec<Type>) -> Function {
        let data     = FunctionData::new(name.to_string(), return_type, arguments);
        let function = self.next_function;

        self.next_function = Function(function.0.checked_add(1)
                                      .expect("Function IDs overflowed."));

        assert!(self.functions.insert(function, data).is_none(), 
                "Multiple functions with the same ID ({}).", function.0);

        function
    }

    pub fn create_label(&mut self) -> Label {
        self.function_mut(self.active_point().function).allocate_label()
    }

    fn function(&self, function: Function) -> &FunctionData {
        self.functions.get(&function).expect("Invalid function.")
    }

    fn function_mut(&mut self, function: Function) -> &mut FunctionData {
        self.functions.get_mut(&function).expect("Invalid function.")
    }

    fn active_point(&self) -> ActivePoint {
        self.active_point.expect("Invalid active point specified.")
    }

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

    pub fn argument(&self, index: usize) -> Value {
        self.function(self.active_point().function).argument_values[index]
    }

    pub fn switch_label(&mut self, label: Label) {
        let point = self.active_point.as_mut()
            .expect("Tried to switch labels without active point.");

        point.label = label;
    }

    pub fn switch_function(&mut self, function: Function) {
        self.active_point = Some(ActivePoint {
            function,
            label: Label(0),
        });
    }

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
        match self.function(func).prototype.return_type.is_some() {
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

    pub fn finalize(&mut self) {
        assert!(!self.finalized, "Cannot finalize module multiple times.");

        let mut function_info = Map::new();

        for (function, data) in &self.functions {
            assert!(function_info.insert(*function, data.prototype.clone()).is_none(), 
                    "Multiple functions with the same ID.");
        }

        let function_info = Rc::new(function_info);

        for data in self.functions.values_mut() {
            data.function_info = Some(function_info.clone());
            data.finalize();
        }

        self.finalized = true;
    }

    pub fn dump_function_graph(&self, function: Function, path: &str) {
        self.function(function).dump_graph(path)
    }

    pub fn dump_function_text<W: Write>(&self, function: Function, w: &mut W) -> io::Result<()> {
        self.function(function).dump_text(w)
    }
}
