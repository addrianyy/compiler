mod display;
mod graph;
mod dump;
mod instruction;
mod instruction_builders;

use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::rc::Rc;

pub use instruction::{UnaryOp, BinaryOp, IntPredicate, Cast};
use instruction::Instruction;
use graph::{FlowGraph, Dominators};

type Map<K, V> = BTreeMap<K, V>;
type Set<T>    = BTreeSet<T>;

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Value(usize);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Function(usize);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Label(usize);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Location(Label, usize);

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

impl Type {
        const U1:  Type = Type { kind: TypeKind::U1,  indirection: 0 };
    pub const U8:  Type = Type { kind: TypeKind::U8,  indirection: 0 };
    pub const U16: Type = Type { kind: TypeKind::U16, indirection: 0 };
    pub const U32: Type = Type { kind: TypeKind::U32, indirection: 0 };
    pub const U64: Type = Type { kind: TypeKind::U64, indirection: 0 };

    pub fn with_indirection(self, indirection: usize) -> Type {
        Self {
            kind:        self.kind,
            indirection: indirection,
        }
    }

    pub fn ptr(self) -> Self {
        assert!(self.kind != TypeKind::U1);

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

    pub fn is_pointer(&self) -> bool {
        self.indirection > 0
    }

    pub fn is_arithmetic(&self) -> bool {
        self.indirection == 0 && self.kind != TypeKind::U1
    }

    pub fn can_be_in_memory(&self) -> bool {
        self.kind != TypeKind::U1
    }

    pub fn is_normal_type(&self) -> bool {
        self.kind != TypeKind::U1
    }

    pub fn size(&self) -> usize {
        if self.is_pointer() {
            return 8;
        }

        match self.kind {
            TypeKind::U1  => panic!("Cannot get size of U1."),
            TypeKind::U8  => 1,
            TypeKind::U16 => 2,
            TypeKind::U32 => 4,
            TypeKind::U64 => 8,
        }
    }
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

struct TypeContext {
    creators:  Map<Value, Location>,
    type_info: TypeInfo,
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

        assert!(!block.is_empty(), "Block {} is empty.", label);

        block[block.len() - 1].targets().unwrap_or_else(|| {
            panic!("Block {} doesn't end in terminator.", label);
        })
    }

    fn value_creators(&self) -> Map<Value, Location> {
        let mut creators = Map::new();

        for label in self.reachable_labels() {
            let body = &self.blocks[&label];

            for (inst_id, inst) in body.iter().enumerate() {
                if let Some(value) = inst.created_value() {
                    creators.insert(value, Location(label, inst_id));
                }
            }
        }

        creators
    }

    fn is_value_argument(&self, value: Value) -> bool {
        self.argument_values.iter().find(|v| **v == value).is_some()
    }

    fn function_prototype(&self, func: Function) -> &FunctionPrototype {
        self.function_info
            .as_ref()
            .expect("Cannot propagate types without CFI.")
            .get(&func)
            .expect("Unknown function is being called.")
    }

    fn infer_value_type(&self, value: Value, cx: &mut TypeContext) -> Type {
        macro_rules! get_type {
            ($value: expr) => {
                self.infer_value_type($value, cx)
            }
        }

        if let Some(&ty) = cx.type_info.get(&value) {
            return ty;
        }

        let creator = cx.creators.get(&value).expect("Value is used without being created.");
        let creator = &self.blocks[&creator.0][creator.1];

        let ty = match creator {
            Instruction::ArithmeticUnary { value, .. } => {
                get_type!(*value)
            }
            Instruction::ArithmeticBinary { a, b, .. } => {
                let a = get_type!(*a);
                let b = get_type!(*b);

                assert!(a == b, "Binary arithmetic instruction must have operands \
                                 of the same type.");

                a
            }
            Instruction::IntCompare { a, b, .. } => {
                let a = get_type!(*a);
                let b = get_type!(*b);

                assert!(a == b, "Int compare instruction must have operands \
                                 of the same type.");
                Type::U1
            }
            Instruction::Load { ptr, .. } => {
                get_type!(*ptr)
                    .strip_ptr()
                    .expect("Cannot load non-pointer value.")
            }
            Instruction::Call { func, .. } => {
                self.function_prototype(*func)
                    .return_type
                    .expect("Void function return value is used.")
                    .clone()
            }
            Instruction::Select { on_true, on_false, .. } => {
                let on_true  = get_type!(*on_true);
                let on_false = get_type!(*on_false);

                assert!(on_true == on_false, "Select instruction must have operands \
                                              of the same type.");

                on_true
            }
            Instruction::StackAlloc    { ty, ..     } => ty.ptr(),
            Instruction::Const         { ty, ..     } => *ty,
            Instruction::GetElementPtr { source, .. } => get_type!(*source),
            Instruction::Cast          { ty, ..     } => *ty,
            _ => {
                panic!("Unexpected value creator: {:?}.", creator);
            }
        };

        assert!(cx.type_info.insert(value, ty).is_none(),
                "Value has type infered multiple times.");
        ty
    }

    fn typecheck(&self, inst: &Instruction, cx: &mut TypeContext) {
        macro_rules! get_type {
            ($value: expr) => {
                self.infer_value_type($value, cx)
            }
        }

        match inst {
            Instruction::ArithmeticUnary { dst, value, .. } => {
                let dst   = get_type!(*dst);
                let value = get_type!(*value);

                assert!(dst == value, "Unary arithmetic instruction requires all \
                        operands to be of the same type");

                assert!(dst.is_arithmetic(), "Unary arithmetic instruction can be \
                        only done on arithmetic types.");
            }
            Instruction::ArithmeticBinary { dst, a, b, .. } => {
                let dst = get_type!(*dst);
                let a   = get_type!(*a);
                let b   = get_type!(*b);

                assert!(dst == a && a == b, "Binary arithmetic instruction requires all \
                        operands to be of the same type");

                assert!(dst.is_arithmetic(), "Binary arithmetic instruction can be \
                        only done on arithmetic types.");
            }
            Instruction::IntCompare { dst, a, b, .. } => {
                let dst = get_type!(*dst);
                let a   = get_type!(*a);
                let b   = get_type!(*b);

                assert!(dst == Type::U1, "Int compare instruction requires \
                        destination type to be U1.");

                assert!(a == b, "Int compare instruction requires all \
                        input operands to be of the same type");

                assert!(a.is_arithmetic() || a == Type::U1, "Int compare instruction can be \
                        only done on arithmetic types or U1.");
            }
            Instruction::Load { dst, ptr } => {
                let dst = get_type!(*dst);
                let ptr = get_type!(*ptr);

                let stripped = ptr.strip_ptr()
                    .expect("Load instruction can only load from pointers.");

                assert!(dst == stripped,
                        "Load instruction destination must have pointee type.");

                assert!(ptr.can_be_in_memory(), "Invalid in-memory type.");
            }
            Instruction::Store { ptr, value } => {
                let ptr   = get_type!(*ptr);
                let value = get_type!(*value);

                let stripped = ptr.strip_ptr()
                    .expect("Store instruction can only store to pointers.");

                assert!(value == stripped,
                        "Store instruction value must have pointee type.");

                assert!(ptr.can_be_in_memory(), "Invalid in-memory type.");
            }
            Instruction::Call { dst, func, args } => {
                let prototype = self.function_prototype(*func);

                if let Some(dst) = dst {
                    let return_type = prototype.return_type
                        .expect("Cannot take the return value of void function.");

                    assert!(get_type!(*dst) == return_type,
                            "Function call return value doesn't match.");
                }

                assert!(args.len() == prototype.arguments.len(), "Function call with invalid \
                        argument count.");

                for (index, arg) in args.iter().enumerate() {
                    assert!(get_type!(*arg) == prototype.arguments[index],
                            "Function call with invalid arguments.");
                }
            }
            Instruction::Branch { .. } => {
            }
            Instruction::BranchCond { value, .. } => {
                let value = get_type!(*value);

                assert!(value == Type::U1, "Conditional branch input must be U1.");
            }
            Instruction::StackAlloc { dst, ty, size } => {
                let dst = get_type!(*dst);

                assert!(*size > 0, "Stack alloc cannot allocate 0 sized array.");
                assert!(dst.strip_ptr().expect("Stack alloc destination must be pointer.") == *ty,
                        "Stack alloc destination must be pointer to input type.");

                assert!(dst.can_be_in_memory(), "Invalid in-memory type.");
            }
            Instruction::Return { value } => {
                let value = value.map(|value| get_type!(value));

                assert!(value == self.prototype.return_type, "Return instruction operand type \
                        must be the same function as function return type.");
            }
            Instruction::Const { dst, ty, .. } => {
                let dst = get_type!(*dst);

                assert!(ty.is_normal_type(), "Only normal types are allowed.");
                assert!(dst == *ty, "Const value instruction operand types must be the same.");
            }
            Instruction::GetElementPtr { dst, source, index } => {
                let dst    = get_type!(*dst);
                let source = get_type!(*source);
                let index  = get_type!(*index);

                assert!(index.is_arithmetic(), "GEP index must be arithmetic.");
                assert!(dst == source, "GEP destination and source must be the same type.");
                assert!(dst.is_pointer() && dst.can_be_in_memory(),
                        "GEP input type is not valid pointer.");
            }
            Instruction::Cast { dst, cast, value, ty } => {
                let dst   = get_type!(*dst);
                let value = get_type!(*value);

                assert!(dst == *ty, "{} destination must be the same type as cast type.", cast);

                match cast {
                    Cast::ZeroExtend | Cast::SignExtend | Cast::Truncate => {
                        assert!(value.is_arithmetic() && ty.is_arithmetic(),
                                "Both types in {} must be arithmetic.", cast);

                        if *cast == Cast::Truncate {
                            assert!(value.size() > ty.size(), "{} must cast from bigger \
                                    integer to smaller one.", cast);
                        } else {
                            assert!(value.size() < ty.size(), "{} must cast from smaller \
                                    integer to bigger one.", cast);
                        }
                    }
                    Cast::Bitcast => {
                        assert!(value.size() == ty.size(), "{} must cast between values \
                                with the same size.", cast);

                        assert!(value.is_normal_type() && ty.is_normal_type(), 
                                "Only normal types are allowed.");
                    }
                }
            }
            Instruction::Select { dst, cond, on_true, on_false } => {
                let dst       = get_type!(*dst);
                let cond      = get_type!(*cond);
                let on_true   = get_type!(*on_true);
                let on_false  = get_type!(*on_false);

                assert!(cond == Type::U1, "Select condition input must be U1.");
                assert!(on_true == on_false && dst == on_true, "Select values and destination \
                        must have the same type.");
            }
        }
    }

    fn build_type_info(&mut self) {
        let mut cx = TypeContext {
            type_info: Map::new(),
            creators:  self.value_creators(),
        };

        for (index, value) in self.argument_values.iter().enumerate() {
            assert!(cx.type_info.insert(*value, self.prototype.arguments[index]).is_none(),
                    "Function arguments defined multiple times.");
        }

        for label in self.reachable_labels() {
            let body = &self.blocks[&label];

            for inst in body {
                if let Some(value) = inst.created_value() {
                    let _ = self.infer_value_type(value, &mut cx);
                }

                for value in inst.read_values() {
                    let _ = self.infer_value_type(value, &mut cx);
                }

                self.typecheck(inst, &mut cx);
            }
        }

        self.type_info = Some(cx.type_info);
    }

    fn validate_ssa(&self) {
        let labels     = self.reachable_labels();
        let dominators = self.dominators();
        let creators   = self.value_creators();

        for &label in &labels {
            let _    = self.targets(label);
            let body = &self.blocks[&label];

            for inst in &body[..body.len() - 1] {
                assert!(inst.targets().is_none(), "Terminator {:?} in the middle of block {}.",
                        inst, label);
            }

            for (inst_id, inst) in body.iter().enumerate() {
                for value in inst.read_values() {
                    if self.is_value_argument(value) {
                        continue;
                    }

                    let creation_loc = *creators.get(&value).expect("Value used but not created.");
                    let usage_loc    = Location(label, inst_id);

                    assert!(self.validate_path(&dominators, creation_loc, usage_loc),
                            "Value {} is used before being created.", value);
                }
            }
        }
    }

    fn finalize(&mut self) {
        assert!(self.prototype.return_type != Some(Type::U1),
                "Functions cannot return U1.");

        self.validate_ssa();
        self.build_type_info();
    }

    fn validate_path(&self, dominators: &Dominators, start: Location, end: Location) -> bool {
        let start_label = start.0;
        let end_label   = end.0;

        if start_label == end_label {
            return start.1 < end.1;
        }

        self.dominates(dominators, start_label, end_label)
    }

    fn dominates(&self, dominators: &Dominators, dominator: Label, target: Label) -> bool {
        let mut current = Some(target);

        while let Some(idom) = current {
            if idom == dominator {
                return true;
            }

            current = dominators.get(&idom).copied();
        }

        false
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
