mod display;
mod graph;
mod dump;
mod instruction;
mod instruction_builders;
mod codegen;
mod ty;
mod analysis;
mod type_inference;
mod register_allocation;
mod passes;

use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::rc::Rc;

pub use ty::Type;
pub use instruction::{UnaryOp, BinaryOp, IntPredicate, Cast};
pub use codegen::MachineCode;
use instruction::Instruction;
use codegen::Backend;
use graph::Dominators;

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Value(usize);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Function(usize);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Label(usize);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Location(Label, usize);

type Map<K, V> = BTreeMap<K, V>;
type Set<T>    = BTreeSet<T>;

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

        let _entry = data.allocate_label();

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

    fn is_terminated(&self, label: Label) -> bool {
        let block = &self.blocks[&label];

        if block.is_empty() {
            return false;
        }

        block[block.len() - 1].targets().is_some()
    }

    fn value_type(&self, value: Value) -> Type {
        self.type_info.as_ref().unwrap()[&value]
    }

    fn is_value_argument(&self, value: Value) -> bool {
        self.argument_values.iter().any(|v| *v == value)
    }

    fn function_prototype(&self, func: Function) -> &FunctionPrototype {
        self.function_info
            .as_ref()
            .expect("Cannot propagate types without CFI.")
            .get(&func)
            .expect("Unknown function is being called.")
    }

    fn finalize(&mut self) {
        assert!(self.prototype.return_type != Some(Type::U1),
                "Functions cannot return U1.");

        self.validate_ssa();
        self.build_type_info();
    }

    fn optimize(&mut self) {
        let passes: &[Box<dyn passes::Pass>]  = &[
            Box::new(passes::TestPass),
            Box::new(passes::RemoveDeadCodePass),
            Box::new(passes::RemoveAliasesPass),
            Box::new(passes::RemoveNopsPass),
        ];

        loop {
            let mut did_something = false;

            for pass in passes {
                did_something |= pass.run_on_function(self)
            }

            if !did_something {
                break;
            }
        }

        self.validate_ssa();
    }

    pub(super) fn value_count(&self) -> usize {
        self.next_value.0
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

    pub fn is_terminated(&self, label: Option<Label>) -> bool {
        let point = self.active_point();
        let label = label.unwrap_or(point.label);

        self.function(point.function).is_terminated(label)
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
        self.active_point.expect("No active point specified.")
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

    #[allow(unused)]
    pub fn dump_function_graph(&self, function: Function, path: &str) {
        self.function(function).dump_graph(path)
    }

    #[allow(unused)]
    pub fn dump_function_text<W: Write>(&self, function: Function, w: &mut W) -> io::Result<()> {
        self.function(function).dump_text(w)
    }

    pub fn optimize(&mut self) {
        for data in self.functions.values_mut() {
            data.optimize();
        }
    }

    pub fn generate_machine_code(&self) -> MachineCode {
        let mut backend = codegen::x86backend::X86Backend::new(self);

        for (function, data) in &self.functions {
            backend.generate_function(*function, data);
        }

        let (buffer, functions) = backend.finalize();

        MachineCode::new(&buffer, functions)
    }
}
