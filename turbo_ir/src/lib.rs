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
mod collections;
mod phi_updater;
mod dot;

use std::time::Instant;
use std::io::{self, Write};
use std::rc::Rc;

pub use ty::Type;
pub use instruction::{UnaryOp, BinaryOp, IntPredicate, Cast};
pub use codegen::MachineCode;
use instruction::Instruction;
use phi_updater::PhiUpdater;
use analysis::ConstType;
use codegen::Backend;
use graph::Dominators;
use graph::FlowGraph;
use collections::{Map, Set, LargeKeyMap, CapacityExt};

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Value(u32);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Function(u32);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Label(u32);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Location {
    location_label: Label,
    location_index: u32,
}

impl Value {
    fn index(&self) -> usize {
        self.0 as usize
    }
}

impl Location {
    fn new(label: Label, index: usize) -> Self {
        use std::convert::TryInto;

        Self {
            location_label: label,
            location_index: index.try_into().expect("Index doesn't fit in U32."),
        }
    }

    fn label(&self) -> Label {
        self.location_label
    }

    fn index(&self) -> usize {
        self.location_index as usize
    }
}

type BasicBlock = Vec<Instruction>;
type TypeInfo   = Map<Value, Type>;

struct CrossFunctionInfo {
    info:    Map<Function, Rc<FunctionPrototype>>,
    externs: Map<Function, usize>,
}

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
    function_info:   Option<Rc<CrossFunctionInfo>>,
    type_info:       Option<TypeInfo>,
    phi_locations:   Map<Value, Location>,
}

impl FunctionData {
    fn new(prototype: Rc<FunctionPrototype>) -> Self {
        let argument_count = prototype.arguments.len();

        let mut data = Self {
            prototype,
            argument_values: vec![Value(0); argument_count],
            blocks:          Map::default(),
            next_value:      Value(0),
            next_label:      Label(0),
            function_info:   None,
            type_info:       None,
            phi_locations:   Map::default(),
        };

        data.allocate_label();

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
        let block    = self.blocks.get_mut(&label).expect("Invalid insertion label.");
        let position = block.len();

        if let Instruction::Phi { dst, .. } = instruction {
            self.phi_locations.insert(dst, Location::new(label, position));
        }

        block.push(instruction);
    }

    fn targets(&self, label: Label) -> Vec<Label> {
        let block = &self.blocks[&label];

        assert!(!block.is_empty(), "Block {} is empty.", label);

        block[block.len() - 1].targets().unwrap_or_else(|| {
            panic!("Block {} doesn't end in terminator.", label);
        })
    }

    fn last_instruction(&self, label: Label) -> &Instruction {
        let block = &self.blocks[&label];

        &block[block.len() - 1]
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
            .info
            .get(&func)
            .expect("Unknown function is being called.")
    }

    fn finalize(&mut self) {
        self.validate_ssa();
        self.build_type_info();
    }

    fn optimize(&mut self) {
        #[derive(Debug, Default, Clone)]
        struct PassStatistics {
            time:      f64,
            successes: u32,
        }

        let passes: &[&dyn passes::Pass]  = &[
            &passes::ConstPropagatePass,
            &passes::RemoveIneffectiveOperationsPass,
            &passes::SimplifyCFGPass,
            &passes::SimplifyComparesPass,
            &passes::SimplifyExpressionsPass,
            &passes::RemoveDeadCodePass,

            /*
            &passes::DeduplicatePass,
            &passes::RemoveKnownLoadsPass,
            &passes::RemoveDeadStoresPass,
            */

            &passes::RemoveAliasesPass,
            &passes::RemoveNopsPass,


            // Architecture specific reorder pass must be after generic reorder pass.
            &passes::ReorderPass,
            &passes::X86ReorderPass,
        ];

        let mut statistics = vec![PassStatistics::default(); passes.len()];
        let mut iterations = 0;

        let start = Instant::now();

        loop {
            let mut did_something = false;

            for (index, pass) in passes.iter().enumerate() {
                let start   = Instant::now();
                let success = pass.run_on_function(self);
                let elapsed = start.elapsed().as_secs_f64();

                did_something |= success;

                let statistics = &mut statistics[index];

                statistics.successes += success as u32;
                statistics.time      += elapsed;
            }

            iterations += 1;

            if !did_something {
                break;
            }
        }

        let elapsed = start.elapsed().as_secs_f64();

        if true && !passes.is_empty() {
            println!("Optimized {} in {} iterations and {}s.", self.prototype.name, 
                     iterations, elapsed);

            statistics.sort_by(|a, b| b.time.partial_cmp(&a.time).unwrap());

            let mut longest_pass_name = None;
            let mut total_passes_time = 0.0;

            for (index, pass) in passes.iter().enumerate() {
                let name       = pass.name();
                let statistics = &statistics[index];

                let is_longer = match longest_pass_name {
                    Some(other) => name.len() > other,
                    None        => true
                };

                if is_longer {
                    longest_pass_name = Some(name.len());
                }

                total_passes_time += statistics.time;
            }

            let longest_pass_name = longest_pass_name.expect("Failed to get longest pass name.");

            for (index, pass) in passes.iter().enumerate() {
                let name       = pass.name();
                let statistics = &statistics[index];

                print!("{} ", name);

                for _ in 0..(longest_pass_name - name.len()) {
                    print!(" ");
                }

                println!("| {:>2} successes | {:>8.4} ms elapsed [{:>6.2}%]",
                         statistics.successes,
                         statistics.time * 1000.0,
                         (statistics.time / total_passes_time) * 100.0);
            }

            println!();
        }

        self.validate_ssa();
    }

    fn value_count(&self) -> usize {
        self.next_value.0 as usize
    }

    fn add_phi_incoming(&mut self, phi: Value, label: Label, value: Value) {
        let location = self.phi_locations[&phi];

        if let Instruction::Phi { incoming, .. } = self.instruction_mut(location) {
            let duplicate = incoming.iter().any(|(used_label, _)| *used_label == label);
            if  duplicate {
                panic!("Cannot add multiple incoming values from the same label.");
            }

            incoming.push((label, value));
        } else {
            panic!("Cannot add incoming value to non-phi value.");
        }
    }
}

#[derive(Copy, Clone)]
pub struct ActivePoint {
    function: Function,
    label:    Label,
}

enum FunctionInternal {
    Local(FunctionData),
    Extern {
        prototype: Rc<FunctionPrototype>,
        address:   usize,
    },
}

impl FunctionInternal {
    fn unwrap_local(&self) -> &FunctionData {
        match self {
            FunctionInternal::Local(data) => {
                data
            }
            _ => {
                panic!("Tried to use extern function.");
            }
        }
    }

    fn unwrap_local_mut(&mut self) -> &mut FunctionData {
        match self {
            FunctionInternal::Local(data) => {
                data
            }
            _ => {
                panic!("Tried to use extern function.");
            }
        }
    }

    fn prototype(&self) -> &Rc<FunctionPrototype> {
        match self {
            FunctionInternal::Local(data) => {
                &data.prototype
            }
            FunctionInternal::Extern { prototype, .. } => {
                prototype
            }
        }
    }
}

pub struct Module {
    functions:     Map<Function, FunctionInternal>,
    active_point:  Option<ActivePoint>,
    next_function: Function,
    finalized:     bool,
}

impl Default for Module {
    fn default() -> Self {
        Self::new()
    }
}

impl Module {
    pub fn new() -> Self {
        Self {
            functions:     Map::default(),
            active_point:  None,
            next_function: Function(0),
            finalized:     false,
        }
    }

    fn function_prototype(&self, function: Function) -> &FunctionPrototype {
        self.functions.get(&function)
            .expect("Invalid function.")
            .prototype()
    }

    fn function(&self, function: Function) -> &FunctionData {
        self.functions.get(&function)
            .expect("Invalid function.")
            .unwrap_local()
    }

    fn function_mut(&mut self, function: Function) -> &mut FunctionData {
        self.functions.get_mut(&function)
            .expect("Invalid function.")
            .unwrap_local_mut()
    }

    fn active_point(&self) -> ActivePoint {
        self.active_point.expect("No active point specified.")
    }

    #[track_caller]
    unsafe fn create_function_internal(&mut self, name: &str, return_type: Option<Type>, 
                                       arguments: Vec<Type>, address: Option<usize>) -> Function {
        assert!(!self.finalized, "Cannot create functions after finalization.");

        let prototype = Rc::new(FunctionPrototype {
            name: name.to_string(),
            return_type,
            arguments,
        });

        let internal = match address {
            Some(address) => {
                FunctionInternal::Extern {
                    prototype,
                    address,
                }
            }
            None => {
                FunctionInternal::Local(FunctionData::new(prototype))
            }
        };

        let function = self.next_function;

        self.next_function = Function(function.0.checked_add(1)
                                      .expect("Function IDs overflowed."));

        assert!(self.functions.insert(function, internal).is_none(), 
                "Multiple functions with the same ID ({}).", function.0);

        function
    }

    pub fn create_function(&mut self, name: &str, return_type: Option<Type>, 
                           arguments: Vec<Type>) -> Function {
        unsafe {
            self.create_function_internal(name, return_type, arguments, None)
        }
    }

    #[allow(clippy::missing_safety_doc)]
    pub unsafe fn create_external_function(&mut self, name: &str, return_type: Option<Type>,
                                           arguments: Vec<Type>, address: usize) -> Function {
        self.create_function_internal(name, return_type, arguments, Some(address))
    }

    pub fn create_label(&mut self) -> Label {
        assert!(!self.finalized, "Cannot create labels after finalization.");

        self.function_mut(self.active_point().function).allocate_label()
    }

    pub fn add_phi_incoming(&mut self, phi: Value, label: Label, value: Value) {
        self.function_mut(self.active_point().function)
            .add_phi_incoming(phi, label, value);
    }

    pub fn is_terminated(&self, label: Option<Label>) -> bool {
        let point = self.active_point();
        let label = label.unwrap_or(point.label);

        self.function(point.function).is_terminated(label)
    }

    pub fn argument(&self, index: usize) -> Value {
        self.function(self.active_point().function).argument_values[index]
    }

    pub fn switch_function(&mut self, function: Function) {
        self.active_point = Some(ActivePoint {
            function,
            label: Label(0),
        });
    }

    pub fn switch_label(&mut self, label: Label) {
        let point = self.active_point.as_mut()
            .expect("Tried to switch labels without active point.");

        point.label = label;
    }

    pub fn finalize(&mut self) {
        assert!(!self.finalized, "Cannot finalize module multiple times.");

        let mut function_info = Map::default();
        let mut externs       = Map::default();

        for (function, internal) in &self.functions {
            assert!(function_info.insert(*function, internal.prototype().clone()).is_none(), 
                    "Multiple functions with the same ID.");

            if let FunctionInternal::Extern { address, .. } = internal {
                assert!(externs.insert(*function, *address).is_none(),
                        "Multiple functions with the same ID.");
            }
        }

        let cfi = Rc::new(CrossFunctionInfo {
            info: function_info,
            externs,
        });

        for internal in self.functions.values_mut() {
            if let FunctionInternal::Local(data) = internal {
                data.function_info = Some(cfi.clone());
                data.finalize();
            }
        }

        self.finalized = true;
    }

    pub fn entry_label(&self) -> Label {
        Label(0)
    }

    pub fn dump_function_graph(&self, function: Function, path: &str) {
        self.function(function).dump_graph(path)
    }

    pub fn dump_function_text<W: Write>(&self, function: Function, w: &mut W) -> io::Result<()> {
        self.function(function).dump_text(w)
    }

    pub fn optimize(&mut self) {
        assert!(self.finalized, "Cannot optimize before finalization.");

        for internal in self.functions.values_mut() {
            if let FunctionInternal::Local(data) = internal {
                data.optimize();
            }
        }
    }

    pub fn generate_machine_code(&mut self) -> MachineCode {
        assert!(self.finalized, "Cannot generate machine code before finalization.");

        let mut backend = codegen::x86backend::X86Backend::new(self);

        for (function, internal) in &mut self.functions {
            if let FunctionInternal::Local(data) = internal {
                backend.generate_function(*function, data);
            }
        }

        let (buffer, functions) = backend.finalize();

        MachineCode::new(&buffer, functions)
    }
}
