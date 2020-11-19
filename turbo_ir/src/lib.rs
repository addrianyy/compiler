#[macro_use] mod timing;

mod instruction_builders;
mod type_inference;
mod instruction;
mod collections;
mod phi_updater;
mod analysis;
mod codegen;
mod display;
mod parser;
mod graph;
mod dump;
mod dot;
mod ty;

pub mod passes;

use std::time::Instant;
use std::io::{self, Write};
use std::rc::Rc;

pub use ty::Type;
pub use instruction::{UnaryOp, BinaryOp, IntPredicate, Cast};
pub use codegen::MachineCode;
pub use codegen::backends;
use instruction::Instruction;
use phi_updater::PhiUpdater;
use analysis::{ConstType, ValidationCache};
use graph::Dominators;
use graph::FlowGraph;
use passes::Pass;
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

pub struct FunctionPrototype {
    pub name:        String,
    pub return_type: Option<Type>,
    pub arguments:   Vec<Type>,
}

struct FunctionData {
    prototype: Rc<FunctionPrototype>,
    blocks:    Map<Label, BasicBlock>,

    argument_values: Vec<Value>,
    argument_set:    Set<Value>,

    undefined:     Map<Type, Value>,
    undefined_set: Set<Value>,

    next_value: Value,
    next_label: Label,
    entry:      Label,

    type_info:     Option<TypeInfo>,
    function_info: Option<Rc<CrossFunctionInfo>>,

    phi_locations: Map<Value, Location>,
}

impl FunctionData {
    fn new(prototype: Rc<FunctionPrototype>) -> Self {
        let argument_count = prototype.arguments.len();

        let mut data = Self {
            prototype,
            blocks: Map::default(),

            argument_values: vec![Value(0); argument_count],
            argument_set:    Set::default(),

            undefined:     Map::default(),
            undefined_set: Set::default(),

            next_value: Value(0),
            next_label: Label(0),
            entry:      Label(0),

            type_info:     None,
            function_info: None,

            phi_locations: Map::default(),
        };

        data.entry = data.allocate_label();

        for index in 0..argument_count {
            let value = data.allocate_value();

            data.argument_values[index] = value;
            data.argument_set.insert(value);
        }

        data
    }

    fn entry(&self) -> Label {
        self.entry
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

    fn allocate_typed_value(&mut self, ty: Type) -> Value {
        let value = self.allocate_value();

        self.type_info.as_mut()
            .expect("Cannot allocate typed value without typeinfo.")
            .insert(value, ty);

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

        assert!(!block.is_empty(), "Block {} is empty.", label);

        &block[block.len() - 1]
    }

    fn is_terminated(&self, label: Label) -> bool {
        let block = &self.blocks[&label];

        if block.is_empty() {
            return false;
        }

        block[block.len() - 1].targets().is_some()
    }

    fn undefined_value(&mut self, ty: Type) -> Value {
        if let Some(&value) = self.undefined.get(&ty) {
            return value;
        }

        let value = self.allocate_value();

        if let Some(type_info) = self.type_info.as_mut() {
            type_info.insert(value, ty);
        }

        self.undefined.insert(ty, value);
        self.undefined_set.insert(value);

        value
    }

    fn value_type(&self, value: Value) -> Type {
        self.type_info.as_ref().unwrap()[&value]
    }

    fn is_value_special(&self, value: Value) -> bool {
        self.argument_set.contains(&value) || self.undefined_set.contains(&value)
    }

    fn is_value_undefined(&self, value: Value) -> bool {
        self.undefined_set.contains(&value)
    }

    fn function_prototype(&self, function: Function) -> &FunctionPrototype {
        self.function_info
            .as_ref()
            .expect("Cannot propagate types without CFI.")
            .info
            .get(&function)
            .expect("Unknown function is being called.")
    }

    fn finalize(&mut self) {
        self.phi_locations.clear();

        self.validate_ssa();
        self.build_type_info();
    }

    fn optimize(&mut self, passes: &[passes::IRPass], show_statistics: bool) {
        time!(optimize);

        #[derive(Debug, Default, Clone)]
        struct PassStatistics {
            time:      f64,
            successes: u32,
            index:     usize,
        }

        if passes.is_empty() {
            return;
        }

        {
            // Make sure that there are not duplicate passes.
            let mut pass_names = Set::new_with_capacity(passes.len());

            for pass in passes {
                assert!(pass_names.insert(pass.inner.name()), "Multiple {} passes.",
                        pass.inner.name());
            }
        }

        let default_passes: &[&dyn Pass] = &[
            &passes::RemoveAliasesPass,
            &passes::RemoveNopsPass,
        ];

        let mut statistics = vec![PassStatistics::default(); passes.len()];
        let mut iterations = 0;

        let start = Instant::now();

        loop {
            let mut did_something = false;

            for (index, pass) in passes.iter().enumerate() {
                let start   = Instant::now();
                let success = pass.inner.run_on_function(self);
                let elapsed = start.elapsed().as_secs_f64();

                did_something |= success;

                let statistics = &mut statistics[index];

                statistics.successes += success as u32;
                statistics.time      += elapsed;
                statistics.index      = index;
            }

            {
                time!(default_passes);

                for pass in default_passes {
                    did_something |= pass.run_on_function(self);
                }
            }

            iterations += 1;

            if !did_something {
                break;
            }
        }

        let elapsed = start.elapsed().as_secs_f64();

        if show_statistics && !passes.is_empty() {
            println!("Optimized {} in {} iterations and {}s.", self.prototype.name,
                     iterations, elapsed);

            statistics.sort_by(|a, b| b.time.partial_cmp(&a.time).unwrap());

            let mut longest_pass_name = None;
            let mut total_passes_time = 0.0;

            for statistics in &statistics {
                let name = passes[statistics.index].inner.name();

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

            for statistics in &statistics {
                let name = passes[statistics.index].inner.name();

                print!("{} ", name);

                for _ in 0..(longest_pass_name - name.len()) {
                    print!(" ");
                }

                println!("| {:>3} successes | {:>15.4} ms elapsed [{:>6.2}%]",
                         statistics.successes,
                         statistics.time * 1000.0,
                         (statistics.time / total_passes_time) * 100.0);
            }

            println!();
        }

        // Cleanup unreachable blocks.
        let reachable = self.reachable_labels();
        self.blocks.retain(|label, _| reachable.iter().any(|x| x == label));

        self.validate_ssa();

        {
            time!(rewrite_values);

            // Rewrite IR values for cleaner look.
            // TODO: Maybe we should do this only in debug mode.
            passes::RewriteValuesPass.run_on_function(self);
        }
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
            FunctionInternal::Local(data) => data,
            _ => panic!("Tried to use extern function."),
        }
    }

    fn unwrap_local_mut(&mut self) -> &mut FunctionData {
        match self {
            FunctionInternal::Local(data) => data,
            _ => panic!("Tried to use extern function."),
        }
    }

    fn prototype(&self) -> &Rc<FunctionPrototype> {
        match self {
            FunctionInternal::Local(data)              => &data.prototype,
            FunctionInternal::Extern { prototype, .. } => prototype,
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
        timing::register_exit_callback();

        Self {
            functions:     Map::default(),
            active_point:  None,
            next_function: Function(0),
            finalized:     false,
        }
    }

    pub fn parse_from_source(source: &str) -> Self {
        parser::parse(source)
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
        assert!(!self.finalized, "Cannot modify PHI incoming values after finalization.");

        self.function_mut(self.active_point().function)
            .add_phi_incoming(phi, label, value);
    }

    pub fn switch_function(&mut self, function: Function) {
        let entry = self.function(function).entry();

        self.active_point = Some(ActivePoint {
            function,
            label: entry,
        });
    }

    pub fn switch_label(&mut self, label: Label) {
        let point = self.active_point.as_mut()
            .expect("Tried to switch labels without active point.");

        point.label = label;
    }

    pub fn entry_label(&self) -> Label {
        self.function(self.active_point().function).entry()
    }

    pub fn argument(&self, index: usize) -> Value {
        self.function(self.active_point().function).argument_values[index]
    }

    pub fn is_terminated(&self, label: Option<Label>) -> bool {
        let point = self.active_point();
        let label = label.unwrap_or(point.label);

        self.function(point.function).is_terminated(label)
    }

    pub fn dump_function_graph(&self, function: Function, path: &str) {
        self.function(function).dump_graph(path)
    }

    pub fn dump_function_text<W: Write>(&self, function: Function, w: &mut W) -> io::Result<()> {
        self.function(function).dump_text(w)
    }

    pub fn dump_function_text_stdout(&self, function: Function) {
        self.function(function).dump_text_stdout()
    }

    pub fn for_each_local_function<F>(&self, mut callback: F)
        where F: FnMut(&FunctionPrototype, Function)
    {
        for (function, internal) in &self.functions {
            if let FunctionInternal::Local(data) = internal {
                let prototype = &data.prototype;

                callback(prototype, *function);
            }
        }
    }

    pub fn finalize(&mut self) {
        time!(finalize);

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

    pub fn optimize(&mut self, passes: &[passes::IRPass], show_statistics: bool) {
        assert!(self.finalized, "Cannot optimize before finalization.");

        for internal in self.functions.values_mut() {
            if let FunctionInternal::Local(data) = internal {
                data.optimize(passes, show_statistics);
            }
        }
    }

    pub fn generate_machine_code(&mut self, backend: &dyn backends::IRBackend) -> MachineCode {
        assert!(self.finalized, "Cannot generate machine code before finalization.");

        let mut backend = backend.create(self);

        // Generate machine code for each function.
        // Register allocator will add additional `alias` instructions to handle PHIs.
        for (function, internal) in &mut self.functions {
            if let FunctionInternal::Local(data) = internal {
                let register_allocation = codegen::allocate_registers(data, backend.get());

                backend.get_mut().generate_function(*function, data, register_allocation);
            }
        }

        let (buffer, functions) = backend.finalize();

        {
            time!(codegen_cleanup);

            // Run passes that will remove `alias` instructions created by register allocator.
            for internal in self.functions.values_mut() {
                if let FunctionInternal::Local(data) = internal {
                    passes::RemoveAliasesPass.run_on_function(data);
                    passes::RemoveNopsPass.run_on_function(data);
                }
            }
        }

        MachineCode::new(&buffer, functions)
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
}
