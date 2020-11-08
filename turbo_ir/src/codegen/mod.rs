pub mod x86backend;
mod executable_memory;
mod register_allocation;

use crate::{Function, FunctionData, Module, Map, Instruction, Value};
use executable_memory::ExecutableMemory;
use register_allocation::RegisterAllocation;

pub type FunctionMCodeMap = Map<Function, (usize, usize)>;

pub(super) trait Backend {
    fn new(ir: &Module) -> Self where Self: Sized;
    fn hardware_registers(&self) -> usize;
    fn can_inline_constant(&self, function: &FunctionData, value: Value, constant: i64,
                           users: &[&Instruction]) -> bool;
    fn generate_function(&mut self, function: Function, data: &FunctionData,
                         register_allocation: RegisterAllocation);
    fn finalize(self) -> (Vec<u8>, FunctionMCodeMap);
}

pub struct MachineCode {
    buffer:    ExecutableMemory,
    functions: FunctionMCodeMap,
}

impl MachineCode {
    pub(super) fn new(buffer: &[u8], functions: FunctionMCodeMap) -> Self {
        let buffer = ExecutableMemory::from_buffer(&buffer);

        Self {
            buffer,
            functions,
        }
    }

    pub fn function_buffer(&self, function: Function) -> &[u8] {
        let (offset, size) = *self.functions.get(&function)
            .expect("Invalid function specified.");

        &self.buffer[offset..][..size]
    }

    #[allow(clippy::missing_safety_doc)]
    pub unsafe fn function_ptr<T: Copy>(&self, function: Function) -> T {
        assert_eq!(std::mem::size_of::<T>(), std::mem::size_of::<usize>(),
                   "Function pointer must have pointer size.");

        let ptr = self.function_buffer(function).as_ptr();

        *(&ptr as *const _ as *const T)
    }
}

pub(super) fn allocate_registers(function: &mut FunctionData, backend: &dyn Backend)
    -> RegisterAllocation
{
    function.allocate_registers(backend)
}
