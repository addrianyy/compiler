pub mod x86backend;
mod execmem;

use super::{Function, FunctionData, Module, Map};
use execmem::ExecutableMemory;

pub type FunctionMCodeMap = Map<Function, (usize, usize)>;

pub(super) trait Backend {
    fn new(ir: &Module) -> Self;
    fn generate_function(&mut self, function: Function, data: &FunctionData);
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
            .expect("Invalid function specified");

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
