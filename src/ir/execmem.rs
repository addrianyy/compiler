use std::ops::{Deref, DerefMut};

#[cfg(windows)]
fn allocate_rwx(size: usize) -> *mut u8  {
    extern "system" {
        fn VirtualAlloc(base: *mut u8, size: usize, alloc_type: u32, prot: u32) -> *mut u8;
    }

    const MEM_COMMIT_RESERVE:     u32 = 0x1000 | 0x2000;
    const PAGE_EXECUTE_READWRITE: u32 = 0x40;

    let prot = PAGE_EXECUTE_READWRITE;

    let result  = unsafe { 
        VirtualAlloc(std::ptr::null_mut(), size, MEM_COMMIT_RESERVE, prot)
    };

    let success = !result.is_null();

    assert!(success, "Allocating memory with size of {} bytes failed.", size);

    result
}

#[cfg(unix)]
fn allocate_rwx(size: usize) -> *mut u8  {
    extern "system" {
        fn mmap(base: *mut u8, size: usize, prot: u32, flags: u32,
            fd: u32, offset: usize) -> *mut u8;
    }

    const MAP_PRIVATE_ANONYMOUS: u32 = 0x02 | 0x20;

    const PROT_READ:  u32 = 1;
    const PROT_WRITE: u32 = 2;
    const PROT_EXEC:  u32 = 4;

    let prot = PROT_READ | PROT_WRITE | PROT_EXEC;

    let result = unsafe {
        mmap(std::ptr::null_mut(), size, prot, MAP_PRIVATE_ANONYMOUS, 1u32.wrapping_neg(), 0)
    };

    let success = !result.is_null() && result as isize > 0;

    assert!(success, "Allocating memory with size of {} bytes failed.", size);

    result
}

#[cfg(windows)]
unsafe fn free_rwx(base: *mut u8, _size: usize) {
    extern "system" {
        fn VirtualFree(base: *mut u8, size: usize, free_type: u32) -> u32;
    }

    const MEM_RELEASE: u32 = 0x8000;

    let result = VirtualFree(base, 0, MEM_RELEASE);

    assert!(result != 0, "Freeing memory at addresss {:p} failed.", base);
}

#[cfg(unix)]
unsafe fn free_rwx(base: *mut u8, size: usize) {
    extern "system" {
        fn munmap(base: *mut u8, size: usize) -> i32;
    }

    let result = munmap(base, size);

    assert!(result == 0, "Freeing memory at addresss {:p} failed.", base);
}

pub struct ExecutableMemory {
    base: *mut u8,
    size: usize,
}

unsafe impl Send for ExecutableMemory {}
unsafe impl Sync for ExecutableMemory {}

impl ExecutableMemory {
    pub fn new(size: usize) -> Self {
        let base = allocate_rwx(size);

        Self {
            base,
            size,
        }
    }

    pub fn from_buffer(buffer: &[u8]) -> Self {
        let mut memory = Self::new(buffer.len());
        
        memory.copy_from_slice(buffer);

        memory
    }
}

impl Drop for ExecutableMemory {
    fn drop(&mut self) {
        unsafe {
            free_rwx(self.base, self.size);
        }
    }
}

impl Deref for ExecutableMemory {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        unsafe {
            std::slice::from_raw_parts(self.base, self.size)
        }
    }
}

impl DerefMut for ExecutableMemory {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            std::slice::from_raw_parts_mut(self.base, self.size)
        }
    }
}
