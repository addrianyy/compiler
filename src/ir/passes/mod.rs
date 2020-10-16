mod stackalloc_to_reg;
mod remove_dead_code;
mod remove_aliases;
mod remove_nops;
mod deduplicate;
mod remove_ineffective_operations;

use super::{FunctionData, Instruction};

pub(super) trait Pass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool;
}

pub(super) use remove_ineffective_operations::RemoveIneffectiveOperationsPass;
pub(super) use stackalloc_to_reg::StackallocToRegPass;
pub(super) use remove_dead_code::RemoveDeadCodePass;
pub(super) use remove_aliases::RemoveAliasesPass;
pub(super) use deduplicate::DeduplicatePass;
pub(super) use remove_nops::RemoveNopsPass;
