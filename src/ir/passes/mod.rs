mod stackalloc_to_reg;
mod remove_dead_code;
mod remove_aliases;
mod remove_nops;
mod deduplicate;
mod simplify_cfg;
mod const_propagate;
mod remove_ineffective_operations;

use super::{FunctionData, Instruction};

pub(super) trait Pass {
    fn run_on_function(&self, function: &mut FunctionData) -> bool;
}

pub(super) use remove_ineffective_operations::RemoveIneffectiveOperationsPass;
pub(super) use stackalloc_to_reg::StackallocToRegPass;
pub(super) use remove_dead_code::RemoveDeadCodePass;
pub(super) use const_propagate::ConstPropagatePass;
pub(super) use remove_aliases::RemoveAliasesPass;
pub(super) use simplify_cfg::SimplifyCFGPass;
pub(super) use deduplicate::DeduplicatePass;
pub(super) use remove_nops::RemoveNopsPass;
