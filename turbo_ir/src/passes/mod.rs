mod remove_ineffective_operations;
mod simplify_expressions;
mod remove_known_loads;
mod remove_dead_stores;
mod simplify_compares;
mod remove_dead_code;
mod const_propagate;
mod remove_aliases;
mod simplify_cfg;
mod deduplicate;
mod remove_nops;
mod x86reorder;
mod reorder;

pub(super) trait Pass {
    fn run_on_function(&self, function: &mut crate::FunctionData) -> bool;
    fn name(&self) -> &str;
}

pub(super) use remove_ineffective_operations::RemoveIneffectiveOperationsPass;
pub(super) use simplify_expressions::SimplifyExpressionsPass;
pub(super) use remove_dead_stores::RemoveDeadStoresPass;
pub(super) use remove_known_loads::RemoveKnownLoadsPass;
pub(super) use simplify_compares::SimplifyComparesPass;
pub(super) use remove_dead_code::RemoveDeadCodePass;
pub(super) use const_propagate::ConstPropagatePass;
pub(super) use remove_aliases::RemoveAliasesPass;
pub(super) use simplify_cfg::SimplifyCFGPass;
pub(super) use deduplicate::DeduplicatePass;
pub(super) use remove_nops::RemoveNopsPass;
pub(super) use x86reorder::X86ReorderPass;
pub(super) use reorder::ReorderPass;
