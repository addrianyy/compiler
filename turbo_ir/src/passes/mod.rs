pub(super) trait Pass {
    fn run_on_function(&self, function: &mut crate::FunctionData) -> bool;
    fn name(&self) -> &str;
}

macro_rules! pass {
    ($module: ident, $pass: ident) => {
        mod $module;
        pub(super) use $module::$pass;
    }
}

pass!(remove_ineffective_operations, RemoveIneffectiveOperationsPass);
pass!(simplify_expressions, SimplifyExpressionsPass);
pass!(remove_dead_stores, RemoveDeadStoresPass);
pass!(remove_known_loads, RemoveKnownLoadsPass);
pass!(simplify_compares, SimplifyComparesPass);
pass!(branch_to_select, BranchToSelectPass);
pass!(remove_dead_code, RemoveDeadCodePass);
pass!(const_propagate, ConstPropagatePass);
pass!(remove_aliases, RemoveAliasesPass);
pass!(rewrite_values, RewriteValuesPass);
pass!(memory_to_ssa, MemoryToSsaPass);
pass!(simplify_cfg, SimplifyCFGPass);
pass!(deduplicate, DeduplicatePass);
pass!(remove_nops, RemoveNopsPass);
pass!(x86reorder, X86ReorderPass);
pass!(reorder, ReorderPass);
