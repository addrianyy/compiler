pub(super) trait Pass {
    fn run_on_function(&self, function: &mut crate::FunctionData) -> bool;
    fn name(&self) -> &str;
}

#[derive(Copy, Clone)]
pub struct IRPass {
    pub(super) inner: &'static dyn Pass,
}

macro_rules! pass {
    (pub $module: ident, $pass: ident) => {
        mod $module;

        #[allow(unused_imports)]
        pub(super) use $module::$pass;

        pub fn $module() -> IRPass {
            IRPass {
                inner: &$module::$pass,
            }
        }
    };
    ($module: ident, $pass: ident) => {
        mod $module;
        pub(super) use $module::$pass;
    };
}

pass!(pub remove_ineffective_operations, RemoveIneffectiveOperationsPass);
pass!(pub simplify_expressions, SimplifyExpressionsPass);
pass!(pub remove_dead_stores, RemoveDeadStoresPass);
pass!(pub remove_known_loads, RemoveKnownLoadsPass);
pass!(pub simplify_compares, SimplifyComparesPass);
pass!(pub branch_to_select, BranchToSelectPass);
pass!(pub remove_dead_code, RemoveDeadCodePass);
pass!(pub const_propagate, ConstPropagatePass);
pass!(pub memory_to_ssa, MemoryToSsaPass);
pass!(pub simplify_cfg, SimplifyCFGPass);
pass!(pub deduplicate, DeduplicatePass);
pass!(pub x86reorder, X86ReorderPass);
pass!(pub reorder, ReorderPass);

pass!(remove_nops, RemoveNopsPass);
pass!(remove_aliases, RemoveAliasesPass);
pass!(rewrite_values, RewriteValuesPass);
