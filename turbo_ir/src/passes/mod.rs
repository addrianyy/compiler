pub(super) trait Pass {
    fn name(&self) -> &str;
    fn run_on_function(&self, function: &mut crate::FunctionData) -> bool;
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

macro_rules! passes {
    (pub $module: ident, $($pass: ident, $function: ident),*) => {
        mod $module;

        $(
            #[allow(unused_imports)]
            pub(super) use $module::$pass;

            pub fn $function() -> IRPass {
                IRPass {
                    inner: &$module::$pass,
                }
            }
        )*
    };
}

pass!(pub remove_ineffective_operations, RemoveIneffectiveOperationsPass);
pass!(pub simplify_expressions, SimplifyExpressionsPass);
pass!(pub undefined_propagate, UndefinedPropagatePass);
pass!(pub remove_dead_stores, RemoveDeadStoresPass);
pass!(pub remove_known_loads, RemoveKnownLoadsPass);
pass!(pub simplify_compares, SimplifyComparesPass);
pass!(pub branch_to_select, BranchToSelectPass);
pass!(pub remove_dead_code, RemoveDeadCodePass);
pass!(pub const_propagate, ConstPropagatePass);
pass!(pub memory_to_ssa, MemoryToSsaPass);
pass!(pub minimize_phis, MinimizePhisPass);
pass!(pub simplify_cfg, SimplifyCFGPass);
pass!(pub x86reorder, X86ReorderPass);
pass!(pub reorder, ReorderPass);

passes!(pub deduplicate, DeduplicatePrecisePass, deduplicate_precise,
                         DeduplicateFastPass, deduplicate_fast);

pass!(remove_nops, RemoveNopsPass);
pass!(remove_aliases, RemoveAliasesPass);
pass!(rewrite_values, RewriteValuesPass);
