pub(super) trait Pass {
    fn name(&self) -> &str;
    fn time(&self) -> crate::timing::TimedBlock;
    fn run_on_function(&self, function: &mut crate::FunctionData) -> bool;

    fn run_on_function_timed(&self, function: &mut crate::FunctionData) -> bool {
        let _time = self.time();

        self.run_on_function(function)
    }
}

#[derive(Copy, Clone)]
pub struct IRPass {
    pub(super) inner: &'static dyn Pass,
}

impl IRPass {
    pub(super) fn name(&self) -> &str {
        self.inner.name()
    }
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
pass!(pub propagate_block_invariants, PropagateBlockInvariantsPass);
pass!(pub simplify_expressions, SimplifyExpressionsPass);
pass!(pub undefined_propagate, UndefinedPropagatePass);
pass!(pub optimize_known_bits, OptimizeKnownBitsPass);
pass!(pub simplify_compares, SimplifyComparesPass);
pass!(pub branch_to_select, BranchToSelectPass);
pass!(pub remove_dead_code, RemoveDeadCodePass);
pass!(pub const_propagate, ConstPropagatePass);
pass!(pub global_reorder, GlobalReorderPass);
pass!(pub memory_to_ssa, MemoryToSsaPass);
pass!(pub minimize_phis, MinimizePhisPass);
pass!(pub simplify_cfg, SimplifyCFGPass);
pass!(pub reorder, ReorderPass);


passes!(pub deduplicate, DeduplicatePrecisePass, deduplicate_precise,
                         DeduplicateFastPass, deduplicate_fast);

passes!(pub remove_known_loads, RemoveKnownLoadsPrecisePass, remove_known_loads_precise,
                                RemoveKnownLoadsFastPass, remove_known_loads_fast);

passes!(pub remove_dead_stores, RemoveDeadStoresPrecisePass, remove_dead_stores_precise,
                                RemoveDeadStoresFastPass, remove_dead_stores_fast);

pass!(remove_nops, RemoveNopsPass);
pass!(remove_aliases, RemoveAliasesPass);
pass!(rewrite_values, RewriteValuesPass);
