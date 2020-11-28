use crate::Set;
use crate::passes;

// All optimization passes here must be in correct order.
const USER_PASSES: &[&dyn passes::Pass] = &[
    &passes::ConstPropagatePass,
    &passes::RemoveIneffectiveOperationsPass,
    &passes::SimplifyExpressionsPass,
    &passes::SimplifyCFGPass,
    &passes::UndefinedPropagatePass,
    &passes::RemoveDeadStoresFastPass,
    &passes::RemoveDeadStoresPrecisePass,
    &passes::RemoveKnownLoadsFastPass,
    &passes::RemoveKnownLoadsPrecisePass,
    &passes::SimplifyComparesPass,
    &passes::PropagateBlockInvariantsPass,
    &passes::BranchToSelectPass,
    &passes::RemoveDeadCodePass,
    &passes::MemoryToSsaPass,
    &passes::MinimizePhisPass,
    &passes::DeduplicateFastPass,
    &passes::DeduplicatePrecisePass,
    &passes::OptimizeKnownBitsPass,
    &passes::ReorderPass,
    &passes::X86ReorderPass,
];

fn pass_to_id(pass: &'static dyn passes::Pass) -> PassID {
    PassID(USER_PASSES.iter().position(|x| x.name() == pass.name()).unwrap_or_else(|| {
        panic!("Tried to reference unknown pass {}.", pass.name());
    }))
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct PassID(usize);

pub struct PassManager {
    enabled: Set<PassID>,
}

impl Default for PassManager {
    fn default() -> Self {
        Self::new()
    }
}

impl PassManager {
    pub fn new() -> Self {
        Self {
            enabled: Set::default(),
        }
    }

    pub fn with_passes(passes: &[passes::IRPass]) -> Self {
        let mut pass_manager = Self::new();

        pass_manager.add_passes(passes);

        pass_manager
    }

    pub fn add_pass(&mut self, pass: passes::IRPass) {
        let pass_id = pass_to_id(pass.inner);

        assert!(self.enabled.insert(pass_id), "Pass {} is already enabled.", pass.name());
    }

    pub fn add_passes(&mut self, passes: &[passes::IRPass]) {
        self.enabled.reserve(passes.len());

        for &pass in passes {
            self.add_pass(pass);
        }
    }

    pub fn remove_pass(&mut self, pass: passes::IRPass) {
        let pass_id = pass_to_id(pass.inner);

        assert!(self.enabled.remove(&pass_id), "Pass {} wasn't enabled.", pass.name());
    }

    pub fn remove_passes(&mut self, passes: &[passes::IRPass]) {
        for &pass in passes {
            self.remove_pass(pass);
        }
    }

    pub(super) fn build_pass_list(&self) -> Vec<&'static dyn passes::Pass> {
        let mut pass_list = Vec::with_capacity(self.enabled.len());

        for (index, pass) in USER_PASSES.iter().enumerate() {
            if self.enabled.contains(&PassID(index)) {
                pass_list.push(*pass);
            }
        }

        pass_list
    }
}
