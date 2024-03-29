use std::collections::VecDeque;

use super::{FunctionData, Value, Location, Label, Dominators, Map, Set,
            Instruction, Type, CapacityExt, BinaryOp};

const VALUE_DIVIDER: usize = 4;

pub(super) type ValidationKey = (Label, Label, Option<KillTarget>);

#[derive(Default)]
pub(super) struct ValidationCache {
    labels: Map<ValidationKey, Option<Vec<Label>>>,
}

pub(super) type Users    = Map<Value, Set<Location>>;
pub(super) type DomCache = Set<(Label, Label)>;
pub(super) type Const    = u64;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(super) enum ConstType {
    U1,
    U8,
    U16,
    U32,
    U64,
}

impl ConstType {
    pub(super) fn new(ty: Type) -> ConstType {
        match ty {
            Type::U1  => ConstType::U1,
            Type::U8  => ConstType::U8,
            Type::U16 => ConstType::U16,
            Type::U32 => ConstType::U32,
            Type::U64 => ConstType::U64,
            // Pointer is treated as constant type U64.
            _ => ConstType::U64,
        }
    }
}

struct PointerAnalysisContext {
    analysis: PointerAnalysis,
    creators: Map<Value, Location>,
}

impl PointerAnalysisContext {
    fn get_origin(&self, pointer: Value) -> Value {
        self.analysis.origins.get(&pointer).copied().unwrap()
    }
}

pub(super) struct PointerAnalysis {
    origins:     Map<Value, Value>,
    stackallocs: Map<Value, bool>,
}

#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub(super) enum KillTarget {
    Start,
    End,
}

impl PointerAnalysis {
    pub fn can_alias(&self, function: &FunctionData, p1: Value, p2: Value) -> bool {
        time!(can_alias);

        // If two pointers are the same they always alias.
        if p1 == p2 {
            return true;
        }

        // Get origin of pointers.
        let p1 = self.origins[&p1];
        let p2 = self.origins[&p2];

        // If two pointers have the same origin they may alias.
        if p1 == p2 {
            return true;
        }

        // Undefined pointers don't alias anything.
        if function.is_value_undefined(p1) || function.is_value_undefined(p2) {
            return false;
        }

        // Get information about pointers stackalloc.
        let p1_stackalloc = self.stackallocs.get(&p1);
        let p2_stackalloc = self.stackallocs.get(&p2);

        match (p1_stackalloc, p2_stackalloc) {
            (Some(_), Some(_)) => {
                // Both pointers come from different stackallocs. It doesn't matter
                // if stackallocs are safe - pointers don't alias.
                false
            }
            (Some(safe), None) | (None, Some(safe)) => {
                // One pointer comes from stackalloc, other does not.
                // If stackalloc usage is safe than these two pointers can't alias. Otherwise
                // they can.

                !safe
            }
            // We don't have any information about pointers. They may alias.
            _ => true,
        }
    }

    pub fn is_stackalloc(&self, pointer: Value) -> bool {
        self.stackallocs.get(&self.origins[&pointer]).is_some()
    }
}

impl FunctionData {
    pub(super) fn can_call_access_pointer(&self, pointer_analysis: &PointerAnalysis,
                                          call: &Instruction, pointer: Value) -> bool {
        time!(can_call_access_pointer);

        if let Instruction::Call { args, .. } = call {
            if args.is_empty() {
                // No pointer can be changed if this function doesn't take any parameters.
                false
            } else {
                // Try to get stackalloc form provided pointer.
                let origin     = pointer_analysis.origins[&pointer];
                let stackalloc = pointer_analysis.stackallocs.get(&origin);

                if let Some(true) = stackalloc {
                    // Pointer is safely used stackalloc. If no argument originates from
                    // the same stackalloc, this call cannot affect the pointer.

                    args.iter().any(|arg| pointer_analysis.origins.get(arg) == Some(&origin))
                } else {
                    // We have no idea about non-safe stackallocs or pointers
                    // with unknown origin.

                    true
                }
            }
        } else {
            panic!("Non call instruction provided to `can_call_access_pointer`.");
        }
    }

    fn get_pointer_origin(&self, pointer: Value, cx: &mut PointerAnalysisContext) {
        time!(get_pointer_origin);

        // If pointer origin is unknown or it's at its primary origin this function will
        // return unmodified `pointer`.

        // Try to get origin from an instruction that created the pointer.
        let origin = if let Some(&creator) = cx.creators.get(&pointer) {
            match self.instruction(creator) {
                // Instructions which can create pointers but for which we don't know the origin.
                Instruction::Load  { .. } => pointer,
                Instruction::Call  { .. } => pointer,

                // Casted pointers can alias, we cannot get their origin.
                Instruction::Cast { .. } => pointer,

                // We are actually at the primary origin.
                Instruction::StackAlloc { .. } => pointer,

                // Get origin from aliased value.
                Instruction::Alias { value, .. } => cx.get_origin(*value),

                // GEP result pointer must be originating from it's source.
                Instruction::GetElementPtr { source, .. } => cx.get_origin(*source),

                // Get common origin if it exists.
                Instruction::Select { on_true, on_false, .. } => {
                    let true_origin  = cx.get_origin(*on_true);
                    let false_origin = cx.get_origin(*on_false);

                    if true_origin == false_origin {
                        true_origin
                    } else {
                        pointer
                    }
                }

                // Get common origin if it exists.
                Instruction::Phi { incoming, .. } => {
                    let mut common_origin = None;

                    // Make sure that all incoming values have the same origin.
                    for &(_, incoming_value) in incoming {
                        // Skip self reference.
                        if incoming_value == pointer {
                            continue;
                        }

                        if let Some(&origin) = cx.analysis.origins.get(&incoming_value) {
                            if common_origin.is_none() || Some(origin) == common_origin {
                                common_origin = Some(origin);
                            } else {
                                // Origin mismatch.
                                common_origin = None;
                                break;
                            }
                        } else {
                            // No origin calculated yet, we cannot reason about this PHI.
                            common_origin = None;
                            break;
                        }
                    }

                    common_origin.unwrap_or(pointer)
                }

                // Other instructions should never create pointers.
                x => panic!("Unexpected instruction {:?} created pointer.", x),
            }
        } else {
            // This pointer doesn't have creator - it's coming from an argument or it is
            // `undefined`. We don't know its origin.

            pointer
        };

        // Add calculated origin to the map.
        assert!(cx.analysis.origins.insert(pointer, origin).is_none(),
                "Someone already added origin of this pointer?");
    }

    fn safe_pointers(&self, processing_order: Vec<Value>, pointers: &FastValueSet,
                     labels: &[Label]) -> FastValueSet {
        time!(safe_pointers);

        let mut safe_pointers = FastValueSet::new(self);
        let users             = self.pointer_users_with_labels(&pointers, labels);

        macro_rules! is_safe {
            ($value: expr) => {
                safe_pointers.contains($value)
            }
        }

        // Reverse ordering so every value is used before being created.
        //
        // We are at point P in the processing order on which value V is created.
        // It is guaranteed that all output values of instructions that use V will
        // after P.
        //
        // After reversing it, it is guaranteed that all output values of instructions that
        // use V are before P and were already processed (which is what we want).
        for pointer in processing_order.into_iter().rev() {
            // Ignore non-pointer values.
            if !pointers.contains(pointer) {
                continue;
            }

            let mut safe = true;

            // Make sure that all uses are safe. If they are it means that we always know
            // all values which point to the same memory as this pointer. Otherwise, pointer may
            // escape and be accessed by unknown instruction.
            if let Some(users) = users.get(&pointer) {
                for &location in users {
                    safe = match self.instruction(location) {
                        Instruction::Store { ptr, value } => {
                            // Make sure that we are actually storing TO the pointer, not
                            // storing the pointer.
                            *ptr == pointer && *value != pointer
                        }
                        Instruction::Load          { .. } => true,
                        Instruction::Return        { .. } => true,
                        Instruction::IntCompare    { .. } => true,
                        Instruction::GetElementPtr { dst, source, .. } => {
                            // GEP returns memory which belongs to the source pointer. Make sure
                            // that GEP return value is safely used.
                            *source == pointer && is_safe!(*dst)
                        }
                        Instruction::Alias { dst, .. } => {
                            // Make sure that aliased pointer is safely used.
                            is_safe!(*dst)
                        }
                        Instruction::Phi { dst, .. } => {
                            // If PHI pointer safety wasn't computed then assume
                            // that it is unsafe.
                            is_safe!(*dst)
                        }
                        // All other uses (casts, etc..) are not safe and we can't
                        // reason about them.
                        _ => false,
                    };

                    if !safe {
                        break;
                    }
                }
            }

            if safe {
                safe_pointers.insert(pointer);
            }
        }

        safe_pointers
    }

    pub(super) fn analyse_pointers(&self) -> PointerAnalysis {
        time!(analyse_pointers);

        let labels = self.reachable_labels();

        let mut cx = PointerAnalysisContext {
            analysis: PointerAnalysis {
                origins:     Map::default(),
                stackallocs: Map::default(),
            },
            creators: self.value_creators_with_labels(&labels),
        };

        let processing_order = self.value_processing_order_with_labels(&labels);
        let mut pointers     = FastValueSet::new(self);

        // Get origin of all pointers used in the function.
        for &value in &processing_order {
            if self.value_type(value).is_pointer() {
                pointers.insert(value);

                self.get_pointer_origin(value, &mut cx);
            }
        }

        // Get list of all safe pointers in the function.
        let safe_pointers = self.safe_pointers(processing_order, &pointers, &labels);

        // Process `stackalloc`s to determine which ones are safely used.
        self.for_each_instruction_with_labels(&labels, |_location, instruction| {
            if let Instruction::StackAlloc { dst, .. } = instruction {
                // Get information about `stackalloc`: check if it's safely used and can't
                // escape.
                let pointer = *dst;
                let safe    = safe_pointers.contains(pointer);

                assert!(cx.analysis.stackallocs.insert(pointer, safe).is_none(),
                        "Multiple pointers from stackalloc?");
            }
        });

        cx.analysis
    }

    pub(super) fn depends_on_predecessors(&self, label: Label, predecessors: &[Label]) -> bool {
        time!(depends_on_predecessors);

        // Go through every PHI instruction in the block.
        for instruction in &self.blocks[&label] {
            if let Instruction::Phi { incoming, .. } = instruction {
                // Check if there is any value which strictly depends on control flow.
                let mut checks = vec![None; predecessors.len()];

                assert!(incoming.len() >= predecessors.len(), "Incoming and \
                        predecessors don't match.");

                // Get value for every `predecessor` if it exists.
                for (label, value) in incoming.iter() {
                    if let Some(index) = predecessors.iter().position(|x| x == label) {
                        checks[index] = Some(*value);
                    }
                }

                let mut last_value = None;

                // Check if every value is the same.
                for value in checks.into_iter().filter_map(|x| x) {
                    if let Some(lv) = last_value {
                        if lv != value {
                            // Two different values for different predecessors, this label
                            // depends on predecessors.
                            return true;
                        }
                    }

                    last_value = Some(value);
                }
            }
        }

        false
    }

    pub(super) fn replace_phi_incoming(&mut self, label: Label, old_incoming: Label,
                                       new_incoming: Label) {
        time!(replace_phi_incoming);

        // Go through every PHI instruction in the block.
        for instruction in self.blocks.get_mut(&label).unwrap() {
            if let Instruction::Phi { incoming, .. } = instruction {
                let mut existing_new = None;

                // Go through incoming labels to check if there is already `new_incoming`
                // value. If there is, we must just remove `old_incoming` values.
                for (label, value) in incoming.iter() {
                    if *label == new_incoming {
                        existing_new = Some(*value);
                        break;
                    }
                }

                if let Some(existing_new) = existing_new {
                    incoming.retain(|&(label, value)| {
                        if label == old_incoming {
                            // We need to remove this entry, but make sure that values are the
                            // same.

                            assert_eq!(existing_new, value, "Tried to replace invalid \
                                       PHI incoming.");

                            return false;
                        }

                        true
                    });
                } else {
                    // `new_incoming` isn't in the PHI node, replace all uses of `old_incoming`
                    // to `new_incoming`.
                    for (label, _) in incoming.iter_mut() {
                        if *label == old_incoming {
                            *label = new_incoming;
                        }
                    }
                }
            }
        }
    }

    pub(super) fn block_contains_phi(&self, label: Label) -> bool {
        time!(block_contains_phi);

        for instruction in &self.blocks[&label] {
            if instruction.is_phi() {
                return true;
            }
        }

        false
    }

    #[allow(unused)]
    pub(super) fn constant_values(&self) -> Map<Value, (Type, Const)> {
        self.constant_values_with_labels(&self.reachable_labels())
    }

    pub(super) fn constant_values_with_labels(&self, labels: &[Label]) 
        -> Map<Value, (Type, Const)>
    {
        time!(constant_values);

        let mut consts = self.constants.clone();

        self.for_each_instruction_with_labels(labels, |_location, instruction| {
            if let Instruction::Alias { dst, value } = instruction {
                if let Some(&(ty, value)) = consts.get(value) {
                    assert!(consts.insert(*dst, (ty, value)).is_none(),
                            "Multiple constant value creators.");
                }
            }
        });

        consts
    }

    /// Check if there is any path that goes from `from` to `to` without going through
    /// `without`.
    fn can_reach(&self, from: Label, to: Label, without: Label) -> bool {
        time!(can_reach);

        // Make sure that start and end points are not blacklisted.
        assert!(from != without && to != without, "Invalid input to `can_reach`.");

        // We can always reach ourselves.
        if from == to {
            return true;
        }

        let mut visited = Set::default();
        let mut stack   = Vec::new();

        // Start from `from`.
        stack.push(from);

        // Always ignore `without`.
        visited.insert(without);

        // Check if we can reach `to` starting from `from` ignoring `without` using
        // DFS traversal.
        while let Some(label) = stack.pop() {
            if label == to {
                return true;
            }

            if !visited.insert(label) {
                continue;
            }

            for target in self.targets(label) {
                stack.push(target);
            }
        }

        false
    }

    /// Check if `killee` can reach itself without hitting `killer`. If it can, this function
    /// will return all labels that take part in the cycle.
    fn escaping_cycle_blocks_internal(&self, killer: Label, killee: Label) -> Option<Set<Label>> {
        time!(escaping_cycle_blocks_internal);

        let mut cycle_blocks = Set::default();
        let mut visited      = Set::default();
        let mut stack        = Vec::new();

        // Start from `killee`.
        stack.push(killee);

        // Always ignore `killer`.
        visited.insert(killer);

        let mut is_first = true;
        let mut escaped  = false;

        while let Some(label) = stack.pop() {
            // If we hit `killee` and it's not the first iteration then some block escaped
            // the cycle.
            if label == killee && !is_first {
                escaped = true;
            }

            is_first = false;

            if !visited.insert(label) {
                continue;
            }

            cycle_blocks.insert(label);

            for target in self.targets(label) {
                stack.push(target);
            }
        }

        // If some blocks escaped then return all blocks that take part in the cycle.
        match escaped {
            true  => Some(cycle_blocks),
            false => None,
        }
    }

    fn escaping_cycle_blocks(&self, start_label: Label, end_label: Label,
                             memory_kill: KillTarget) -> Option<Set<Label>> {
        time!(escaping_cycle_blocks);

        let (killer, killee) = match memory_kill {
            KillTarget::Start => (end_label, start_label),
            KillTarget::End   => (start_label, end_label),
        };

        self.escaping_cycle_blocks_internal(killer, killee).map(|blocks| {
            // `blocks` is a list of all blocks that take part in the cycle.

            let mut escaped = Set::default();

            for block in blocks {
                let insert = match memory_kill {
                    KillTarget::Start => {
                        // If it is possible to reach `block` from `start` without `end` then
                        // this block escapes cycle and needs to be additionaly checked.
                        self.can_reach(start_label, block, end_label)
                    }
                    KillTarget::End => {
                        // If it is possible to reach `end` from `block` without `start` then
                        // this block escapes cycle and needs to be additionaly checked.
                        self.can_reach(block, end_label, start_label)
                    }
                };

                if insert {
                    escaped.insert(block);
                }
            }

            assert!(!escaped.is_empty(), "There must be at least one escaped block.");
            assert!(!escaped.insert(killee), "killee block must have been inserted.");
            assert!(escaped.get(&killer).is_none(), "killer block shouldn't have been inserted.");

            escaped
        })
    }

    fn validate_blocks(
        &self,
        start:        Location,
        end:          Location,
        labels:       &[Label],
        mut verifier: impl FnMut(&Instruction) -> bool,
    ) -> Option<usize> {
        time!(validate_blocks);

        let start_label = start.label();
        let end_label   = end.label();

        let mut instruction_count = 0;

        let mut included_start = false;
        let mut included_end   = false;

        // Check instructions in all queued labels.
        for &label in labels {
            for (inst_id, instruction) in self.blocks[&label].iter().enumerate() {
                // Ignore start instruction and end instruction.
                let location = Location::new(label, inst_id);

                if location == start {
                    included_start = true;
                    continue;
                }

                if location == end {
                    included_end = true;
                    continue;
                }

                if instruction.is_nop() {
                    continue;
                }

                if !verifier(instruction) {
                    return None;
                }

                instruction_count += 1;
            }
        }

        // Check start label partially if we haven't checked it previously.
        if !included_start {
            // Make sure there is no invalid instruction in the remaining part of start block.
            for instruction in &self.blocks[&start_label][start.index() + 1..] {
                if instruction.is_nop() {
                    continue;
                }

                if !verifier(instruction) {
                    return None;
                }

                instruction_count += 1;
            }
        }

        // Check end label partially if we haven't checked it previously.
        if !included_end {
            // Make sure there is no invalid instruction in the initial part of end block.
            for instruction in &self.blocks[&end_label][..end.index()] {
                if instruction.is_nop() {
                    continue;
                }

                if !verifier(instruction) {
                    return None;
                }

                instruction_count += 1;
            }
        }

        Some(instruction_count)
    }

    fn validate_path_internal(
        &self,
        dominators:   &Dominators,
        start:        Location,
        end:          Location,
        memory_kill:  Option<KillTarget>,
        cache:        &mut ValidationCache,
        mut verifier: impl FnMut(&Instruction) -> bool,
    ) -> Option<usize> {
        time!(validate_path_complex);

        let start_label = start.label();
        let end_label   = end.label();

        // Base case: both path points are in the same block.
        if start_label == end_label {
            let mut instruction_count = 0;

            // Start must be before end to make valid path.
            if start.index() < end.index() {
                // Verify all instructions between `start` and `end`.
                for instruction in &self.blocks[&start_label][start.index() + 1..end.index()] {
                    if !verifier(instruction) {
                        return None;
                    }

                    instruction_count += 1;
                }

                return Some(instruction_count);
            }

            return None;
        }

        // Get a key for this path validation.
        let key = (start_label, end_label, memory_kill);

        // Check if this path was already explored.
        if let Some(labels) = cache.labels.get(&key) {
            // It was, check all blocks that are part of this path.
            return labels.as_ref().and_then(|labels| {
                self.validate_blocks(start, end, labels, verifier)
            });
        }

        let mut result: Option<Vec<Label>> = None;

        // When path points are in different blocks then start block must dominate end block.
        if self.dominates(dominators, start_label, end_label) {
            let mut labels = Set::default();

            // If there is a cycle then other blocks may need to be checked.
            let blocks = memory_kill.and_then(|memory_kill| {
                self.escaping_cycle_blocks(start_label, end_label, memory_kill)
            });

            if let Some(blocks) = blocks {
                labels.reserve(blocks.len());

                // Queue traversal of additional blocks.
                for block in blocks {
                    labels.insert(block);
                }
            }

            // Find all blocks that are possible to hit when going from start to end.

            let incoming = self.flow_graph_incoming();

            let mut visited = Set::default();
            let mut stack   = Vec::new();

            // Start traversing from end of path and go upwards.
            stack.push(end_label);

            while let Some(label) = stack.pop() {
                if !visited.insert(label) {
                    continue;
                }

                // Queue traversal of upper blocks.
                for &predecessor in &incoming[&label] {
                    // Because start block dominates end block we must eventually hit start block
                    // during traversal. In this case we shouldn't go up.
                    if predecessor != start_label {
                        stack.push(predecessor);
                    }
                }
            }

            labels.reserve(visited.len() - 1);

            for &label in &visited {
                // Don't check `end_label` or `start_label` here because we will only go
                // through part of it and it was already checked before.
                if label != end_label && label != start_label {
                    labels.insert(label);
                }
            }

            result = Some(labels.into_iter().collect());
        }

        // Validate calculated path.
        let validated = result.as_ref().and_then(|labels| {
            self.validate_blocks(start, end, &labels, verifier)
        });

        // Add blocks that belong to that path to the cache.
        cache.labels.insert(key, result);

        validated
    }

    pub(super) fn validate_path_memory(
        &self,
        dominators: &Dominators,
        start:      Location,
        end:        Location,
        target:     KillTarget,
        cache:      &mut ValidationCache,
        verifier:   impl FnMut(&Instruction) -> bool,
    ) -> Option<usize> {
        self.validate_path_internal(dominators, start, end, Some(target), cache, verifier)
    }

    pub(super) fn validate_path_count(
        &self,
        dominators: &Dominators,
        start:      Location,
        end:        Location,
        cache:      &mut ValidationCache,
    ) -> Option<usize> {
        self.validate_path_internal(dominators, start, end, None, cache, |_| true)
    }

    pub(super) fn dominates(&self, dominators: &Dominators,
                            dominator: Label, target: Label) -> bool {
        time!(dominates);

        let mut current = Some(target);

        while let Some(idom) = current {
            if idom == dominator {
                return true;
            }

            current = dominators.get(&idom).copied();
        }

        false
    }

    pub(super) fn validate_path_cached(&self, dominators: &Dominators,
                                       start: Location, end: Location,
                                       cache: &mut DomCache) -> bool {
        time!(validate_path);

        let start_label = start.label();
        let end_label   = end.label();

        if start_label == end_label {
            return start.index() < end.index();
        }

        if cache.contains(&(start_label, end_label)) {
            return true;
        }

        let dominates = self.dominates(dominators, start_label, end_label);

        if dominates {
            cache.insert((start_label, end_label));
        }

        dominates
    }

    pub(super) fn validate_ssa(&self) {
        time!(validate_ssa);

        let dominators    = self.dominators();
        let creators      = self.value_creators();
        let flow_incoming = self.flow_graph_incoming();

        assert!(flow_incoming[&self.entry()].is_empty(),
                "There cannot be jumps to the entry block.");

        let mut cache = Set::default();

        for label in self.reachable_labels() {
            let _    = self.targets(label);
            let body = &self.blocks[&label];

            for instruction in &body[..body.len() - 1] {
                assert!(instruction.targets().is_none(), "Terminator {:?} in the middle of block {}.",
                        instruction, label);
            }

            for (inst_id, instruction) in body.iter().enumerate() {
                if let Some(value) = instruction.created_value() {
                    assert!(!self.is_value_undefined(value),
                            "Cannot return to undefined value {}.", value);
                }

                if let Instruction::Phi { incoming, .. } = instruction {
                    assert_ne!(label, self.entry(), "Entry labels cannot have PHI nodes.");
                    assert!(!incoming.is_empty(), "PHI nodes cannot be empty.");

                    let incoming_labels: Set<Label> = incoming.iter()
                        .map(|(label, _value)| *label)
                        .collect();

                    assert_eq!(incoming_labels, flow_incoming[&label], "PHI node incoming \
                               labels and block predecessors don't match.");

                    assert_eq!(incoming.len(), incoming_labels.len(),
                               "PHI node has duplicate labels.");

                    for &(label, value) in incoming {
                        if self.is_value_special(value) {
                            continue;
                        }

                        let other_body = &self.blocks[&label];

                        // Simulate usage at the end of predecessor.
                        let creation_loc = *creators.get(&value)
                            .expect("Value used but not created.");
                        let usage_loc = Location::new(label, other_body.len());

                        assert!(self.validate_path_cached(&dominators, creation_loc, usage_loc,
                                                          &mut cache),
                                "PHI value {} is used before being created.", value);
                    }

                    continue;
                }

                for value in instruction.read_values() {
                    if self.is_value_special(value) {
                        continue;
                    }

                    let creation_loc = *creators.get(&value).expect("Value used but not created.");
                    let usage_loc    = Location::new(label, inst_id);

                    assert!(self.validate_path_cached(&dominators, creation_loc, usage_loc,
                                                      &mut cache),
                            "Value {} is used before being created.", value);
                }
            }
        }
    }

    pub(super) fn instruction(&self, location: Location) -> &Instruction {
        &self.blocks[&location.label()][location.index()]
    }

    pub(super) fn instruction_mut(&mut self, location: Location) -> &mut Instruction {
        &mut self.blocks.get_mut(&location.label()).unwrap()[location.index()]
    }

    pub(super) fn for_each_instruction_with_labels(
        &self,
        labels:       &[Label],
        mut callback: impl FnMut(Location, &Instruction)
    ) {
        for &label in labels {
            for (inst_id, inst) in self.blocks[&label].iter().enumerate() {
                callback(Location::new(label, inst_id), inst)
            }
        }
    }

    pub(super) fn for_each_instruction(&self, callback: impl FnMut(Location, &Instruction)) {
        self.for_each_instruction_with_labels(&self.reachable_labels(), callback);
    }

    pub(super) fn for_each_instruction_with_labels_mut(
        &mut self,
        labels:       &[Label],
        mut callback: impl FnMut(Location, &mut Instruction),
    ) {
        for &label in labels {
            for (inst_id, inst) in self.blocks.get_mut(&label).unwrap().iter_mut().enumerate() {
                callback(Location::new(label, inst_id), inst)
            }
        }
    }
    pub(super) fn for_each_instruction_mut(&mut self,
                                           callback: impl FnMut(Location, &mut Instruction)) {
        self.for_each_instruction_with_labels_mut(&self.reachable_labels(), callback);
    }

    pub(super) fn usage_counts(&self) -> Vec<u32> {
        time!(usage_counts);

        let mut usage_counts = vec![0; self.value_count()];

        self.for_each_instruction(|_location, instruction| {
            for value in instruction.read_values() {
                usage_counts[value.index()] += 1;
            }
        });

        usage_counts
    }

    pub(super) fn value_creators(&self) -> Map<Value, Location> {
        self.value_creators_with_labels(&self.reachable_labels())
    }

    pub(super) fn value_creators_with_labels(&self, labels: &[Label]) -> Map<Value, Location> {
        time!(value_creators);

        let mut creators = Map::new_with_capacity(self.value_count() / VALUE_DIVIDER);

        self.for_each_instruction_with_labels(labels, |location, instruction| {
            if let Some(value) = instruction.created_value() {
                assert!(creators.insert(value, location).is_none(),
                        "Value {} is defined multiple times.", value);
            }
        });

        creators
    }

    pub(super) fn find_uses(&self, value: Value) -> Vec<Location> {
        time!(find_uses);

        let mut uses = Vec::new();

        self.for_each_instruction(|location, instruction| {
            if instruction.read_values().iter().any(|x| *x == value) {
                uses.push(location);
            }
        });

        uses
    }

    pub (super) fn find_stackallocs(&self, required_size: Option<usize>)
        -> Vec<(Value, Location)>
    {
        time!(find_stackallocs);

        let mut results = Vec::new();

        self.for_each_instruction(|location, instruction| {
            if let Instruction::StackAlloc { dst, size, .. } = instruction {
                if required_size.is_none() || Some(*size) == required_size {
                    results.push((*dst, location));
                }
            }
        });

        results
    }

    pub(super) fn users_with_labels(&self, labels: &[Label]) -> Users {
        time!(users);

        let mut users = Map::new_with_capacity(self.value_count() / VALUE_DIVIDER);

        for &label in labels {
            let body = &self.blocks[&label];

            for (inst_id, instruction) in body.iter().enumerate() {
                let location = Location::new(label, inst_id);

                for value in instruction.read_values() {
                    // Mark `value` as used by this instruction.
                    users.entry(value)
                        .or_insert_with(Set::default)
                        .insert(location);
                }
            }
        }

        users
    }

    pub(super) fn pointer_users_with_labels(&self, pointers: &FastValueSet,
                                            labels: &[Label]) -> Users {
        time!(pointer_users);

        let mut users = Map::new_with_capacity(self.value_count() / VALUE_DIVIDER);

        for &label in labels {
            let body = &self.blocks[&label];

            for (inst_id, instruction) in body.iter().enumerate() {
                let location = Location::new(label, inst_id);

                for value in instruction.read_values() {
                    if pointers.contains(value) {
                        // Mark `value` as used by this instruction.
                        users.entry(value)
                            .or_insert_with(|| Set::new_with_capacity(2))
                            .insert(location);
                    }
                }
            }
        }

        users
    }

    pub(super) fn value_processing_order(&self) -> Vec<Value> {
        self.value_processing_order_with_labels(&self.reachable_labels())
    }

    pub(super) fn value_processing_order_with_labels(&self, labels: &[Label]) -> Vec<Value> {
        time!(value_processing_order);

        let mut users: Map<Value, Set<(Location, Value)>> =
            Map::new_with_capacity(self.value_count() / VALUE_DIVIDER);

        let mut phis  = Vec::new();
        let mut queue = VecDeque::with_capacity(self.argument_values.len() +
                                                self.undefined_set.len() +
                                                self.constants.len());

        let mut expected_value_count = 0;

        {
            time!(processing_order_presolve);

            // Handle all function arguments.
            for &value in &self.argument_values {
                // Function arguments can be processed immediately.
                queue.push_back(value);

                expected_value_count += 1;
            }

            // Handle all undefined values.
            for &value in &self.undefined_set {
                // Undefined values can be processed immediately.
                queue.push_back(value);

                expected_value_count += 1;
            }

            // Handle all constant values.
            for &value in self.constants.keys() {
                // Constant values can be processed immediately.
                queue.push_back(value);

                expected_value_count += 1;
            }

            // Handle all other values which were created in the IR.
            for &label in labels {
                let body = &self.blocks[&label];

                for (inst_id, instruction) in body.iter().enumerate() {
                    let location = Location::new(label, inst_id);

                    // We only care about instructions which create new values.
                    if let Some(created_value) = instruction.created_value() {
                        let read_values = instruction.read_values();

                        // If this instruction doesn't depend on any value then it can be
                        // processed immediately.
                        if read_values.is_empty() {
                            queue.push_back(created_value);
                        }

                        // PHIs can have cycles and they need to be handled specially.
                        if let Instruction::Phi { dst, incoming } = instruction {
                            phis.push((*dst, incoming));
                        }

                        for value in read_values {
                            // Mark `value` as used by this instruction.
                            users.entry(value)
                                .or_insert_with(|| Set::new_with_capacity(2))
                                .insert((location, created_value));
                        }

                        expected_value_count += 1;
                    }
                }
            }
        }

        let mut order  = Vec::with_capacity(expected_value_count);
        let mut done   = FastValueSet::new(self);
        let mut ignore = FastValueSet::new(self);

        // Try to iteratively solve dependencies.
        'main_loop: loop {
            while let Some(value) = queue.pop_front() {
                // This value is now processed and its dependencies are solved.
                order.push(value);
                done.insert(value);

                if let Some(users) = users.get(&value) {
                    // Processing this value may have solved dependencies for some users
                    // of this value.
                    for &(location, output) in users.iter() {
                        // Skip if output is already processed or is queued to be processed.
                        if done.contains(output) || ignore.contains(output) {
                            continue;
                        }

                        // If all input values of this instruction are now processed,
                        // `output` is ready to be processed too.
                        let ready = self.instruction(location).read_values().iter()
                            .all(|&input| input == output || done.contains(input));

                        if ready {
                            queue.push_back(output);
                            ignore.insert(output);
                        }
                    }
                }
            }

            let mut best_phi        = None;
            let mut unresolved_phis = false;

            // Find PHI which has smallest number of known inputs (but at least one).
            for &(phi_value, incoming) in &phis {
                if done.contains(phi_value) {
                    continue;
                }

                unresolved_phis = true;

                let mut known_inputs = 0;

                // Get amount of known inputs to PHI.
                for &(_, value) in incoming.iter() {
                    if value != phi_value && done.contains(value) {
                        known_inputs += 1;
                    }
                }

                // We can't do anything with PHIs that have no known inputs.
                if known_inputs < 1 {
                    continue;
                }

                // Pick PHI with smallest number of known inputs.
                let better = match best_phi {
                    Some((_, count)) => known_inputs < count,
                    None             => true,
                };

                if better {
                    best_phi = Some((phi_value, known_inputs));
                }
            }

            // No PHIs left to process, we are done.
            if !unresolved_phis {
                break;
            }

            if let Some((phi_value, _)) = best_phi {
                queue.push_back(phi_value);

                continue 'main_loop;
            }

            // There are unsolved PHIs left but none of them have at least one processed input.
            // If program is in valid SSA form this should never happen.
            panic!("Couldn't solve value dpendencies because of PHI cycles.");
        }

        // Make sure that we have actually processed everything.
        assert_eq!(order.len(), expected_value_count, "Not all values were processed.");

        order
    }

    pub(super) fn can_load_pointer(&self, instruction: &Instruction,
                                   pointer_analysis: &PointerAnalysis,
                                   pointer: Value) -> bool {
        match instruction {
            Instruction::Call  { .. } => {
                self.can_call_access_pointer(&pointer_analysis,
                                             instruction,
                                             pointer)
            }
            Instruction::Load { ptr, .. } => {
                pointer_analysis.can_alias(self, pointer, *ptr)
            }
            _ => false,
        }
    }

    pub(super) fn can_store_pointer(&self, instruction: &Instruction,
                                    pointer_analysis: &PointerAnalysis,
                                    pointer: Value) -> bool {
        match instruction {
            Instruction::Call  { .. } => {
                self.can_call_access_pointer(&pointer_analysis,
                                             instruction,
                                             pointer)
            }
            Instruction::Store { ptr, .. } => {
                pointer_analysis.can_alias(self, pointer, *ptr)
            }
            _ => false,
        }
    }
}

const BITS_PER_VALUE: usize = std::mem::size_of::<usize>() * 8;

pub struct FastValueSet {
    bitmap: Vec<usize>,
}

impl FastValueSet {
    pub(super) fn new(function: &FunctionData) -> Self {
        time!(fvs_new);

        Self {
            bitmap: vec![0; (function.value_count() + (BITS_PER_VALUE - 1)) / BITS_PER_VALUE],
        }
    }

    pub fn contains(&self, value: Value) -> bool {
        let index = value.index() / BITS_PER_VALUE;
        let bit   = value.index() % BITS_PER_VALUE;

        (self.bitmap[index] & (1 << bit)) != 0
    }

    pub fn insert(&mut self, value: Value) {
        let index = value.index() / BITS_PER_VALUE;
        let bit   = value.index() % BITS_PER_VALUE;

        self.bitmap[index] |= 1 << bit;
    }
}

pub fn corresponding_divmod(op: BinaryOp) -> BinaryOp {
    match op {
        BinaryOp::ModU => BinaryOp::DivU,
        BinaryOp::DivU => BinaryOp::ModU,
        BinaryOp::ModS => BinaryOp::DivS,
        BinaryOp::DivS => BinaryOp::ModS,
        _              => unreachable!(),
    }
}