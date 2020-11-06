use super::{FunctionData, Value, Location, Label, Dominators, Map, Set,
            Instruction, Type};

pub(super) type Const = u64;

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

pub(super) struct PointerAnalysis {
    origins:     Map<Value, Value>,
    stackallocs: Map<Value, bool>,
}

#[derive(PartialEq, Eq)]
pub(super) enum KillTarget {
    Start,
    End,
}

impl PointerAnalysis {
    pub fn get_stackalloc(&self, pointer: Value) -> Option<bool> {
        // Get origin of the pointer.
        let pointer = self.origins[&pointer];

        self.stackallocs.get(&pointer).copied()
    }

    pub fn can_alias(&self, p1: Value, p2: Value) -> bool {
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
}

impl FunctionData {
    pub(super) fn can_call_access_pointer(&self, pointer_analysis: &PointerAnalysis,
                                          call: &Instruction, pointer: Value) -> bool {
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

    fn get_pointer_origin(&self, pointer: Value,
                          cx: &mut PointerAnalysisContext) -> Value {
        // If pointer origin is unknown or it's at its primary origin this function will
        // return unmodified `pointer`.

        // Make sure that `pointer` is actually a pointer.
        assert!(self.value_type(pointer).is_pointer(),
                "Tried to get origin of non-pointer value.");
        
        // Check if we already know about origin of this pointer.
        if let Some(&origin) = cx.analysis.origins.get(&pointer) {
            return origin;
        }

        // Try to get origin from an instruction that created the pointer.
        let origin = if let Some(&creator) = cx.creators.get(&pointer) {
            match self.instruction(creator) {
                // Instructions which can create pointers but for which we don't know the origin.
                Instruction::Load   { .. } => pointer,
                Instruction::Call   { .. } => pointer,
                Instruction::Const  { .. } => pointer,
                Instruction::Select { .. } => pointer,

                // Casted pointers can alias, we cannot get their origin.
                Instruction::Cast { .. } => pointer,

                // We are actually at primary origin.
                Instruction::StackAlloc { .. } => pointer,

                // Get origin from aliased value.
                Instruction::Alias { value, .. } => self.get_pointer_origin(*value, cx),

                // GEP result pointer must be originating from it's source.
                Instruction::GetElementPtr { source, .. } => self.get_pointer_origin(*source, cx),

                Instruction::Phi { .. } => {
                    // TODO: Check all incoming values.  But to do that we need to handle
                    // self-referential PHIs.
                    pointer
                }

                // Other instructions should never create pointers.
                x => panic!("Unexpected instruction {:?} created pointer.", x),
            }
        } else {
            // This pointer doesn't have creator - it's coming from an argument.
            // We don't know it's origin.

            pointer
        };

        // Add calculated origin to the map.
        assert!(cx.analysis.origins.insert(pointer, origin).is_none(),
                "Someone already added origin of this pointer?");

        origin
    }

    fn is_pointer_safely_used(&self, pointer: Value) -> bool {
        // Make sure that `pointer` is actually a pointer.
        assert!(self.value_type(pointer).is_pointer(),
                "Tried to get origin of non-pointer value.");

        // Make sure that all uses are safe. If they are it means that we always know
        // all values which point to the same memory as this pointer. Otherwise, pointer may
        // escape and be accessed by unknown instruction.
        for location in self.find_uses(pointer) {
            match self.instruction(location) {
                Instruction::Store { ptr, value } => {
                    // Make sure that we are actually storing TO the pointer, not
                    // storing the pointer.
                    if *ptr != pointer || *value == pointer {
                        return false;
                    }
                }
                Instruction::Load          { .. } => {},
                Instruction::Return        { .. } => {},
                Instruction::IntCompare    { .. } => {},
                Instruction::GetElementPtr { dst, source, .. } => {
                    if *source != pointer {
                        return false;
                    }

                    // GEP returns memory which belongs to the source pointer. Make sure
                    // that GEP return value is safely used.
                    if !self.is_pointer_safely_used(*dst) {
                        return false;
                    }
                }
                Instruction::Alias { dst, .. } => {
                    // Make sure that aliased pointer is safely used.
                    if !self.is_pointer_safely_used(*dst) {
                        return false;
                    }
                }
                Instruction::Phi { dst, .. } => {
                    // Ignore self referential PHIs. TODO: Maybe we should return true here.
                    if *dst == pointer {
                        return false;
                    }

                    // Make sure that resulting pointer is safely used.
                    if !self.is_pointer_safely_used(*dst) {
                        return false;
                    }
                }
                // All other uses (casts, etc..) are not safe and we can't reason about them.
                _ => return false,
            }
        }

        true
    }

    pub(super) fn analyse_pointers(&self) -> PointerAnalysis {
        let mut cx = PointerAnalysisContext {
            analysis: PointerAnalysis {
                origins:     Map::default(),
                stackallocs: Map::default(),
            },
            creators: self.value_creators(),
        };

        macro_rules! calculate_origin {
            ($value: expr) => {
                // Calculate origin if provided value is actually a pointer.
                if self.value_type($value).is_pointer() {
                    let _ = self.get_pointer_origin($value, &mut cx);
                }
            }
        }

        // Go through every instruction and analyze used pointers.
        self.for_each_instruction(|_location, instruction| {
            // Analyze origins of all used/created pointers by this instruction.
            if let Some(value) = instruction.created_value() {
                calculate_origin!(value);
            }
            for value in instruction.read_values() {
                calculate_origin!(value);
            }

            if let Instruction::StackAlloc { dst, .. } = instruction {
                // Get information about stackalloc, check if it's safely used and can't
                // escape.
                let pointer = *dst;
                let safe    = self.is_pointer_safely_used(pointer);

                assert!(cx.analysis.stackallocs.insert(pointer, safe).is_none(),
                        "Multiple pointers from stackalloc?");
            }
        });

        // Analyze origins of arguments to this function.
        for &value in &self.argument_values {
            calculate_origin!(value);
        }

        cx.analysis
    }

    pub(super) fn depends_on_predecessors(&self, label: Label, predecessors: &[Label]) -> bool {
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

                            assert!(existing_new == value, "Tried to replace invalid \
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
        for instruction in &self.blocks[&label] {
            if instruction.is_phi() {
                return true;
            }
        }

        false
    }

    pub(super) fn constant_values(&self) -> Map<Value, (Type, Const)> {
        let mut consts = Map::default();

        self.for_each_instruction(|_location, instruction| {
            match instruction {
                Instruction::Const { dst, imm, ty } => {
                    let imm = *imm as Const;
                    let imm = match ConstType::new(*ty) {
                        ConstType::U1 => {
                            assert!(imm == 0 || imm == 1, "U1 has invalid value {}.", imm);
                            imm
                        }
                        ConstType::U8  => imm as u8  as u64,
                        ConstType::U16 => imm as u16 as u64,
                        ConstType::U32 => imm as u32 as u64,
                        ConstType::U64 => imm as u64 as u64,
                    };

                    assert!(consts.insert(*dst, (*ty, imm)).is_none(),
                            "Multiple constant value creators.");
                }
                Instruction::Alias { dst, value } => {
                    if let Some(&(ty, value)) = consts.get(value) {
                        assert!(consts.insert(*dst, (ty, value)).is_none(),
                                "Multiple constant value creators.");
                    }
                }
                _ => {}
            }
        });

        consts
    }


    /// Check if there is any path that goes from `from` to `to` without going through
    /// `without`.
    fn can_reach(&self, from: Label, to: Label, without: Label) -> bool {
        // Make sure that start and end points are not blacklisted.
        assert!(from != without && to != without);

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

    fn validate_path_internal(
        &self,
        dominators:   &Dominators,
        start:        Location,
        end:          Location,
        memory_kill:  Option<KillTarget>,
        mut verifier: impl FnMut(&Instruction) -> bool,
    ) -> Option<usize> {
        let start_label = start.label();
        let end_label   = end.label();

        let mut instruction_count = 0;

        // Base case: both path points are in the same block.
        if start_label == end_label {
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

        // When path points are in different blocks then start block must dominate end block.
        if self.dominates(dominators, start_label, end_label) {
            // If there is a cycle then other blocks may need to be checked.
            let blocks = memory_kill.and_then(|memory_kill| {
                self.escaping_cycle_blocks(start_label, end_label, memory_kill)
            });

            if let Some(blocks) = blocks {
                for block in blocks {
                    for (inst_id, instruction) in self.blocks[&block].iter().enumerate() {
                        // Ignore start instruction and end instruction.
                        let location = Location::new(block, inst_id);
                        if  location == start || location == end {
                            continue;
                        }

                        if !verifier(instruction) {
                            return None;
                        }

                        // Don't increase the instruction count.
                    }
                }
            }

            // Make sure there is no invalid instruction in the remaining part of start block.
            for instruction in &self.blocks[&start_label][start.index() + 1..] {
                if !verifier(instruction) {
                    return None;
                }

                instruction_count += 1;
            }

            // Make sure there is no invalid instruction in the initial part of end block.
            for instruction in &self.blocks[&end_label][..end.index()] {
                if !verifier(instruction) {
                    return None;
                }

                instruction_count += 1;
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

            for &label in &visited {
                // Don't check `end_label` here because we will only go through part of it and
                // it was already checked before.
                if label != end_label {
                    // `start_label` should never be here.
                    assert!(label != start_label);

                    // Make sure that there is no invalid instruction in every block
                    // that we can hit.
                    for instruction in &self.blocks[&label] {
                        if !verifier(instruction) {
                            return None;
                        }

                        instruction_count += 1;
                    }
                }
            }

            return Some(instruction_count);
        }
        
        None
    }

    pub(super) fn validate_path_memory(
        &self,
        dominators: &Dominators,
        start:      Location,
        end:        Location,
        target:     KillTarget,
        verifier:   impl FnMut(&Instruction) -> bool,
    ) -> Option<usize> {
        self.validate_path_internal(dominators, start, end, Some(target), verifier)
    }

    pub(super) fn validate_path_count(
        &self,
        dominators: &Dominators,
        start:      Location,
        end:        Location,
    ) -> Option<usize> {
        self.validate_path_internal(dominators, start, end, None, |_| true)
    }

    pub(super) fn dominates(&self, dominators: &Dominators,
                            dominator: Label, target: Label) -> bool {
        let mut current = Some(target);

        while let Some(idom) = current {
            if idom == dominator {
                return true;
            }

            current = dominators.get(&idom).copied();
        }

        false
    }

    pub(super) fn validate_path(&self, dominators: &Dominators,
                                start: Location, end: Location) -> bool {
        let start_label = start.label();
        let end_label   = end.label();

        if start_label == end_label {
            return start.index() < end.index();
        }

        self.dominates(dominators, start_label, end_label)
    }

    pub(super) fn validate_ssa(&self) {
        let dominators    = self.dominators();
        let creators      = self.value_creators();
        let flow_incoming = self.flow_graph_incoming();

        for label in self.reachable_labels() {
            let _    = self.targets(label);
            let body = &self.blocks[&label];

            for inst in &body[..body.len() - 1] {
                assert!(inst.targets().is_none(), "Terminator {:?} in the middle of block {}.",
                        inst, label);
            }

            let mut can_see_phi = true;

            for (inst_id, inst) in body.iter().enumerate() {
                if let Some(value) = inst.created_value() {
                    assert!(!self.undefined_set.contains(&value),
                            "Cannot return to undefined value {}.", value);
                }

                if let Instruction::Phi { incoming, .. } = inst {
                    assert!(can_see_phi, "PHI nodes are not at the function beginning.");
                    assert!(label != Label(0), "Entry labels cannot have PHI nodes.");
                    assert!(!incoming.is_empty(), "PHI nodes cannot be empty.");

                    let incoming_labels: Set<Label> = incoming.iter()
                        .map(|(label, _value)| *label)
                        .collect();

                    assert!(incoming_labels == flow_incoming[&label], "PHI node incoming \
                            labels and block predecessors don't match.");

                    assert!(incoming.len() == incoming_labels.len(),
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

                        assert!(self.validate_path(&dominators, creation_loc, usage_loc),
                                "PHI value {} is used before being created.", value);
                    }

                    continue;
                } 

                if !matches!(inst, Instruction::Nop) {
                    can_see_phi = false;
                }

                for value in inst.read_values() {
                    if self.is_value_special(value) {
                        continue;
                    }

                    let creation_loc = *creators.get(&value).expect("Value used but not created.");
                    let usage_loc    = Location::new(label, inst_id);

                    assert!(self.validate_path(&dominators, creation_loc, usage_loc),
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

    pub(super) fn for_each_instruction(&self, mut callback: impl FnMut(Location, &Instruction)) {
        for label in self.reachable_labels() {
            for (inst_id, inst) in self.blocks[&label].iter().enumerate() {
                callback(Location::new(label, inst_id), inst)
            }
        }
    }

    pub(super) fn for_each_instruction_mut(&mut self,
                                           mut callback: impl FnMut(Location, &mut Instruction)) {
        for label in self.reachable_labels() {
            for (inst_id, inst) in self.blocks.get_mut(&label).unwrap().iter_mut().enumerate() {
                callback(Location::new(label, inst_id), inst)
            }
        }
    }

    pub(super) fn usage_counts(&self) -> Vec<u32> {
        let mut usage_counts = vec![0; self.value_count()];

        self.for_each_instruction(|_location, instruction| {
            for value in instruction.read_values() {
                usage_counts[value.index()] += 1;
            }
        });

        usage_counts
    }

    pub(super) fn value_creators(&self) -> Map<Value, Location> {
        let mut creators = Map::default();

        self.for_each_instruction(|location, instruction| {
            if let Some(value) = instruction.created_value() {
                creators.insert(value,location);
            }
        });

        creators
    }

    pub(super) fn find_uses(&self, value: Value) -> Vec<Location> {
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

    pub(super) fn phi_used_values(&self) -> Set<Value> {
        let mut results = Set::default();

        self.for_each_instruction(|_location, instruction| {
            if let Instruction::Phi { incoming, .. } = instruction {
                for (_, value) in incoming {
                    results.insert(*value);
                }
            }
        });

        results
    }
}
