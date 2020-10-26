use std::collections::VecDeque;

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
            _ => true
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
            panic!("Non call instruction provided to `can_call_affect_pointer`.");
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

    pub(super) fn validate_path_ex(
        &self,
        dominators:   &Dominators,
        start:        Location,
        end:          Location,
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
                for inst in &self.blocks[&start_label][start.index() + 1..end.index()] {
                    if !verifier(inst) {
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
            // Make sure there is no invalid instruction in the remaining part of start block.
            for inst in &self.blocks[&start_label][start.index() + 1..] {
                if !verifier(inst) {
                    return None;
                }

                instruction_count += 1;
            }

            // Make sure there is no invalid instruction in the initial part of end block.
            for inst in &self.blocks[&end_label][..end.index()] {
                if !verifier(inst) {
                    return None;
                }

                instruction_count += 1;
            }

            // Find all blocks that are possible to hit when going from start to end.

            let incoming = self.flow_graph_incoming();

            let mut visited = Set::default();
            let mut queue   = VecDeque::new();

            // Start traversing from end of path and go upwards.
            queue.push_back(end_label);
            
            while let Some(label) = queue.pop_front() {
                if !visited.insert(label) {
                    continue;
                }

                // Queue traversal of upper blocks.
                for &predecessor in &incoming[&label] {
                    // Because start block dominates end block we must eventually hit start block
                    // during traversal. In this case we shouldn't go up.
                    if predecessor != start_label {
                        queue.push_back(predecessor);
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
                    for inst in &self.blocks[&label] {
                        if !verifier(inst) {
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
                if let Instruction::Phi { dst, incoming } = inst {
                    assert!(can_see_phi, "PHI nodes are not at the function beginning.");
                    assert!(label != Label(0), "Entry labels cannot have PHI nodes.");
                    assert!(!incoming.is_empty(), "PHI nodes cannot be empty.");

                    let incoming_labels: Set<Label> = incoming.into_iter()
                        .map(|(label, _value)| *label)
                        .collect();

                    assert!(incoming_labels == flow_incoming[&label], "PHI node incoming \
                            labels and block predecessors don't match.");

                    for &(label, value) in incoming {
                        if self.is_value_argument(value) {
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

                can_see_phi = false;

                for value in inst.read_values() {
                    if self.is_value_argument(value) {
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
}
