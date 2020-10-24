use std::collections::{HashSet, VecDeque};

use super::{FunctionData, Value, Location, Label, Dominators, Map, Instruction, Type};

pub(super) type Const = u64;

#[derive(Copy, Clone, PartialEq, Eq)]
pub(super) enum ConstType {
    U1,
    U8,
    U16,
    U32,
    U64,
}

impl ConstType {
    pub(super) fn from_ir_type(ty: Type) -> Option<ConstType> {
        match ty {
            Type::U1  => Some(ConstType::U1),
            Type::U8  => Some(ConstType::U8),
            Type::U16 => Some(ConstType::U16),
            Type::U32 => Some(ConstType::U32),
            Type::U64 => Some(ConstType::U64),
            _         => None,
        }
    }

    pub(super) fn ir_type(&self) -> Type {
        match self {
            ConstType::U1  => Type::U1,
            ConstType::U8  => Type::U8,
            ConstType::U16 => Type::U16,
            ConstType::U32 => Type::U32,
            ConstType::U64 => Type::U64,
        }
    }
}

impl FunctionData {
    pub(super) fn constant_values(&self) -> Map<Value, (ConstType, Const)> {
        let mut consts = Map::new();

        self.for_each_instruction(|_location, instruction| {
            match instruction {
                Instruction::Const { dst, imm, ty } => {
                    let ty = ConstType::from_ir_type(*ty)
                        .unwrap_or_else(|| panic!("Invalid constant type {:?}.", ty));

                    let imm = *imm as Const;
                    let imm = match ty {
                        ConstType::U1  => imm & 1,
                        ConstType::U8  => imm as u8  as u64,
                        ConstType::U16 => imm as u16 as u64,
                        ConstType::U32 => imm as u32 as u64,
                        ConstType::U64 => imm as u64 as u64,
                    };

                    assert!(consts.insert(*dst, (ty, imm)).is_none(),
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
        let start_label = start.0;
        let end_label   = end.0;

        if start_label == end_label {
            return start.1 < end.1;
        }

        self.dominates(dominators, start_label, end_label)
    }

    pub(super) fn validate_path_ex(&self, dominators: &Dominators,
                                   start: Location, end: Location,
                                   mut verifier: impl FnMut(&Instruction) -> bool) -> bool {
        let start_label = start.0;
        let end_label   = end.0;

        // Base case: both path points are in the same block.
        if start_label == end_label {
            // Start must be before end to make valid path.
            if start.1 < end.1 {
                // Verify all instructions between `start` and `end`.
                for inst in &self.blocks[&start_label][start.1 + 1..end.1] {
                    if !verifier(inst) {
                        return false;
                    }
                }

                return true;
            }

            return false;
        }

        // When path points are in different blocks then start block must dominate end block.
        if self.dominates(dominators, start_label, end_label) {
            // Make sure there is no invalid instruction in the remaining part of start block.
            for inst in &self.blocks[&start_label][start.1 + 1..] {
                if !verifier(inst) {
                    return false;
                }
            }

            // Make sure there is no invalid instruction in the initial part of end block.
            for inst in &self.blocks[&end_label][..end.1] {
                if !verifier(inst) {
                    return false;
                }
            }

            // Find all blocks that are possible to hit when going from start to end.

            let incoming = self.flow_graph_incoming();

            let mut visited = HashSet::new();
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
                            return false;
                        }
                    }
                }
            }

            return true;
        }
        
        false
    }

    pub(super) fn instruction(&self, location: Location) -> &Instruction {
        &self.blocks[&location.0][location.1]
    }

    pub(super) fn instruction_mut(&mut self, location: Location) -> &mut Instruction {
        &mut self.blocks.get_mut(&location.0).unwrap()[location.1]
    }

    pub(super) fn for_each_instruction(&self, mut callback: impl FnMut(Location, &Instruction)) {
        for label in self.reachable_labels() {
            for (inst_id, inst) in self.blocks[&label].iter().enumerate() {
                callback(Location(label, inst_id), inst)
            }
        }
    }

    pub(super) fn for_each_instruction_mut(&mut self, 
                                           mut callback: impl FnMut(Location, &mut Instruction)) {
        for label in self.reachable_labels() {
            for (inst_id, inst) in self.blocks.get_mut(&label).unwrap().iter_mut().enumerate() {
                callback(Location(label, inst_id), inst)
            }
        }
    }

    pub(super) fn validate_ssa(&self) {
        let labels     = self.reachable_labels();
        let dominators = self.dominators();
        let creators   = self.value_creators();

        for &label in &labels {
            let _    = self.targets(label);
            let body = &self.blocks[&label];

            for inst in &body[..body.len() - 1] {
                assert!(inst.targets().is_none(), "Terminator {:?} in the middle of block {}.",
                        inst, label);
            }

            for (inst_id, inst) in body.iter().enumerate() {
                for value in inst.read_values() {
                    if self.is_value_argument(value) {
                        continue;
                    }

                    let creation_loc = *creators.get(&value).expect("Value used but not created.");
                    let usage_loc    = Location(label, inst_id);

                    assert!(self.validate_path(&dominators, creation_loc, usage_loc),
                            "Value {} is used before being created.", value);
                }
            }
        }
    }

    pub(super) fn value_creators(&self) -> Map<Value, Location> {
        let mut creators = Map::new();

        for label in self.reachable_labels() {
            let body = &self.blocks[&label];

            for (inst_id, inst) in body.iter().enumerate() {
                if let Some(value) = inst.created_value() {
                    creators.insert(value, Location(label, inst_id));
                }
            }
        }

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

        self.for_each_instruction(|location, inst| {
            if let Instruction::StackAlloc { dst, size, .. } = inst {
                if required_size.is_none() || Some(*size) == required_size {
                    results.push((*dst, location));
                }
            }
        });

        results
    }
}
