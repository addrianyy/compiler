use super::{FunctionData, Value, Location, Label, Dominators, Map};

impl FunctionData {
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
}
