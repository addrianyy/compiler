use crate::{FunctionData, Value, Map, Set, CapacityExt};

#[derive(Default)]
struct Values {
    next_value: Value,
    map:        Map<Value, Value>,
}

impl Values {
    fn allocate(&mut self, previous: Value) -> Value {
        let value = self.next_value;

        self.next_value = Value(value.0.checked_add(1)
                                .expect("Value IDs overflowed."));

        self.map.insert(previous, value);

        value
    }
}

pub struct RewriteValuesPass;

impl super::Pass for RewriteValuesPass {
    fn name(&self) -> &str {
        "rewrite values"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::rewrite_values()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        // This is not an optimization pass. We need to be careful here because `validate_ssa`
        // won't be called after this pass is run.

        let mut values = Values::default();

        // Use DFS traversal to match value order in `dump` routines.
        let labels = function.reachable_labels_dfs();

        // Allocate new values for function arguments.
        for &argument in &function.argument_values {
            let value = values.allocate(argument);

            // Old value and new value must be the same.
            assert_eq!(value, argument, "Argument value allocations don't match.");
        }

        // Allocate new values for all created IR values.
        function.for_each_instruction_with_labels_mut(&labels, |_location, instruction| {
            if let Some(value) = instruction.created_value() {
                values.allocate(value);
            }
        });

        // Allocate new values for undefined values.
        for &undefined in &function.undefined_set {
            values.allocate(undefined);
        }

        // Allocate new values for constant values.
        for &constant in function.constants.keys() {
            values.allocate(constant);
        }

        // We have now allocated and assigned all required values.
        let values = values;

        // Update inputs and outputs for every instruction.
        function.for_each_instruction_with_labels_mut(&labels, |_location, instruction| {
            let transform = |value: &mut Value| {
                *value = values.map[value];
            };

            instruction.transform_output(transform);
            instruction.transform_inputs(transform);
        });

        // Argument values are the same so we don't need to update them.

        // Update undefined values.
        {
            let mut undefined_set = Set::new_with_capacity(function.undefined.len());

            for value in function.undefined.values_mut() {
                let new_value = values.map[&value];

                *value = new_value;

                assert!(undefined_set.insert(new_value), "Multiple entries \
                        in undefined set for the same value.");
            }

            function.undefined_set = undefined_set;
        }

        // Update constant values.
        {
            let mut constants = Map::new_with_capacity(function.constants.len());

            for (&(ty, constant), value) in &mut function.constant_to_value {
                let new_value = values.map[value];

                *value = new_value;

                assert!(constants.insert(new_value, (ty, constant)).is_none(), "Multiple entries \
                        in constants map for the same value.");
            }

            function.constants = constants;
        }

        // Update next value index.
        function.next_value = values.next_value;

        // Update function type information.
        function.type_info = function.type_info.take().map(|old_type_info| {
            let mut type_info = Map::new_with_capacity(old_type_info.len());

            for (value, ty) in old_type_info {
                // Previous type information can include types of now non-existent values.
                if let Some(&value) = values.map.get(&value) {
                    assert!(type_info.insert(value, ty).is_none(), "Multiple entries \
                            in type info for the same value.");
                }
            }

            type_info
        });

        // `phi_locations` should be empty and shouldn't require update.
        assert!(function.phi_locations.is_empty(), "PHI locations map \
                wasn't empty during rewrite.");

        // This pass doesn't optimize anything.
        false
    }
}
