use crate::{FunctionData, Value, Map, Set};

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

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        // This is not an optimization pass. We need to be careful here because `validate_ssa`
        // won't be called after this pass is run.

        let mut values = Values::default();

        // Allocate new values for function arguments.
        for &argument in &function.argument_values {
            let value = values.allocate(argument);

            // Old value and new value must be the same.
            assert!(value == argument, "Argument value allocations don't match.");
        }

        // Allocate new values for all created IR values.
        function.for_each_instruction_mut(|_location, instruction| {
            if let Some(value) = instruction.created_value() {
                values.allocate(value);
            }
        });

        // Allocate new values for undefined values.
        for &undefined in &function.undefined_set {
            values.allocate(undefined);
        }

        // We have now allocated and assigned all required values.
        let values = values;

        // Update inputs and outputs for every instruction.
        function.for_each_instruction_mut(|_location, instruction| {
            let transform = |value: &mut Value| {
                *value = values.map[value];
            };

            instruction.transform_output(transform);
            instruction.transform_inputs(transform);
        });

        // Argument values are the same so we don't need to update them.

        // Update undefined values.
        {
            let mut undefined_set = Set::default();

            for value in function.undefined.values_mut() {
                let new_value = values.map[&value];

                *value = new_value;

                assert!(undefined_set.insert(new_value), "Multiple entries \
                        in undefined set for the same value.");
            }

            function.undefined_set = undefined_set;
        }

        // Update next value index.
        function.next_value = values.next_value;

        // Update function type information.
        function.type_info = function.type_info.take().map(|old_type_info| {
            let mut type_info = Map::default();

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
