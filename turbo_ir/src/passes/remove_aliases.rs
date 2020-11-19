use crate::{FunctionData, Instruction, Set};

pub struct RemoveAliasesPass;

impl super::Pass for RemoveAliasesPass {
    fn name(&self) -> &str {
        "alias elimination"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::remove_aliases()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;
        let     labels        = function.reachable_labels();

        // Some optimization passess will create alias instruction.
        // If v1 is aliased to v0 that means that v1 has always exact value as v0.
        // This optimization pass will actually remove alias instruction and change
        // all uses of its return value to its operand.
        //
        // v2 = alias v1
        // v3 = add u32 v2, v0
        //
        // This will get optimized to:
        // v3 = add u32 v1, v0

        let mut users      = function.users_with_labels(&labels);
        let mut new_users  = Vec::new();
        let mut next_index = 0;

        loop {
            let mut alias = None;

            // Go through every instruction in every block to find alias instruction.
            'alias_search: for (index, &label) in labels[next_index..].iter().enumerate() {
                let body = function.blocks.get_mut(&label).unwrap().iter_mut();

                for instruction in body {
                    if let Instruction::Alias { dst, value } = instruction {
                        // Record replacement information for this alias.
                        alias = Some((*dst, *value));

                        // Remove alias instruction.
                        *instruction = Instruction::Nop;

                        // Start from this label next time.
                        next_index += index;

                        // Break out to perform the replacement.
                        break 'alias_search;
                    }
                }
            }

            if let Some((old, new)) = alias {
                // We start with no new users of `new` value.
                new_users.clear();

                if let Some(old_users) = users.get(&old) {
                    new_users.reserve(users.len());

                    // Go through every possible user and change `old` inputs to `new` inputs.
                    for &user in old_users {
                        let instruction = function.instruction_mut(user);
                        let mut changed = false;

                        instruction.transform_inputs(|value| {
                            if *value == old {
                                *value  = new;
                                changed = true;
                            }
                        });

                        // If we have changed input then `user` is now user of `new` too.
                        if changed {
                            new_users.push(user);
                        }
                    }

                    // Nobody uses `old` anymore.
                    // users.remove(&old);
                    //
                    // This seems to slow down algorithm and is not needed to don't remove it
                    // actually.
                }

                // If there are new users of `new` then fill them in.
                if !new_users.is_empty() {
                    let users = users.entry(new)
                        .or_insert_with(Set::default);

                    users.reserve(new_users.len());

                    // Add new users of `new` value.
                    for &new_user in &new_users {
                        users.insert(new_user);
                    }
                }

                did_something = true;

                // Maybe there are more aliases to handle. Continue to the next iteration.
                continue;
            }

            // No alias was found, we can stop searching.
            break;
        }

        did_something
    }
}
