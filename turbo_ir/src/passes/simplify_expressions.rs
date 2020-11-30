use crate::{FunctionData, Instruction, Value, ConstType, BinaryOp, Map, Type, Location, Label};

#[derive(Clone)]
struct Chain {
    value:  Value,
    consts: Vec<u64>,
    ty:     ConstType,
    op:     BinaryOp,
}

fn rebuild_creators_in_block(function: &FunctionData, creators: &mut Map<Value, Location>,
                             label: Label, start_index: usize) {
    for (inst_id, instruction) in function.blocks[&label][start_index..].iter().enumerate() {
        let inst_id  = inst_id + start_index;
        let location = Location::new(label, inst_id);

        if let Some(value) = instruction.created_value() {
            creators.insert(value, location);
        }
    }
}

pub struct SimplifyExpressionsPass;

impl super::Pass for SimplifyExpressionsPass {
    fn name(&self) -> &str {
        "expression simplification"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::simplify_expressions()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let labels = function.reachable_labels();

        let mut did_something             = false;
        let mut chains: Map<Value, Chain> = Map::default();
        let mut creators                  = function.value_creators_with_labels(&labels);
        let mut consts                    = function.constant_values_with_labels(&labels);

        // Chain commulative operations with at least two constant operands.
        // (a + 1) + 1
        //
        // Gets optimized to:
        // a + 2
        //
        // TODO: Make a tree-based expression simplifier.

        // Evaluate chain of (a op (C1 op (C2 op C3))) to (a op C).
        macro_rules! evaluate_chain {
            ($chain: expr, $type: ty) => {{
                let chain: &Chain = $chain;

                // Current partial value of right hand side expression. There must be
                // at least one constant there.
                let mut current = chain.consts[0] as $type;

                // Calculate whole value of right hand side expression.
                for &constant in &chain.consts[1..] {
                    let constant = constant as $type;

                    let a = current;
                    let b = constant;

                    let result = match chain.op {
                        BinaryOp::Add => a.wrapping_add(b),
                        BinaryOp::Mul => a.wrapping_mul(b),
                        BinaryOp::And => a & b,
                        BinaryOp::Or  => a | b,
                        BinaryOp::Xor => a ^ b,
                        _             => unreachable!(),
                    };

                    current = result;
                }

                current as u64
            }}
        }

        {
            time!(build_expression_chains);

            function.for_each_instruction_with_labels(&labels, |_, instruction| {
                // We only simplify binary expressions for now.
                if let Instruction::ArithmeticBinary { dst, a, op, b } = instruction {
                    // If operator is associative then (a op b) op c == a op (a b).
                    // We cannot chain non-associative operations.
                    if !op.is_associative() {
                        return;
                    }

                    // Get 1 unknown value, 1 constant value and return type.
                    let result = match (consts.get(a), consts.get(b)) {
                        (Some(&a), None) => Some((*b, a.1, ConstType::new(a.0))),
                        (None, Some(&b)) => Some((*a, b.1, ConstType::new(b.0))),
                        _                => None,
                    };

                    // If there are 2 constant values or 2 unknown values we can't do anything.
                    if let Some((value, constant, ty)) = result {
                        let chain = match chains.get(&value) {
                            Some(chain) => {
                                // This is next part of previously calculated chain.
                                // We cannot chain both operations if they have different
                                // binary operator.
                                if chain.op != *op {
                                    None
                                } else {
                                    // Join current operation and previous chain into one.

                                    let mut chain = chain.clone();
                                    chain.consts.push(constant);

                                    Some(chain)
                                }
                            }
                            None => {
                                // Beginning of the chain, with one value and one constant.
                                Some(Chain {
                                    value,
                                    consts: vec![constant],
                                    op:     *op,
                                    ty,
                                })
                            }
                        };

                        if let Some(chain) = chain {
                            // This value has a valid expression chain, add it to the list.
                            assert!(chains.insert(*dst, chain).is_none(),
                                    "Multiple chains from the same value?");
                        }
                    }
                }
            });
        }

        // Evaluate all chain and replace instructions.
        for (output_value, chain) in &chains {
            // We don't gain anything from simplifying already simple chains.
            if chain.consts.len() <= 1 {
                continue;
            }

            // Evaluate right hand side of the chain. It must be integer value.
            let (chain_value, ir_type) = match chain.ty {
                ConstType::U1  => unreachable!(),
                ConstType::U8  => (evaluate_chain!(&chain, u8),  Type::U8),
                ConstType::U16 => (evaluate_chain!(&chain, u16), Type::U16),
                ConstType::U32 => (evaluate_chain!(&chain, u32), Type::U32),
                ConstType::U64 => (evaluate_chain!(&chain, u64), Type::U64),
            };

            // Create instructions which will create RHS constant and calculate simplified
            // expression.
            let temp_constant = function.allocate_typed_value(ir_type);
            let simplified    = vec![
                Instruction::Const {
                    dst: temp_constant,
                    ty:  ir_type,
                    imm: chain_value,
                },
                Instruction::ArithmeticBinary {
                    dst: *output_value,
                    a:   chain.value,
                    op:  chain.op,
                    b:   temp_constant,
                },
            ];

            // Add new constant to the list.
            consts.insert(temp_constant, (ir_type, chain_value));

            // Get the block which created expression which we are going to simplify.
            let creator = creators[&output_value];
            let body    = function.blocks.get_mut(&creator.label()).unwrap();

            // Remove old, complex expression.
            body.remove(creator.index());

            // Insert new, simplified expression to the block.
            for instruction in simplified.into_iter().rev() {
                body.insert(creator.index(), instruction);
            }

            // We have modified `creator.label()` so we need to rebuild creators for it.
            rebuild_creators_in_block(function, &mut creators, creator.label(), creator.index());

            did_something = true;
        }

        did_something
    }
}
