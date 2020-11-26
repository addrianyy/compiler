use crate::{FunctionData, Instruction, Map, BinaryOp, UnaryOp, Type, Cast, IntPredicate, Value};

#[derive(Default, Copy, Clone, Debug)]
struct KnownBits {
    mask:  u64,
    known: u64,
}

impl KnownBits {
    fn sign(&self, ty: Type) -> Option<bool> {
        let ty_size = ty.size_bits();

        if self.mask & (1 << (ty_size - 1)) != 0 {
            return Some((self.known >> (ty_size - 1)) != 0);
        }

        None
    }
}

fn combine_known_bits(kb1: &KnownBits, kb2: &KnownBits) -> KnownBits {
    // Get common mask for `kb1` and `kb2`.
    let common_mask = kb1.mask & kb2.mask;

    // Adjust known values with new common mask.
    let kb1_known = kb1.known & common_mask;
    let kb2_known = kb2.known & common_mask;

    // Create mask without differing known bits.
    let valid_mask = !(kb1_known ^ kb2_known);

    // Combine known bits.
    KnownBits {
        mask:  common_mask & valid_mask,
        known: (kb1_known | kb2_known) & valid_mask,
    }
}

/// Try to compare two positive integers.
fn bit_compare_greater(a_bits: &KnownBits, b_bits: &KnownBits, ty: Type) -> Option<bool> {
    // Go through every bit from MSB to LSB.
    for idx in (0..ty.size_bits()).rev() {
        let m = 1 << idx;

        // If this bit is not known in both operands we cannot continue.
        if (a_bits.mask & m) == 0 || (b_bits.mask & m) == 0 {
            return None;
        }

        // Extract bit values.
        let bit_a = (a_bits.known >> idx) & 1 != 0;
        let bit_b = (b_bits.known >> idx) & 1 != 0;

        if bit_a != bit_b {
            // This is first bit from MSB that is different in `a` and `b`.
            // If `a` has this bit set it means that `a` is > `b`.
            return Some(bit_a);
        }
    }

    None
}

#[allow(unused)]
fn dump_known_bits(function: &FunctionData, known_bits: &Map<Value, KnownBits>) {
    println!("Known bits for {}:", function.prototype.name);

    for (value, known_bits) in known_bits {
        if known_bits.mask == 0 {
            continue;
        }

        print!("{}", value);

        if value.0 < 10 {
            print!(" ");
        }

        print!(": ");

        let size = function.value_type(*value).size_bits();

        for idx in (0..size).rev() {
            let mask = 1 << idx;

            if known_bits.mask & mask == 0 {
                print!("_");
            } else {
                print!("{}", (known_bits.known >> idx) & 1);
            }
        }

        println!();
    }

    println!();
}

pub struct OptimizeKnownBitsPass;

impl super::Pass for OptimizeKnownBitsPass {
    fn name(&self) -> &str {
        "bit optimization"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::optimize_known_bits()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut did_something = false;

        let labels           = function.reachable_labels();
        let processing_order = function.value_processing_order_with_labels(&labels);
        let consts           = function.constant_values_with_labels(&labels);
        let creators         = function.value_creators_with_labels(&labels);
        
        let mut known_bits = Map::default();

        for value in processing_order {
            let mut computed    = KnownBits::default();
            let mut replacement = None;
            let ty              = function.value_type(value);
            let ty_size         = ty.size_bits();
            let ty_bitmask      = ty.bitmask();

            if let Some(creator) = creators.get(&value).copied() {
                let instruction = function.instruction_mut(creator);

                match instruction {
                    Instruction::Const { imm, .. } => {
                        computed.mask  = ty_bitmask;
                        computed.known = *imm;
                    }
                    Instruction::Alias { value, .. } => {
                        computed = known_bits[value];
                    }
                    Instruction::ArithmeticUnary { op, value, .. } => {
                        match op {
                            UnaryOp::Not => {
                                // Invert all known bits.
                                computed       =  known_bits[value];
                                computed.known = !computed.known & computed.mask;
                            }
                            UnaryOp::Neg => {
                                // TODO: Don't just invert the sign bit.
                                if let Some(sign) = known_bits[value].sign(ty) {
                                    let mask = 1 << (ty_size - 1);

                                    computed.mask |= mask;

                                    if !sign {
                                        computed.known |= mask;
                                    }
                                }
                            }
                        }
                    }
                    Instruction::ArithmeticBinary { dst, a, op, b } => {
                        let dst     = *dst;
                        let a_value = *a;
                        let b_value = *b;

                        let a = known_bits[a];
                        let b = known_bits[b];

                        match op {
                            BinaryOp::Or | BinaryOp::And | BinaryOp::Xor => {
                                // Get common `known` and `mask` for two operands.
                                let mut mask  = a.mask & b.mask;
                                let mut known = match op {
                                    BinaryOp::Or  => a.known | b.known,
                                    BinaryOp::And => a.known & b.known,
                                    BinaryOp::Xor => a.known ^ b.known,
                                    _             => unreachable!(),
                                } & mask;

                                // `and` and `or` can give us more information about known bits.
                                if *op != BinaryOp::Xor {
                                    // Check every bit.
                                    for idx in 0..ty.size_bits() {
                                        let m = 1 << idx;

                                        match op {
                                            BinaryOp::Or => {
                                                // If this bit is one in at least one operand
                                                // than destination will be one too.

                                                let a_one = (a.known & m != 0) &&
                                                            (a.mask  & m != 0);

                                                let b_one = (b.known & m != 0) &&
                                                            (b.mask  & m != 0);

                                                if a_one || b_one {
                                                    mask  |= m;
                                                    known |= m;
                                                }
                                            }
                                            BinaryOp::And => {
                                                // If this bit is zero in at least zero operand
                                                // than destination will be zero too.

                                                let a_zero = (a.known & m == 0) &&
                                                             (a.mask  & m != 0);

                                                let b_zero = (b.known & m == 0) &&
                                                             (b.mask  & m != 0);

                                                if a_zero || b_zero {
                                                    mask  |= m;
                                                    known &= !m;
                                                }
                                            }
                                            _ => unreachable!(),
                                        }
                                    }

                                    // If one operand is constant maybe we can prove that
                                    // this operation is unneccesary.
                                    if a.mask == ty_bitmask || b.mask == ty_bitmask {
                                        // Get fully known value and partially known value.
                                        let (bits, value, operand) = if a.mask == ty_bitmask {
                                            (b, a.known, b_value)
                                        } else if b.mask == ty_bitmask {
                                            (a, b.known, a_value)
                                        } else {
                                            unreachable!()
                                        };

                                        let mut alias = None;

                                        // Check if this operation can affect the result. If
                                        // it can't, optimize it out.
                                        match op {
                                            BinaryOp::And => {
                                                // 1. Make sure that all 0 bits in `value`
                                                //    are known.
                                                // 2. Make sure that and doesn't affect known bits.
                                                if ((!bits.mask & !value) & ty_bitmask) == 0 &&
                                                   (bits.known & value) == bits.known {
                                                    alias = Some(operand);
                                                }
                                            }
                                            BinaryOp::Or => {
                                                // 1. Make sure that all 1 bits in `value`
                                                //    are known.
                                                // 2. Make sure that or doesn't affect known bits.
                                                if ((!bits.mask & value) & ty_bitmask) == 0 &&
                                                   (bits.known | value) == bits.known {
                                                    alias = Some(operand);
                                                }
                                            }
                                            _ => unreachable!(),
                                        }

                                        // Replace unneeded instruction.
                                        if let Some(alias) = alias {
                                            replacement = Some(Instruction::Alias {
                                                dst,
                                                value: alias,
                                            });
                                        }
                                    }
                                }

                                computed.mask  = mask;
                                computed.known = known;
                            }
                            BinaryOp::Shl | BinaryOp::Shr | BinaryOp::Sar => {
                                if let Some((_, amount)) = consts.get(&b_value).copied() {
                                    // Shift known bits by the specified amount.
                                    let (mut mask, mut known) = match op {
                                        BinaryOp::Shl => (a.mask << amount, a.known << amount),
                                        BinaryOp::Shr | BinaryOp::Sar => {
                                            (a.mask >> amount, a.known >> amount)
                                        }
                                        _ => unreachable!(),
                                    };

                                    if amount != 0 {
                                        // Some bits after shifting may become known.
                                        // Calculate mask of shifted out bits.
                                        let mut amount_mask = 0;

                                        for idx in 0..amount {
                                            amount_mask |= 1 << idx;
                                        }

                                        match op {
                                            BinaryOp::Shl => {
                                                // All shifted bits become zero.
                                                mask  |=  amount_mask;
                                                known &= !amount_mask;
                                            }
                                            BinaryOp::Shr => {
                                                // All shifted bits become zero. Shifted bits
                                                // are on the right side.
                                                let amount_mask = amount_mask <<
                                                    (ty_size - amount as usize);

                                                mask  |=  amount_mask;
                                                known &= !amount_mask;
                                            }
                                            BinaryOp::Sar => {
                                                // Bits become known only if `a` sign bit is known.
                                                if let Some(sign) = a.sign(ty) {
                                                    // All shifted bits become equal to sign
                                                    // of `a`. Shifted bits are on the right side.
                                                    let amount_mask = amount_mask <<
                                                        (ty_size - amount as usize);

                                                    mask |= amount_mask;

                                                    if !sign {
                                                        known &= !amount_mask;
                                                    } else {
                                                        known |= amount_mask;
                                                    }
                                                }
                                            }
                                            _ => unreachable!(),
                                        }
                                    }

                                    computed.mask  = mask;
                                    computed.known = known;
                                }

                                // If we are sure that the sign bit is 0 than we can
                                // optimize `sar` to `shr`.
                                if *op == BinaryOp::Sar {
                                    if let Some(false) = a.sign(ty) {
                                        *op           = BinaryOp::Shr;
                                        did_something = true;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    Instruction::Select { on_true, on_false, .. } => {
                        let on_true  = known_bits[on_true];
                        let on_false = known_bits[on_false];

                        computed = combine_known_bits(&on_true, &on_false);
                    }
                    Instruction::Phi { incoming, .. } => {
                        let mut first = true;

                        for (_, value) in incoming {
                            if let Some(known) = known_bits.get(value) {
                                if first {
                                    computed = *known;
                                    first    = false;
                                } else {
                                    computed = combine_known_bits(&computed, &known);
                                }
                            } else {
                                // Cannot get known bits for all PHI incoming values.
                                computed.mask  = 0;
                                computed.known = 0;
                                break;
                            }
                        }
                    }
                    &mut Instruction::IntCompare { dst, a, pred, b, .. } => {
                        let ty    = function.value_type(a);
                        let mut a = known_bits[&a];
                        let mut b = known_bits[&b];

                        // Try to resolve `icmp` result using known bits.
                        let result = match pred {
                            IntPredicate::Equal | IntPredicate::NotEqual => {
                                // Quickly prove inequality by comparing operands known bits.
                                let common_mask = a.mask & b.mask;
                                let not_equal   = (a.known & common_mask) !=
                                                  (b.known & common_mask);

                                if not_equal {
                                    match pred {
                                        IntPredicate::Equal    => Some(false),
                                        IntPredicate::NotEqual => Some(true),
                                        _                      => unreachable!(),
                                    }
                                } else {
                                    // We can only prove inequality, we don't know if values
                                    // are equal.
                                    None
                                }
                            }
                            IntPredicate::GtS | IntPredicate::GteS => {
                                if let (Some(a_sign), Some(b_sign)) = (a.sign(ty), b.sign(ty)) {
                                    if a_sign != b_sign {
                                        // If `b` is negative than `a` is positive and `a` is
                                        // always > and >= `b`.
                                        Some(b_sign)
                                    } else if !a_sign {
                                        // Compare positive integers.
                                        bit_compare_greater(&a, &b, ty)
                                    } else {
                                        // Fake positive integers. Because of how
                                        // `bit_comapre_greator` works it shouldn't affect results.
                                        a.known = !a.known & a.mask;
                                        b.known = !b.known & b.mask;

                                        bit_compare_greater(&a, &b, ty)
                                    }
                                } else {
                                    // We cannot reason about this compare because we don't know
                                    // sign bits of both inputs.
                                    None
                                }
                            }
                            IntPredicate::GtU | IntPredicate::GteU => {
                                bit_compare_greater(&a, &b, ty)
                            }
                        };

                        // If comparison result is constant than replace `icmp` with that constant.
                        if let Some(result) = result {
                            replacement = Some(Instruction::Const {
                                dst,
                                ty:  Type::U1,
                                imm: result as u64,
                            });
                        }
                    }
                    &mut Instruction::Cast { cast, value, .. } => {
                        let input_ty      = function.value_type(value);
                        let input_bitmask = input_ty.bitmask();
                        let value         = known_bits[&value];

                        match cast {
                            Cast::Truncate | Cast::Bitcast => {
                                // Just carry over previous known value and mask off truncated
                                // part.
                                computed.mask  &= ty_bitmask;
                                computed.known &= ty_bitmask;
                            }
                            Cast::SignExtend | Cast::ZeroExtend => {
                                // Try to get value of extension bit.
                                let extension_bit = match cast {
                                    Cast::ZeroExtend => Some(false),
                                    Cast::SignExtend => value.sign(input_ty),
                                    _                => unreachable!(),
                                };

                                // Add new extension known bits.
                                if let Some(extension_bit) = extension_bit {
                                    // Calculate mask of all bits that will be set to
                                    // `extension_bit`.
                                    let extension_mask = ty_bitmask & !input_bitmask;

                                    computed.mask |= extension_mask;

                                    if extension_bit {
                                        computed.known |= extension_mask;
                                    } else {
                                        computed.known &= !extension_mask;
                                    }
                                }

                                // Copy bit information of original input to lower part of output.
                                computed.known |= value.known;
                                computed.mask  |= value.mask;
                            }
                        }
                    }
                    _ => {}
                }

                if let Some(replacement) = replacement {
                    let instruction = function.instruction_mut(creator);

                    *instruction  = replacement;
                    did_something = true;
                } else if computed.mask == ty_bitmask {
                    // If all bits are known and this value isn't a constant than replace
                    // instruction with a constant.
                    let mut stripped = value;

                    // Strip aliases.
                    loop {
                        if let Some(creator) = creators.get(&stripped) {
                            let instruction = function.instruction(*creator);

                            if let Instruction::Alias { value, .. } = instruction {
                                stripped = *value;
                                continue;
                            }
                        }

                        break;
                    }

                    if let Some(creator) = creators.get(&stripped) {
                        let instruction = function.instruction_mut(*creator);

                        if !matches!(instruction, Instruction::Const { .. }) {
                            *instruction = Instruction::Const {
                                dst: instruction.created_value().unwrap(),
                                imm: computed.known,
                                ty,
                            };

                            did_something = true;
                        }
                    }
                }
            }

            assert!(!computed.mask & computed.known == 0, "Computed invalid known bits.");

            known_bits.insert(value, computed);
        }

        //dump_known_bits(function, &known_bits);

        did_something
    }
}