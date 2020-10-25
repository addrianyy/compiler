use super::{FunctionData, Value, Location, Map, Type, TypeInfo, Instruction, Cast};

struct TypeContext {
    creators:  Map<Value, Location>,
    type_info: TypeInfo,
}

impl FunctionData {
    fn infer_value_type(&self, value: Value, cx: &mut TypeContext) -> Type {
        macro_rules! get_type {
            ($value: expr) => {
                self.infer_value_type($value, cx)
            }
        }

        if let Some(&ty) = cx.type_info.get(&value) {
            return ty;
        }

        let creator = cx.creators.get(&value).expect("Value is used without being created.");
        let creator = &self.blocks[&creator.label()][creator.index()];

        let ty = match creator {
            Instruction::ArithmeticUnary { value, .. } => {
                get_type!(*value)
            }
            Instruction::ArithmeticBinary { a, b, .. } => {
                let a = get_type!(*a);
                let b = get_type!(*b);

                assert!(a == b, "Binary arithmetic instruction must have operands \
                                 of the same type.");

                a
            }
            Instruction::IntCompare { a, b, .. } => {
                let a = get_type!(*a);
                let b = get_type!(*b);

                assert!(a == b, "Int compare instruction must have operands \
                                 of the same type.");
                Type::U1
            }
            Instruction::Load { ptr, .. } => {
                get_type!(*ptr)
                    .strip_ptr()
                    .expect("Cannot load non-pointer value.")
            }
            Instruction::Call { func, .. } => {
                self.function_prototype(*func)
                    .return_type
                    .expect("Void function return value is used.")
            }
            Instruction::Select { on_true, on_false, .. } => {
                let on_true  = get_type!(*on_true);
                let on_false = get_type!(*on_false);

                assert!(on_true == on_false, "Select instruction must have operands \
                                              of the same type.");

                on_true
            }
            Instruction::StackAlloc    { ty, ..     } => ty.ptr(),
            Instruction::Const         { ty, ..     } => *ty,
            Instruction::GetElementPtr { source, .. } => get_type!(*source),
            Instruction::Cast          { ty, ..     } => *ty,
            Instruction::Alias         { value, ..  } => get_type!(*value),
            _ => {
                panic!("Unexpected value creator: {:?}.", creator);
            }
        };

        assert!(cx.type_info.insert(value, ty).is_none(),
                "Value has type infered multiple times.");
        ty
    }

    fn typecheck(&self, inst: &Instruction, cx: &mut TypeContext) {
        macro_rules! get_type {
            ($value: expr) => {
                self.infer_value_type($value, cx)
            }
        }

        match inst {
            Instruction::ArithmeticUnary { dst, value, .. } => {
                let dst   = get_type!(*dst);
                let value = get_type!(*value);

                assert!(dst == value, "Unary arithmetic instruction requires all \
                        operands to be of the same type");

                assert!(dst.is_arithmetic(), "Unary arithmetic instruction can be \
                        only done on arithmetic types.");
            }
            Instruction::ArithmeticBinary { dst, a, b, .. } => {
                let dst = get_type!(*dst);
                let a   = get_type!(*a);
                let b   = get_type!(*b);

                assert!(dst == a && a == b, "Binary arithmetic instruction requires all \
                        operands to be of the same type");

                assert!(dst.is_arithmetic(), "Binary arithmetic instruction can be \
                        only done on arithmetic types.");
            }
            Instruction::IntCompare { dst, a, b, .. } => {
                let dst = get_type!(*dst);
                let a   = get_type!(*a);
                let b   = get_type!(*b);

                assert!(dst == Type::U1, "Int compare instruction requires \
                        destination type to be U1.");

                assert!(a == b, "Int compare instruction requires all \
                        input operands to be of the same type");

                assert!(a.is_arithmetic() || a == Type::U1, "Int compare instruction can be \
                        only done on arithmetic types or U1.");
            }
            Instruction::Load { dst, ptr } => {
                let dst = get_type!(*dst);
                let ptr = get_type!(*ptr);

                let stripped = ptr.strip_ptr()
                    .expect("Load instruction can only load from pointers.");

                assert!(dst == stripped,
                        "Load instruction destination must have pointee type.");
            }
            Instruction::Store { ptr, value } => {
                let ptr   = get_type!(*ptr);
                let value = get_type!(*value);

                let stripped = ptr.strip_ptr()
                    .expect("Store instruction can only store to pointers.");

                assert!(value == stripped,
                        "Store instruction value must have pointee type.");
            }
            Instruction::Call { dst, func, args } => {
                let prototype = self.function_prototype(*func);

                if let Some(dst) = dst {
                    let return_type = prototype.return_type
                        .expect("Cannot take the return value of void function.");

                    assert!(get_type!(*dst) == return_type,
                            "Function call return value doesn't match.");
                }

                assert!(args.len() == prototype.arguments.len(), "Function call with invalid \
                        argument count.");

                for (index, arg) in args.iter().enumerate() {
                    assert!(get_type!(*arg) == prototype.arguments[index],
                            "Function call with invalid arguments.");
                }
            }
            Instruction::Branch { .. } => {
            }
            Instruction::BranchCond { cond, .. } => {
                let cond = get_type!(*cond);

                assert!(cond == Type::U1, "Conditional branch input must be U1.");
            }
            Instruction::StackAlloc { dst, ty, size } => {
                let dst = get_type!(*dst);

                assert!(*size > 0, "Stack alloc cannot allocate 0 sized array.");
                assert!(dst.strip_ptr().expect("Stack alloc destination must be pointer.") == *ty,
                        "Stack alloc destination must be pointer to input type.");
            }
            Instruction::Return { value } => {
                let value = value.map(|value| get_type!(value));

                assert!(value == self.prototype.return_type, "Return instruction operand type \
                        must be the same function as function return type.");
            }
            Instruction::Const { dst, ty, imm, .. } => {
                let dst = get_type!(*dst);

                if *ty == Type::U1 {
                    assert!(*imm == 0 || *imm == 1, "Invalid U1 constant {}.", imm);
                }

                assert!(dst == *ty, "Const value instruction operand types must be the same.");
            }
            Instruction::GetElementPtr { dst, source, index } => {
                let dst    = get_type!(*dst);
                let source = get_type!(*source);
                let index  = get_type!(*index);

                assert!(index.is_arithmetic(), "GEP index must be arithmetic.");
                assert!(dst == source, "GEP destination and source must be the same type.");
                assert!(dst.is_pointer(), "GEP input type is not valid pointer.");
            }
            Instruction::Cast { dst, cast, value, ty } => {
                let dst   = get_type!(*dst);
                let value = get_type!(*value);

                assert!(dst == *ty, "{} destination must be the same type as cast type.", cast);

                match cast {
                    Cast::ZeroExtend | Cast::SignExtend | Cast::Truncate => {
                        assert!(value.is_arithmetic() && ty.is_arithmetic(),
                                "Both types in {} must be arithmetic.", cast);

                        if *cast == Cast::Truncate {
                            assert!(value.size() > ty.size(), "{} must cast from bigger \
                                    integer to smaller one.", cast);
                        } else {
                            assert!(value.size() < ty.size(), "{} must cast from smaller \
                                    integer to bigger one.", cast);
                        }
                    }
                    Cast::Bitcast => {
                        assert!(value.size() == ty.size(), "{} must cast between values \
                                with the same size.", cast);

                        assert!(value != Type::U1 && *ty != Type::U1, "Cannot bitcast U1s.");
                    }
                }
            }
            Instruction::Select { dst, cond, on_true, on_false } => {
                let dst       = get_type!(*dst);
                let cond      = get_type!(*cond);
                let on_true   = get_type!(*on_true);
                let on_false  = get_type!(*on_false);

                assert!(cond == Type::U1, "Select condition input must be U1.");
                assert!(on_true == on_false && dst == on_true, "Select values and destination \
                        must have the same type.");
            }
            Instruction::Nop => {
            }
            Instruction::Alias { dst, value } => {
                assert!(get_type!(*dst) == get_type!(*value), "Alias can only alias values \
                        of the same type.");
            }
        }
    }

    pub(super) fn build_type_info(&mut self) {
        let mut cx = TypeContext {
            type_info: Map::default(),
            creators:  self.value_creators(),
        };

        for (index, value) in self.argument_values.iter().enumerate() {
            assert!(cx.type_info.insert(*value, self.prototype.arguments[index]).is_none(),
                    "Function arguments defined multiple times.");
        }

        for label in self.reachable_labels() {
            let body = &self.blocks[&label];

            for inst in body {
                if let Some(value) = inst.created_value() {
                    let _ = self.infer_value_type(value, &mut cx);
                }

                for value in inst.read_values() {
                    let _ = self.infer_value_type(value, &mut cx);
                }

                self.typecheck(inst, &mut cx);
            }
        }

        self.type_info = Some(cx.type_info);
    }
}
