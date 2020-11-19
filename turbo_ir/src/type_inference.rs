use super::{FunctionData, Value, Location, Map, Type, TypeInfo, Instruction, Cast};

struct TypeContext {
    creators:  Map<Value, Location>,
    type_info: TypeInfo,
}

impl TypeContext {
    fn get_type(&self, value: Value) -> Type {
        self.type_info.get(&value).copied().unwrap()
    }
}

impl FunctionData {
    fn infer_value_type(&self, value: Value, cx: &mut TypeContext) {
        time!(infer_value_type);

        let creator = cx.creators.get(&value).map(|location| {
            self.instruction(*location)
        }).expect("Value is used without being created.");

        let ty = match creator {
            Instruction::ArithmeticUnary { value, .. } => {
                cx.get_type(*value)
            }
            Instruction::ArithmeticBinary { a, b, .. } => {
                let a = cx.get_type(*a);
                let b = cx.get_type(*b);

                assert_eq!(a, b, "Binary arithmetic instruction must have operands \
                                  of the same type.");

                a
            }
            Instruction::IntCompare { a, b, .. } => {
                let a = cx.get_type(*a);
                let b = cx.get_type(*b);

                assert_eq!(a, b, "Int compare instruction must have operands \
                                  of the same type.");

                Type::U1
            }
            Instruction::Load { ptr, .. } => {
                cx.get_type(*ptr)
                    .strip_ptr()
                    .expect("Cannot load non-pointer value.")
            }
            Instruction::Call { func, .. } => {
                self.function_prototype(*func)
                    .return_type
                    .expect("Void function return value is used.")
            }
            Instruction::Select { on_true, on_false, .. } => {
                let on_true  = cx.get_type(*on_true);
                let on_false = cx.get_type(*on_false);

                assert_eq!(on_true, on_false, "Select instruction must have operands \
                                               of the same type.");

                on_true
            }
            Instruction::Phi { incoming, .. } => {
                let mut result = None;

                // It's possible that we don't know types of all incoming values.
                // We always need to know the type of at least one.
                for &(_, incoming_value) in incoming {
                    if let Some(ty) = cx.type_info.get(&incoming_value) {
                        result = Some(*ty);
                        break;
                    }
                }

                result.expect("Failed to get PHI output value.")
            }
            Instruction::StackAlloc    { ty, ..       } => ty.ptr(),
            Instruction::Const         { ty, ..       } => *ty,
            Instruction::GetElementPtr { source, ..   } => cx.get_type(*source),
            Instruction::Cast          { ty, ..       } => *ty,
            Instruction::Alias         { value, ..    } => cx.get_type(*value),
            _ => {
                panic!("Unexpected value creator: {:?}.", creator);
            }
        };

        assert!(cx.type_info.insert(value, ty).is_none(),
                "Value has type infered multiple times.");
    }

    fn typecheck(&self, instruction: &Instruction, cx: &mut TypeContext) {
        time!(typecheck);

        match instruction {
            Instruction::ArithmeticUnary { dst, value, .. } => {
                let dst   = cx.get_type(*dst);
                let value = cx.get_type(*value);

                assert_eq!(dst, value, "Unary arithmetic instruction requires all \
                           operands to be of the same type");

                assert!(dst.is_arithmetic(), "Unary arithmetic instruction can be \
                        only done on arithmetic types.");
            }
            Instruction::ArithmeticBinary { dst, a, b, .. } => {
                let dst = cx.get_type(*dst);
                let a   = cx.get_type(*a);
                let b   = cx.get_type(*b);

                assert!(dst == a && a == b, "Binary arithmetic instruction requires all \
                        operands to be of the same type");

                assert!(dst.is_arithmetic(), "Binary arithmetic instruction can be \
                        only done on arithmetic types.");
            }
            Instruction::IntCompare { dst, a, b, .. } => {
                let dst = cx.get_type(*dst);
                let a   = cx.get_type(*a);
                let b   = cx.get_type(*b);

                assert_eq!(dst, Type::U1, "Int compare instruction requires \
                           destination type to be U1.");

                assert_eq!(a, b, "Int compare instruction requires all \
                           input operands to be of the same type");
            }
            Instruction::Load { dst, ptr } => {
                let dst = cx.get_type(*dst);
                let ptr = cx.get_type(*ptr);

                let stripped = ptr.strip_ptr()
                    .expect("Load instruction can only load from pointers.");

                assert_eq!(dst, stripped, "Load instruction destination must have pointee type.");
            }
            Instruction::Store { ptr, value } => {
                let ptr   = cx.get_type(*ptr);
                let value = cx.get_type(*value);

                let stripped = ptr.strip_ptr()
                    .expect("Store instruction can only store to pointers.");

                assert_eq!(value, stripped, "Store instruction value must have pointee type.");
            }
            Instruction::Call { dst, func, args } => {
                let prototype = self.function_prototype(*func);

                if let Some(dst) = dst {
                    let return_type = prototype.return_type
                        .expect("Cannot take the return value of void function.");

                    assert_eq!(cx.get_type(*dst), return_type,
                               "Function call return value doesn't match.");
                }

                assert_eq!(args.len(), prototype.arguments.len(), "Function call with invalid \
                           argument count.");

                for (index, arg) in args.iter().enumerate() {
                    assert_eq!(cx.get_type(*arg), prototype.arguments[index],
                               "Function call with invalid arguments.");
                }
            }
            Instruction::Branch { .. } => {
            }
            Instruction::BranchCond { cond, .. } => {
                let cond = cx.get_type(*cond);

                assert_eq!(cond, Type::U1, "Conditional branch input must be U1.");
            }
            Instruction::StackAlloc { dst, ty, size } => {
                let dst = cx.get_type(*dst);

                assert!(*size > 0, "Stack alloc cannot allocate 0 sized array.");
                assert_eq!(dst.strip_ptr().expect("Stack alloc destination must be pointer."), *ty,
                           "Stack alloc destination must be pointer to input type.");
            }
            Instruction::Return { value } => {
                let value = value.map(|value| cx.get_type(value));

                assert_eq!(value, self.prototype.return_type, "Return instruction operand type \
                           must be the same function as function return type.");
            }
            Instruction::Const { dst, ty, imm, .. } => {
                let dst = cx.get_type(*dst);

                if *ty == Type::U1 {
                    assert!(*imm == 0 || *imm == 1, "Invalid U1 constant {}.", imm);
                }

                assert_eq!(dst, *ty, "Const value instruction operand types must be the same.");
            }
            Instruction::GetElementPtr { dst, source, index } => {
                let dst    = cx.get_type(*dst);
                let source = cx.get_type(*source);
                let index  = cx.get_type(*index);

                assert!(index.is_arithmetic(), "GEP index must be arithmetic.");
                assert_eq!(dst, source, "GEP destination and source must be the same type.");
                assert!(dst.is_pointer(), "GEP input type is not valid pointer.");
            }
            Instruction::Cast { dst, cast, value, ty } => {
                let dst   = cx.get_type(*dst);
                let value = cx.get_type(*value);

                assert_eq!(dst, *ty, "{} destination must be the same type as cast type.", cast);
                assert!(value != Type::U1 && *ty != Type::U1, "Cannot cast U1s.");

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
                        assert_eq!(value.size(), ty.size(), "{} must cast between values \
                                   with the same size.", cast);
                    }
                }
            }
            Instruction::Select { dst, cond, on_true, on_false } => {
                let dst       = cx.get_type(*dst);
                let cond      = cx.get_type(*cond);
                let on_true   = cx.get_type(*on_true);
                let on_false  = cx.get_type(*on_false);

                assert_eq!(cond, Type::U1, "Select condition input must be U1.");
                assert!(on_true == on_false && dst == on_true, "Select values and destination \
                        must have the same type.");
            }
            Instruction::Phi { dst, incoming } => {
                let dst = cx.get_type(*dst);

                for (_label, value) in incoming {
                    assert_eq!(cx.get_type(*value), dst, "PHI values must have the same types.");
                }
            }
            Instruction::Nop => {
            }
            Instruction::Alias { dst, value } => {
                assert_eq!(cx.get_type(*dst), cx.get_type(*value), "Alias can only alias values \
                           of the same type.");
            }
        }
    }

    pub(super) fn build_type_info(&mut self) {
        time!(build_type_info);

        let mut cx = TypeContext {
            type_info: Map::default(),
            creators:  self.value_creators(),
        };

        for (index, value) in self.argument_values.iter().enumerate() {
            assert!(cx.type_info.insert(*value, self.prototype.arguments[index]).is_none(),
                    "Function arguments defined multiple times.");
        }

        for (ty, value) in &self.undefined {
            assert!(cx.type_info.insert(*value, *ty).is_none(),
                    "Undefined values defined multiple times.");
        }

        for value in self.value_processing_order() {
            if !self.is_value_special(value) {
                self.infer_value_type(value, &mut cx);
            }
        }

        for label in self.reachable_labels() {
            for instruction in &self.blocks[&label] {
                self.typecheck(instruction, &mut cx);
            }
        }

        self.type_info = Some(cx.type_info);
    }
}
