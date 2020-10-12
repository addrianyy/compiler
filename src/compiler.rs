use std::collections::BTreeMap;
use std::cmp::Ordering;

use crate::parser;
use crate::ir;
use crate::parser::{Body, Stmt, Expr, Ty, UnaryOp, BinaryOp};

fn to_ir_type(ty: &Ty) -> ir::Type {
    fn to_ir_type_internal(ty: &Ty, indirection: usize) -> ir::Type {
        match ty {
            Ty::I8  | Ty::U8  => ir::Type::U8 .with_indirection(indirection),
            Ty::I16 | Ty::U16 => ir::Type::U16.with_indirection(indirection),
            Ty::I32 | Ty::U32 => ir::Type::U32.with_indirection(indirection),
            Ty::I64 | Ty::U64 => ir::Type::U64.with_indirection(indirection),
            Ty::Ptr(inside)   => to_ir_type_internal(&inside, indirection + 1),
            Ty::Void          => panic!("IR doesn't support void type."),
        }
    }

    to_ir_type_internal(ty, 0)
}

fn constant_expression(expression: &Expr) -> Option<u64> {
    // TODO: handle more expressions.

    match expression {
        Expr::Number { value, .. } => {
            Some(*value)
        }
        _ => None,
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum ValueType {
    Rvalue,
    Lvalue,
}

#[derive(Clone)]
struct CodegenValue {
    value:      ir::Value,
    value_type: ValueType,
    ty:         Ty,
}

impl CodegenValue {
    fn lvalue(ty: Ty, value: ir::Value) -> Self {
        Self {
            value,
            ty,
            value_type: ValueType::Lvalue,
        }
    }

    fn rvalue(ty: Ty, value: ir::Value) -> Self {
        Self {
            value,
            ty,
            value_type: ValueType::Rvalue,
        }
    }

    fn extract(&self, ir: &mut ir::Module) -> ir::Value {
        match self.value_type {
            ValueType::Lvalue => ir.load(self.value),
            ValueType::Rvalue => self.value,
        }
    }

    fn ir_type(&self) -> ir::Type {
        to_ir_type(&self.ty)
    }

    fn is_lvalue(&self) -> bool {
        self.value_type == ValueType::Lvalue
    }

    fn is_rvalue(&self) -> bool {
        self.value_type == ValueType::Rvalue
    }
}

#[derive(Clone)]
struct CodegenFunction {
    function:  ir::Function,
    return_ty: Ty,
    args:      Vec<Ty>,
}

struct Variables {
    map:   BTreeMap<String, CodegenValue>,
    scope: Vec<Vec<String>>,
}

impl Variables {
    fn new() -> Self {
        Self {
            map:   BTreeMap::new(),
            scope: Vec::new(),
        }
    }

    fn get(&self, name: &str) -> CodegenValue {
        self.map.get(name)
            .unwrap_or_else(|| panic!("Unknown variable {} referenced."))
            .clone()
    }
    
    fn clear(&mut self) {
        self.map.clear()
    }

    fn insert(&mut self, name: &str, value: CodegenValue) {
        let last = self.scope.len() - 1;
        self.scope[last].push(name.to_owned());

        assert!(self.map.insert(name.to_owned(), value).is_none(), 
                "Mutliple variables with the same name.");
    }

    fn enter_scope(&mut self) {
        self.scope.push(Vec::new());
    }

    fn exit_scope(&mut self) {
        for name in self.scope.pop().unwrap() {
            self.map.remove(&name);
        }
    }
}

struct Functions {
    map: BTreeMap<String, CodegenFunction>,
}

impl Functions {
    fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    fn get(&self, name: &str) -> &CodegenFunction {
        &self.map[name]
    }
}

pub struct Compiler {
    ir:        ir::Module,
    variables: Variables,
    functions: Functions,
}

impl Compiler {
    fn int_cast(&mut self, value: ir::Value, orig_ty: &Ty, target_ty: &Ty) -> ir::Value {
        assert!(!orig_ty.is_pointer() && !target_ty.is_pointer(), "Cannot intcast pointers.");

        let cast = match orig_ty.size().cmp(&target_ty.size()) {
            Ordering::Greater => {
                Some(ir::Cast::Truncate)
            }
            Ordering::Less => {
                match orig_ty.is_signed() {
                    true  => Some(ir::Cast::SignExtend),
                    false => Some(ir::Cast::ZeroExtend),
                }
            }
            Ordering::Equal => {
                None
            }
        };

        match cast {
            Some(cast) => self.ir.cast(value, to_ir_type(target_ty), cast),
            None       => value,
        }
    }

    fn codegen_nonvoid_expression(&mut self, expression: &Expr) -> CodegenValue {
        self.codegen_expression(expression)
            .expect("Expected non-void expression, got void one.")
    }

    fn codegen_expression(&mut self, expression: &Expr) -> Option<CodegenValue> {
        match expression {
            Expr::Variable(variable) => {
                Some(self.variables.get(variable))
            }
            Expr::Unary { op, value } => {
                let value = self.codegen_nonvoid_expression(&value);

                match op {
                    UnaryOp::Ref => {
                        assert!(value.is_lvalue(), "Cannot get address of rvalue.");

                        Some(CodegenValue::rvalue(value.ty.ptr(), value.value))
                    }
                    UnaryOp::Deref => {
                        let new_ty = value.ty.strip_pointer().expect("Cannot deref non-pointer.");

                        // If value is lvalue we want to deref it and keep it lvalue.
                        // If value is rvalue we just want to make it lvalue.
                        let result = value.extract(&mut self.ir);

                        Some(CodegenValue::lvalue(new_ty, result))
                    }
                    _ => {
                        assert!(value.ty.is_arithmetic_type(), "Unary operator can only be \
                                applied on arithmetic types.");

                        let op = match op {
                            UnaryOp::Neg => ir::UnaryOp::Neg,
                            UnaryOp::Not => ir::UnaryOp::Not,
                            _            => unreachable!(),
                        };

                        let result = value.extract(&mut self.ir);
                        let result = self.ir.arithmetic_unary(op, result);

                        Some(CodegenValue::rvalue(value.ty, result))
                    }
                }
            }
            Expr::Binary { left, op, right } => {
                let left  = self.codegen_nonvoid_expression(&left);
                let right = self.codegen_nonvoid_expression(&right);

                let left_value  = left.extract(&mut self.ir);
                let right_value = right.extract(&mut self.ir);

                let pointers = left.ty.is_pointer() || right.ty.is_pointer();

                match op {
                    BinaryOp::Equal | BinaryOp::NotEqual | BinaryOp::Gt |
                    BinaryOp::Lt    | BinaryOp::Gte      | BinaryOp::Lte => {
                        assert!(left.ty == right.ty && left.ty != Ty::Void, "Cannot compare \
                                two values with different types (or void types.");

                        let mut left_value  = left_value;
                        let mut right_value = right_value;

                        if left.ty.is_pointer() {
                            // IR doesn't allow comparing pointers. Convert them to integers.

                            left_value = self.ir.cast(left_value, ir::Type::U64,
                                                      ir::Cast::Bitcast);
                            right_value = self.ir.cast(right_value, ir::Type::U64,
                                                       ir::Cast::Bitcast);
                        }

                        let op_change = match op {
                            BinaryOp::Lt  => Some(BinaryOp::Gt),
                            BinaryOp::Lte => Some(BinaryOp::Gte),
                            _             => None,
                        };

                        let mut op = *op;

                        if let Some(new_op) = op_change {
                            op = new_op;

                            std::mem::swap(&mut left_value, &mut right_value);
                        }

                        let predicate = match (op, left.ty.is_signed()) {
                            (BinaryOp::Equal,    _    ) => ir::IntPredicate::Equal,
                            (BinaryOp::NotEqual, _    ) => ir::IntPredicate::NotEqual,
                            (BinaryOp::Gt,       true ) => ir::IntPredicate::GtS,
                            (BinaryOp::Gte,      true ) => ir::IntPredicate::GteS,
                            (BinaryOp::Gt,       false) => ir::IntPredicate::GtU,
                            (BinaryOp::Gte,      false) => ir::IntPredicate::GteU,
                            _                           => unreachable!(),
                        };

                        let result = self.ir.int_compare(left_value, predicate, right_value);
                        let zero   = self.ir.iconst(0u8, ir::Type::U8);
                        let one    = self.ir.iconst(1u8, ir::Type::U8);
                        let result = self.ir.select(result, one, zero);

                        Some(CodegenValue::rvalue(Ty::U8, result))
                    }
                    BinaryOp::Add | BinaryOp::Sub if pointers => {
                        // TODO: Special case: add/sub on pointers
                        panic!()
                    }
                    _ => {
                        assert!(left.ty == right.ty && left.ty.is_arithmetic_type(), "Cannot \
                                apply binary operator to values of different types or \
                                non-arithmetic values.");

                        let op = match op {
                            BinaryOp::Add => ir::BinaryOp::Add,
                            BinaryOp::Sub => ir::BinaryOp::Sub,
                            BinaryOp::Mul => ir::BinaryOp::Mul,
                            BinaryOp::Mod => ir::BinaryOp::Mod,
                            BinaryOp::Div => ir::BinaryOp::Div,
                            BinaryOp::Shr => {
                                if left.ty.is_signed() {
                                    ir::BinaryOp::Sar
                                } else {
                                    ir::BinaryOp::Shr
                                }
                            }
                            BinaryOp::Shl => ir::BinaryOp::Shl,
                            BinaryOp::And => ir::BinaryOp::And,
                            BinaryOp::Or  => ir::BinaryOp::Or,
                            BinaryOp::Xor => ir::BinaryOp::Xor,
                            _             => unreachable!(),
                        };

                        let result = self.ir.arithmetic_binary(left_value, op, right_value);

                        Some(CodegenValue::rvalue(left.ty, result))
                    }
                }
            }
            Expr::Array { array, index } => {
                let array = self.codegen_nonvoid_expression(&array);
                let index = self.codegen_nonvoid_expression(&index);

                assert!(array.ty.is_nonvoid_ptr(),     "Array must be non-void pointer.");
                assert!(index.ty.is_arithmetic_type(), "Index must be arithmetic type.");

                let array_value = array.extract(&mut self.ir);
                let index_value = index.extract(&mut self.ir);

                let new_ty = array.ty.strip_pointer().expect("Cannot deref non-pointer.");
                let result = self.ir.get_element_ptr(array_value, index_value);

                Some(CodegenValue::lvalue(new_ty, result))
            }
            Expr::Number { value, ty } => {
                let ty    = ty.clone().unwrap_or(Ty::I32);
                let value = self.ir.iconst(*value, to_ir_type(&ty));

                Some(CodegenValue::rvalue(ty, value))
            }
            Expr::Cast { value, ty } => {
                let value = self.codegen_nonvoid_expression(&value);

                let orig_ty   = value.ty.clone();
                let target_ty = ty.clone();
                let extracted = value.extract(&mut self.ir);
                
                let integer   = !orig_ty.is_pointer() && !target_ty.is_pointer();
                let same_size = orig_ty.size() == target_ty.size();

                let target_ty_ir = to_ir_type(&target_ty);

                let result = if integer {
                    self.int_cast(extracted, &orig_ty, &target_ty)
                } else if same_size {
                    self.ir.cast(extracted, target_ty_ir, ir::Cast::Bitcast)
                } else {
                    match (orig_ty.is_pointer(), target_ty.is_pointer()) {
                        (true, false) => {
                            let x = self.ir.cast(extracted, ir::Type::U64, ir::Cast::Bitcast);
                            self.int_cast(x, &Ty::U64, &target_ty)
                        }
                        (false, true) => {
                            let x = self.int_cast(extracted, &orig_ty, &Ty::U64);
                            self.ir.cast(x, target_ty_ir, ir::Cast::Bitcast)
                        }
                        _ => unreachable!(),
                    }
                };

                Some(CodegenValue::rvalue(target_ty, result))
            }
            Expr::Call { target, args } => {
                let function = self.functions.get(target).clone();

                assert!(function.args.len() == args.len(),
                        "Number of arguments mismatch in call.");

                let mut generated_args = Vec::new();

                for index in 0..args.len() {
                    let value = self.codegen_nonvoid_expression(&args[index]);

                    assert!(value.ty == function.args[index], "Invalid type of parameter \
                            passed to function {}.", target);

                    generated_args.push(value.extract(&mut self.ir));
                }

                self.ir.call(function.function, generated_args).map(|value| {
                    CodegenValue::rvalue(function.return_ty.clone(), value)
                })
            }
        }
    }

    fn codegen_body(&mut self, body: &Body, return_ty: &Ty) {
        self.variables.enter_scope();

        for statement in body {
            match statement {
                Stmt::Expr(expression) => {
                    self.codegen_expression(expression);
                }
                Stmt::Declare { ty, decl_ty, name, value, array } => {
                    let (size, array) = match array {
                        Some(array) => {
                            (constant_expression(array)
                                .expect("Array size must be constant.") as usize, true)
                        }
                        None => (1, false),
                    };

                    let variable = self.ir.stack_alloc(to_ir_type(decl_ty), size);

                    if let Some(value) = value {
                        let value = self.codegen_nonvoid_expression(value);

                        assert!(!array, "Arrays cannot have initializers.");
                        assert!(value.ty == *ty, "Initializer doesn't have the same \
                                type as variable.");

                        let extracted = value.extract(&mut self.ir);

                        self.ir.store(variable, extracted);
                    }

                    let value = match array {
                        true  => CodegenValue::rvalue(ty.clone(), variable),
                        false => CodegenValue::lvalue(ty.clone(), variable),
                    };

                    self.variables.insert(name, value);
                }
                Stmt::Assign { variable, value } => {
                    let variable = self.codegen_nonvoid_expression(variable);
                    let value    = self.codegen_nonvoid_expression(value);

                    assert!(variable.ty == value.ty, "Cannot assign value of different type.");
                    assert!(variable.is_lvalue(), "Cannot assign to rvalue.");

                    let extracted = value.extract(&mut self.ir);

                    self.ir.store(variable.value, extracted);
                }
                Stmt::Return(value) => {
                    match value {
                        Some(value) => {
                            let value     = self.codegen_nonvoid_expression(value);
                            let extracted = value.extract(&mut self.ir);

                            assert!(return_ty == &value.ty, "Function return type differs.");

                            self.ir.ret(Some(extracted));
                        }
                        None => {
                            assert!(return_ty == &Ty::Void, "Cannot return void from \
                                    non-void function.");

                            self.ir.ret(None);
                        }
                    }
                }
                _ => panic!(),
            }
        }

        self.variables.exit_scope();
    }

    pub fn new(module: parser::ParsedModule) -> Self {
        let mut compiler = Compiler {
            ir:        ir::Module::new(),
            variables: Variables::new(),
            functions: Functions::new(),
        };

        for function in &module.functions {
            let mut args    = Vec::new();
            let mut args_ir = Vec::new();

            for (_, ty) in &function.prototype.args {
                args.push(ty.clone());
                args_ir.push(to_ir_type(ty));
            }

            let return_ty = match &function.prototype.return_ty {
                Ty::Void => None,
                x        => Some(to_ir_type(&x)),
            };

            let name    = &function.prototype.name;
            let ir_func = compiler.ir.create_function(name, return_ty, args_ir);

            let codegen_func = CodegenFunction {
                return_ty: function.prototype.return_ty.clone(),
                function:  ir_func,
                args,
            };

            assert!(compiler.functions.map.insert(name.clone(), codegen_func).is_none(),
                    "Multiple functions with the same name.");
        }

        for function in &module.functions {
            compiler.variables.clear();

            let return_ty = &function.prototype.return_ty;
            let ir_func   = compiler.functions.get(&function.prototype.name);

            compiler.ir.switch_function(ir_func.function);

            compiler.variables.enter_scope();

            for (index, (arg_name, arg_ty)) in function.prototype.args.iter().enumerate() {
                // Move arguments from registers to stack to make sure that they are lvalues.

                let storage = compiler.ir.stack_alloc(to_ir_type(arg_ty), 1);
                let value   = compiler.ir.argument(index);

                compiler.ir.store(storage, value);

                let variable = CodegenValue::lvalue(arg_ty.clone(), storage);

                compiler.variables.insert(arg_name, variable);
            }
            
            compiler.codegen_body(&function.body, return_ty);

            compiler.variables.exit_scope();
        }

        compiler.ir.finalize();

        for function in compiler.functions.map.values() {
            compiler.ir.dump_function_text(function.function,
                                           &mut std::io::stdout()).unwrap();
        }

        panic!()
    }
}
