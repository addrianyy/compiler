use crate::parser;
use crate::ir;
use crate::parser::{Body, Stmt, TypedExpr, Expr, Ty, UnaryOp, BinaryOp};
use std::collections::BTreeMap;

/*
pub struct Compiler {
    ir:     ir::Module,
}

struct Cx {
    vars:  BTreeMap<String, Ty>,
    funcs: BTreeMap<String, (Ty, Vec<Ty>)>,
}

/*
#[derive(Clone)]
struct Var {
    value:  ir::Value,
    rvalue: bool,
    ty:     Ty,
}
*/

type Var = GenExpr;

#[derive(Clone)]
struct GenExpr {
    value:  ir::Value,
    rvalue: bool,
    ty:     Ty,
}


fn ty_to_irtype_internal(ty: &Ty, ptrlevel: usize) -> ir::Type {
    match ty {
        Ty::I8  | Ty::U8  => ir::Type::U8.with_indirection(ptrlevel), 
        Ty::I16 | Ty::U16 => ir::Type::U16.with_indirection(ptrlevel),
        Ty::I32 | Ty::U32 => ir::Type::U32.with_indirection(ptrlevel),
        Ty::I64 | Ty::U64 => ir::Type::U64.with_indirection(ptrlevel),
        Ty::Ptr(p)        => ty_to_irtype_internal(&p, ptrlevel + 1),
        Ty::Void => panic!(),
    }
}

fn ty_to_irtype(ty: &Ty) -> ir::Type {
    ty_to_irtype_internal(ty, 0)
}

struct CodegenContext {
    vars: BTreeMap<String, Var>,
}

fn constprop_expr(expr: &Expr) -> Option<u64> {
    match expr {
        Expr::Number { value, .. } => Some(*value),
        _ => None,
    }
}

impl Compiler {
    fn get_type(cx: &CodegenContext, expr: &Expr) -> Ty {
        match expr {
            Expr::Variable(name) => {
                cx.vars[name].ty.clone()
            }
            Expr::Unary { op, value } => {
                let ty = Self::get_type(cx, &value.expr);

                match op {
                    UnaryOp::Ref   => Ty::Ptr(Box::new(ty)),
                    UnaryOp::Deref => ty.strip_pointer().unwrap(),
                    _ => {
                        assert!(ty.is_arithmetic_type());
                        ty

                    }
                }
            }
            Expr::Binary { left, op, right } => {
                let left  = Self::get_type(cx, &left.expr);
                let right = Self::get_type(cx, &right.expr);

                match op {
                    BinaryOp::Equal | BinaryOp::NotEqual | BinaryOp::Gt |
                    BinaryOp::Lt    | BinaryOp::Gte      | BinaryOp::Lte => {
                        assert!(left == right && left != Ty::Void);

                        Ty::U8
                    }
                    BinaryOp::Add | BinaryOp::Sub => {
                        assert!(left.is_arithmetic_type() || right.is_arithmetic_type());

                        if left != right {
                            return match (left.is_nonvoid_ptr(), right.is_nonvoid_ptr()) {
                                (true, false) => {
                                    left
                                }
                                (false, true) => {
                                    right
                                }
                                _ => panic!(),
                            };
                        }

                        left
                    }
                    _ => {
                        assert!(left == right && left.is_arithmetic_type());

                        left
                    }
                }
            }
            Expr::Call { target, args } => {
                /*
                let func = &cx.funcs[target];

                assert!(args.len() == func.1.len());

                for index in 0..args.len() {
                    assert!(Self::get_type(cx, &args[index].expr) == func.1[index]);
                }

                func.0.clone()
                */

                panic!()
            }
            Expr::Array { array, index } => {
                let array = Self::get_type(cx, &array.expr);
                let index = Self::get_type(cx, &index.expr);

                assert!(index.is_arithmetic_type());
                assert!(array.is_nonvoid_ptr());

                array.strip_pointer().unwrap()
            }
            Expr::Cast { value, ty } => {
                ty.clone()
            }
            Expr::Number { value, ty } => {
                ty.as_ref().unwrap().clone()
            }
            _ => panic!()
        }
    }

    /*
    fn handle_function(body: &mut Body, cx: &mut Cx, return_ty: &Ty) {
        let mut added = Vec::new();

        for stmt in body {
            match stmt {
                Stmt::Assign { variable, value } => {
                    assert!(Self::get_type(cx, &variable.expr) == 
                            Self::get_type(cx, &value.expr));
                }
                Stmt::While { condition, body } => {
                    assert!(!Self::get_type(cx, &condition.expr).is_void());
                    Self::handle_function(body, cx, return_ty);
                }
                Stmt::If { arms, default } => {
                    for (condition, body) in arms {
                        assert!(!Self::get_type(cx, &condition.expr).is_void());
                        Self::handle_function(body, cx, return_ty);
                    }

                    if let Some(default) = default.as_mut() {
                        Self::handle_function(default, cx, return_ty);
                    }
                }
                Stmt::Expr(expr) => {
                    let _ = Self::get_type(cx, &expr.expr);
                }
                Stmt::Return(value) => {
                    if let Some(value) = value.as_mut() {
                        assert!(&Self::get_type(cx, &value.expr) == return_ty);
                    }
                }
                Stmt::Declare { ty, decl_ty, name, value, array } => {
                    added.push(name.clone());

                    assert!(cx.vars.insert(name.clone(), ty.clone()).is_none());
                    assert!(array.is_none());
                    if let Some(value) = value {
                        assert!(&Self::get_type(cx, &value.expr) == ty);
                    }
                }
            }
        }

        for added in added {
            cx.vars.remove(&added);
        }
    }
    */

    fn codegen_expr(&mut self, expr: &Expr, cx: &mut CodegenContext) -> GenExpr {
        macro_rules! extract {
            ($e: expr) => {
                if $e.rvalue {
                    self.ir.load($e.value)
                } else {
                    $e.value
                }
            }
        }

        match expr {
            Expr::Variable(name) => {
                cx.vars[name].clone()
            }
            Expr::Unary { op, value } => {
                let value = self.codegen_expr(&value.expr, cx);

                match op {
                    UnaryOp::Ref => {
                        assert!(value.rvalue, "Tried to get address of non-rvalue");

                        GenExpr {
                            value:  value.value,
                            ty:     Ty::Ptr(Box::new(value.ty)),
                            rvalue: false,
                        }
                    }
                    UnaryOp::Deref => {
                        let new_value = extract!(value);

                        GenExpr {
                            value:  new_value,
                            rvalue: true,
                            ty:     value.ty.strip_pointer().unwrap(),
                        }
                    }
                    _ => {
                        assert!(value.ty.is_arithmetic_type());

                        let op = match op {
                            UnaryOp::Neg => ir::UnaryOp::Neg,
                            UnaryOp::Not => ir::UnaryOp::Not,
                            _            => panic!(),
                        };

                        let new_value = extract!(value);
                        let new_value = self.ir.arithmetic_unary(op, new_value);

                        GenExpr {
                            value:  new_value,
                            rvalue: false,
                            ty:     value.ty,
                        }
                    }
                }
            }
            Expr::Binary { left, op, right } => {
                let left  = self.codegen_expr(&left.expr, cx);
                let right = self.codegen_expr(&right.expr, cx);

                match op {
                    BinaryOp::Equal | BinaryOp::NotEqual | BinaryOp::Gt |
                    BinaryOp::Lt    | BinaryOp::Gte      | BinaryOp::Lte => {
                        panic!()
                    }
                    BinaryOp::Add | BinaryOp::Sub => {
                        panic!()
                    }
                    _ => {
                        assert!(left.ty == right.ty && left.ty.is_arithmetic_type());

                        let a = extract!(left);
                        let b = extract!(right);

                        let op = match op {
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
                            _             => panic!(),
                        };

                        let res = self.ir.arithmetic_binary(a, op, b);

                        GenExpr {
                            value:  res,
                            rvalue: false,
                            ty:     left.ty,
                        }
                    }
                }
            }
            Expr::Number { value, ty } => {
                let ty    = ty.clone().unwrap_or(Ty::I32);
                let value = self.ir.iconst(*value, ty_to_irtype(&ty));

                GenExpr {
                    value,
                    rvalue: false,
                    ty,
                }
            }
            Expr::Array { array, index } => {
                let array = self.codegen_expr(&array.expr, cx);
                let index = self.codegen_expr(&index.expr, cx);

                assert!(index.ty.is_arithmetic_type());
                assert!(array.ty.is_nonvoid_ptr());

                let array_v = extract!(array);
                let index_v = extract!(index);

                let value = self.ir.get_element_ptr(array_v, index_v);

                GenExpr {
                    value,
                    rvalue: true,
                    ty:     array.ty.strip_pointer().unwrap(),
                }
            }
            _ => panic!(),
        }
    }

    fn codegen_body(&mut self, body: &Body, cx: &mut CodegenContext) {
        macro_rules! extract {
            ($e: expr) => {
                if $e.rvalue {
                    self.ir.load($e.value)
                } else {
                    $e.value
                }
            }
        }

        for stmt in body {
            match stmt {
                Stmt::Expr(expr) => {
                    self.codegen_expr(&expr.expr, cx);
                }
                Stmt::Assign { variable, value } => {
                    let value    = self.codegen_expr(&value.expr, cx);
                    let value    = extract!(value);
                    let variable = self.codegen_expr(&variable.expr, cx);

                    assert!(variable.rvalue);

                    self.ir.store(variable.value, value);
                }
                Stmt::Declare { ty, decl_ty, name, value, array } => {
                    let size = if let Some(array) = array {
                        constprop_expr(&array.expr).unwrap()
                    } else {
                        1
                    };

                    let mut var = self.ir.stack_alloc(ty_to_irtype(decl_ty), size as usize);

                    let rvalue = size == 1;

                    if let Some(value) = value {
                        let value = self.codegen_expr(&value.expr, cx);
                        let value = extract!(value);

                        self.ir.store(var, value);
                    }

                    cx.vars.insert(name.to_string(), Var {
                        value: var,
                        rvalue,
                        ty:    ty.clone(),
                    });
                }
                Stmt::Return(value) => {
                    let res = value.as_ref().map(|v| {
                        let v = self.codegen_expr(&v.expr, cx);
                        extract!(v)
                    });

                    self.ir.ret(res);
                }
                _ => panic!(),
            }
        }
    }

    pub fn new(mut module: parser::ParsedModule) -> Self {
        /*
        let mut cx = Cx {
            vars:  BTreeMap::new(),
            funcs: BTreeMap::new(),
        };

        for func in &module.functions {
            let mut types = Vec::new();

            for (name, ty) in &func.proto.args {
                types.push(ty.clone());
            }

            assert!(cx.funcs.insert(func.proto.name.clone(), (func.proto.return_ty.clone(), types))
                    .is_none());
            
        }

        for func in &mut module.functions {
            cx.vars.clear();

            for (name, ty) in &func.proto.args {
                assert!(cx.vars.insert(name.clone(), ty.clone()).is_none());
            }

            Self::handle_function(&mut func.body, &mut cx, &func.proto.return_ty);
        }
        */

        let mut compiler = Compiler {
            ir:    ir::Module::new(),
        };

        let mut cx = CodegenContext {
            vars: BTreeMap::new(),
        };

        let ir_func = compiler.ir.create_function("test", None, Vec::new());
        compiler.ir.switch_function(ir_func);

        for func in &mut module.functions {
            compiler.codegen_body(&func.body, &mut cx);
            compiler.ir.finalize();
            compiler.ir.dump_function_text(ir_func, &mut std::io::stdout());

            panic!();
        }

        panic!();
    }
}
*/

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

fn to_ir_type(ty: &Ty) -> ir::Type {
    to_ir_type_internal(ty, 0)
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

struct Variables {
    map: BTreeMap<String, CodegenValue>,
}

impl Variables {
    fn get(&self, name: &str) -> CodegenValue {
        self.map[name].clone()
    }
}

pub struct Compiler {
    ir:        ir::Module,
    variables: Variables,
}

impl Compiler {
    fn codegen_expression(&mut self, expression: &Expr) -> CodegenValue {
        match expression {
            Expr::Variable(variable) => {
                self.variables.get(variable)
            }
            Expr::Unary { op, value } => {
                let value = self.codegen_expression(&value);

                match op {
                    UnaryOp::Ref => {
                        assert!(value.is_lvalue(), "Cannot get address of rvalue.");

                        CodegenValue::rvalue(value.ty.ptr(), value.value)
                    }
                    UnaryOp::Deref => {
                        let new_ty = value.ty.strip_pointer().expect("Cannot deref non-pointer.");

                        // If value is lvalue we want to deref it and keep it lvalue.
                        // If value is rvalue we just want to make it lvalue.
                        let result = value.extract(&mut self.ir);

                        CodegenValue::lvalue(new_ty, result)
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

                        CodegenValue::rvalue(value.ty, result)
                    }
                }
            }
            Expr::Binary { left, op, right } => {
                let left  = self.codegen_expression(&left);
                let right = self.codegen_expression(&right);

                match op {
                    BinaryOp::Equal | BinaryOp::NotEqual | BinaryOp::Gt |
                    BinaryOp::Lt    | BinaryOp::Gte      | BinaryOp::Lte => {
                        assert!(left.ty == right.ty && left.ty != Ty::Void, "Cannot compare \
                                two values with different types (or void types.");

                        let mut left_value  = left.extract(&mut self.ir);
                        let mut right_value = right.extract(&mut self.ir);

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

                        CodegenValue::rvalue(Ty::U8, result)
                    }
                    _ => {
                        panic!()
                    }
                }
            }
            Expr::Array { array, index } => {
                let array = self.codegen_expression(&array);
                let index = self.codegen_expression(&index);

                assert!(array.ty.is_nonvoid_ptr(),     "Array must be non-void pointer.");
                assert!(index.ty.is_arithmetic_type(), "Index must be arithmetic type.");

                let array_value = array.extract(&mut self.ir);
                let index_value = index.extract(&mut self.ir);

                let new_ty = array.ty.strip_pointer().expect("Cannot deref non-pointer.");
                let result = self.ir.get_element_ptr(array_value, index_value);

                CodegenValue::lvalue(new_ty, result)
            }
            Expr::Number { value, ty } => {
                let ty    = ty.clone().unwrap_or(Ty::I32);
                let value = self.ir.iconst(*value, to_ir_type(&ty));

                CodegenValue::rvalue(ty, value)
            }
            _ => panic!(),
        }
    }

    pub fn new(module: parser::ParsedModule) -> Self {
        panic!()
    }
}
