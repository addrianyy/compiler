use crate::parser;
use crate::parser::{Body, Stmt, TypedExpr, Expr, Ty, UnaryOp, BinaryOp};
use std::collections::BTreeMap;

pub struct Compiler {
    module: parser::ParsedModule,
}

struct Cx {
    vars:  BTreeMap<String, Ty>,
    funcs: BTreeMap<String, (Ty, Vec<Ty>)>,
}

impl Compiler {
    fn get_type(cx: &Cx, expr: &Expr) -> Ty {
        match expr {
            Expr::Variable(name) => {
                cx.vars[name].clone()
            }
            Expr::Unary { op, value } => {
                let ty = Self::get_type(cx, &value.expr).clone();

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
                let func = &cx.funcs[target];

                assert!(args.len() == func.1.len());

                for index in 0..args.len() {
                    assert!(Self::get_type(cx, &args[index].expr) == func.1[index]);
                }

                func.0.clone()
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
        }
    }

    fn handle_stmt(cx: &mut Cx, stmt: &mut Stmt) {
    }

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

    pub fn new(mut module: parser::ParsedModule) -> Self {
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

        panic!();
    }
}
