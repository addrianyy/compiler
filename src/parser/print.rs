use std::io::{self, Write};

use super::{Stmt, Expr, BodyRef, Function, FunctionPrototype, ParsedModule};

const INDENT_STRING:  &str = "    ";
const SUBITEM_INDENT: &str = "  ";

fn print_body<W: Write>(body: BodyRef, w: &mut W, indent: usize) -> io::Result<()> {
    for stmt in body {
        stmt.print(w, indent)?;
    }

    Ok(())
}

impl Expr {
    pub fn print<W: Write>(&self, w: &mut W, indent: usize) -> io::Result<()> {
        let mut j = String::new();

        for _ in 0..indent {
            j.push_str(INDENT_STRING);
        }

        let i = j.clone() + SUBITEM_INDENT;

        match self {
            Expr::Variable(name) => {
                writeln!(w, "{}{}", i, name)?;
            }
            Expr::Cast { value, ty } => {
                writeln!(w, "{}CastExpr to {}", i, ty)?;

                writeln!(w, "{}Value:", i)?;
                value.print(w, indent + 1)?;
            }
            Expr::Unary { op, value } => {
                writeln!(w, "{}UnaryExpr", j)?;

                writeln!(w, "{}Op: {:?}", i, op)?;

                writeln!(w, "{}Value:", i)?;
                value.print(w, indent + 1)?;
            }
            Expr::Binary { left, op, right } => {
                writeln!(w, "{}BinaryExpr", j)?;

                writeln!(w, "{}Op: {:?}", i, op)?;

                writeln!(w, "{}Left:", i)?;
                left.print(w, indent + 1)?;

                writeln!(w, "{}Right:", i)?;
                right.print(w, indent + 1)?;
            }
            Expr::Number { value, .. } => {
                writeln!(w, "{}{}", i, value)?;
            }
            Expr::Array { array, index } => {
                writeln!(w, "{}ArrayExpr", j)?;

                writeln!(w, "{}Array:", i)?;
                array.print(w, indent + 1)?;

                writeln!(w, "{}Index:", i)?;
                index.print(w, indent + 1)?;
            }
            Expr::Call { target, args } => {
                writeln!(w, "{}CallExpr", j)?;

                writeln!(w, "{}Target: {}", i, target)?;

                writeln!(w, "{}Args:", i)?;
                for arg in args {
                    arg.print(w, indent + 1)?;
                }
            }
        }

        Ok(())
    }
}

impl Stmt {
    pub fn print<W: Write>(&self, w: &mut W, indent: usize) -> io::Result<()> {
        let mut j = String::new();

        for _ in 0..indent {
            j.push_str(INDENT_STRING);
        }

        let i = j.clone() + SUBITEM_INDENT;

        match self {
            Stmt::Assign { variable, value } => {
                writeln!(w, "{}AssignStmt", j)?;

                writeln!(w, "{}Target:", i)?;
                variable.print(w, indent + 1)?;

                writeln!(w, "{}Value:", i)?;
                value.print(w, indent + 1)?;
            }
            Stmt::Declare { ty, decl_ty, name, value, array } => {
                writeln!(w, "{}DeclareStmt", j)?;

                writeln!(w, "{}Name:   {}", i, name)?;
                writeln!(w, "{}DeclTy: {}", i, decl_ty)?;
                writeln!(w, "{}Ty:     {}", i, ty)?;

                if let Some(value) = value {
                    writeln!(w, "{}Value:", i)?;
                    value.print(w, indent + 1)?;
                }

                if let Some(array) = array {
                    writeln!(w, "{}ArraySize:", i)?;
                    array.print(w, indent + 1)?;
                }
            }
            Stmt::While { condition, body } => {
                writeln!(w, "{}WhileStmt", j)?;

                writeln!(w, "{}Condition:", i)?;
                condition.print(w, indent + 1)?;

                writeln!(w, "{}Body:", i)?;
                print_body(body, w, indent + 1)?;
            }
            Stmt::For { init, condition, step, body } => {
                writeln!(w, "{}ForStmt", j)?;

                if let Some(init) = init {
                    writeln!(w, "{}Init:", i)?;
                    init.print(w, indent + 1)?;
                }

                if let Some(condition) = condition {
                    writeln!(w, "{}Condition:", i)?;
                    condition.print(w, indent + 1)?;
                }

                if let Some(step) = step {
                    writeln!(w, "{}Step:", i)?;
                    step.print(w, indent + 1)?;
                }

                writeln!(w, "{}Body:", i)?;
                print_body(body, w, indent + 1)?;
            }
            Stmt::If { arms, default } => {
                writeln!(w, "{}IfStmt", j)?;

                for (index, arm) in arms.iter().enumerate() {
                    writeln!(w, "{}Arm {} condition:", i, index)?;
                    arm.0.print(w, indent + 1)?;

                    writeln!(w, "{}Arm {} body:", i, index)?;
                    print_body(&arm.1, w, indent + 1)?;
                }

                if let Some(default) = default {
                    writeln!(w, "{}Default arm body:", i)?;
                    print_body(default, w, indent + 1)?;
                }
            }
            Stmt::Return(value) => {
                writeln!(w, "{}ReturnStmt", j)?;

                if let Some(value) = value {
                    writeln!(w, "{}Value:", i)?;
                    value.print(w, indent + 1)?;
                } else {
                    writeln!(w, "{}Value: none", i)?;
                }
            }
            Stmt::Expr(value) => {
                value.print(w, indent)?;
            }
            Stmt::Break    => writeln!(w, "{}BreakStmt", j)?,
            Stmt::Continue => writeln!(w, "{}ContinueStmt", j)?,
        }

        Ok(())
    }
}

impl FunctionPrototype {
    pub fn print<W: Write>(&self, w: &mut W) -> io::Result<()> {
        writeln!(w, "Name:     {}", self.name)?;
        writeln!(w, "ReturnTy: {}", self.return_ty)?;
        writeln!(w, "Args:")?;

        for (name, ty) in &self.args {
            writeln!(w, "{}{} {}", INDENT_STRING, ty, name)?;
        }

        Ok(())
    }
}

impl Function {
    pub fn print<W: Write>(&self, w: &mut W) -> io::Result<()> {
        self.prototype.print(w)?;

        if let Some(body) = &self.body {
            writeln!(w, "Body:")?;
            print_body(&body, w, 1)?;
        } else {
            writeln!(w, "Extern")?;
        }

        Ok(())
    }
}

impl ParsedModule {
    #[allow(unused)]
    pub fn print<W: Write>(&self, w: &mut W) -> io::Result<()> {
        for func in &self.functions {
            func.print(w)?;
            writeln!(w)?;
        }

        Ok(())
    }
}
