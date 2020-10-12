use std::io::{self, Write};
use std::fmt;

use super::{Ty, Stmt, Expr, TypedExpr, Body, Function, FunctionPrototype, ParsedModule};

const INDENT_STRING:  &str = "    ";
const SUBITEM_INDENT: &str = "  ";

fn print_body<W: Write>(body: &Body, w: &mut W, indent: usize) -> io::Result<()> {
    for stmt in body {
        stmt.print(w, indent)?;
    }

    Ok(())
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ty::U8          => write!(f, "u8")?,
            Ty::U16         => write!(f, "u16")?,
            Ty::U32         => write!(f, "u32")?,
            Ty::U64         => write!(f, "u64")?,
            Ty::I8          => write!(f, "i8")?,
            Ty::I16         => write!(f, "i16")?,
            Ty::I32         => write!(f, "i32")?,
            Ty::I64         => write!(f, "i64")?,
            Ty::Void        => write!(f, "void")?,
            Ty::Ptr(inside) => write!(f, "{}*", inside)?,
        }

        Ok(())
    }
}

impl TypedExpr {
    pub fn print<W: Write>(&self, w: &mut W, indent: usize) -> io::Result<()> {
        self.expr.print(w, indent)
    }
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
            Expr::Number { value, ty } => {
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

                writeln!(w, "{}Target: {}", j, target)?;

                writeln!(w, "{}Args:", j)?;
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

        writeln!(w, "Body:")?;
        print_body(&self.body, w, 1)?;

        Ok(())
    }
}

impl ParsedModule {
    pub fn print<W: Write>(&self, w: &mut W) -> io::Result<()> {
        for func in &self.functions {
            func.print(w)?;
            writeln!(w)?;
        }

        Ok(())
    }
}
