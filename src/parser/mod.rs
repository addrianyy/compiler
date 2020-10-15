mod print;
mod lexer;
mod ast;
mod ty;

use lexer::{Keyword, Token, Literal, IntegerSuffix, Lexer};
pub use ast::{UnaryOp, BinaryOp, Expr, TypedExpr, Stmt, Body, BodyRef};
pub use ty::{TyKind, Ty};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionPrototype {
    pub name:      String,
    pub args:      Vec<(String, Ty)>,
    pub return_ty: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub prototype: FunctionPrototype,
    pub body:      Body,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedModule {
    pub functions: Vec<Function>,
}

struct Parser {
    lexer: Lexer,
}

impl Parser {
    fn new(lexer: Lexer) -> Self {
        Self {
            lexer,
        }
    }

    fn parse_ty(&mut self) -> Ty {
        let current = self.lexer.eat();
        let mut ty  = Ty::from_token(current)
            .unwrap_or_else(|| panic!("Invalid type keyword {:?}.", current));

        loop {
            if self.lexer.current() != &Token::Mul {
                break;
            }

            ty    = ty.ptr();
            let _ = self.lexer.eat();
        }

        ty
    }

    fn parse_argument_list(&mut self, mut callback: impl FnMut(&mut Self)) {
        self.lexer.eat_expect(&Token::ParenOpen);

        loop {
            if self.lexer.current() == &Token::ParenClose {
                let _ = self.lexer.eat();
                break;
            }

            callback(self);

            let current = self.lexer.current();

            if current == &Token::Comma {
                let _ = self.lexer.eat();
            } else {
                assert!(current == &Token::ParenClose,
                        "Expected comma or closing paren in argument list. Got {:?}", current);
            }
        }
    }

    fn parse_call_expression(&mut self, target: String) -> TypedExpr {
        let mut args = Vec::new();

        self.parse_argument_list(|parser| {
            args.push(parser.parse_expression());
        });

        TypedExpr::new(Expr::Call {
            target,
            args,
        })
    }

    fn parse_primary_expression(&mut self) -> TypedExpr {
        let current = self.lexer.current();

        if let Some(unary) = UnaryOp::from_token(current) {
            return self.parse_unary_expression(unary);
        }

        let mut result = match current {
            Token::Literal(Literal::Number { value, suffix }) => {
                let ty = suffix.as_ref().map(|suffix| {
                    match suffix {
                        IntegerSuffix::U8  => Ty::U8,
                        IntegerSuffix::U16 => Ty::U16,
                        IntegerSuffix::U32 => Ty::U32,
                        IntegerSuffix::U64 => Ty::U64,
                        IntegerSuffix::I8  => Ty::I8,
                        IntegerSuffix::I16 => Ty::I16,
                        IntegerSuffix::I32 => Ty::I32,
                        IntegerSuffix::I64 => Ty::I64,
                    }
                });

                let value = *value;
                let _     = self.lexer.eat();

                TypedExpr::new(Expr::Number {
                    value,
                    ty,
                })
            }
            Token::Literal(Literal::Char(value)) => {
                let value = *value as u64;
                let _     = self.lexer.eat();

                TypedExpr::new(Expr::Number {
                    value,
                    ty: Some(Ty::U8),
                })
            }
            Token::Literal(..) => {
                panic!("Literal {:?} is not supported. Only number literals are supported.", 
                       current);
            }
            Token::Identifier(ident) => {
                let ident = ident.clone();
                let _     = self.lexer.eat();

                if self.lexer.current() == &Token::ParenOpen {
                    self.parse_call_expression(ident)
                } else {
                    TypedExpr::new(Expr::Variable(ident))
                }
            }
            Token::ParenOpen => {
                let _ = self.lexer.eat();

                if Ty::from_token(self.lexer.current()).is_some() {
                    let ty   = self.parse_ty();
                    let _    = self.lexer.eat_expect(&Token::ParenClose);
                    let expr = self.parse_primary_expression();

                    TypedExpr::new(Expr::Cast {
                        value: Box::new(expr),
                        ty,
                    })
                } else {
                    self.lexer.restore(1);
                    self.parse_paren_expression()
                }
            }
            _ => panic!("Unexpected token in primary expression: {:?}.", current),
        };

        if self.lexer.current() == &Token::BracketOpen {
            let _     = self.lexer.eat();
            let index = self.parse_expression();
            let _     = self.lexer.eat_expect(&Token::BracketClose);

            result = TypedExpr::new(Expr::Array {
                array: Box::new(result),
                index: Box::new(index),
            });
        }

        result
    }

   fn parse_binary_expression(&mut self, mininal_precedence: i32,
                              mut expr: TypedExpr) -> TypedExpr {
        let get_token_precedence = |parser: &Self| {
            BinaryOp::from_token(parser.lexer.current())
                .map(|op| op.precedence())
                .unwrap_or(-1)
        };

        loop {
            let precedence = get_token_precedence(self);
            if  precedence < mininal_precedence {
                return expr;
            }

            let op        = BinaryOp::from_token(self.lexer.current()).unwrap();
            let _         = self.lexer.eat();
            let mut right = self.parse_primary_expression();

            let next_precedence = get_token_precedence(self);
            if  next_precedence > precedence {
                right = self.parse_binary_expression(precedence + 1, right);
            }

            expr = TypedExpr::new(Expr::Binary {
                left:  Box::new(expr),
                right: Box::new(right),
                op,
            });
        }
    }

    fn parse_expression(&mut self) -> TypedExpr {
        let left = self.parse_primary_expression();

        self.parse_binary_expression(0, left)
    }

    fn parse_paren_expression(&mut self) -> TypedExpr {
        let _    = self.lexer.eat_expect(&Token::ParenOpen);
        let expr = self.parse_expression();
        let _    = self.lexer.eat_expect(&Token::ParenClose);

        expr
    }

    fn parse_unary_expression(&mut self, op: UnaryOp) -> TypedExpr {
        let _    = self.lexer.eat();
        let expr = self.parse_primary_expression();

        TypedExpr::new(Expr::Unary {
            op, 
            value: Box::new(expr),
        })
    }

    fn parse_expression_statement(&mut self) -> Stmt {
        let expr         = self.parse_expression();
        let mut stmt     = None;
        let mut combined = None;

        match self.lexer.current() {
            Token::Assign => {
                let _ = self.lexer.eat();

                stmt = Some(Stmt::Assign {
                    variable: expr.clone(),
                    value:    self.parse_expression(),
                });
            }
            Token::AddAssign => combined = Some(BinaryOp::Add),
            Token::SubAssign => combined = Some(BinaryOp::Sub),
            Token::MulAssign => combined = Some(BinaryOp::Mul),
            Token::ModAssign => combined = Some(BinaryOp::Mod),
            Token::DivAssign => combined = Some(BinaryOp::Div),
            Token::ShrAssign => combined = Some(BinaryOp::Shr),
            Token::ShlAssign => combined = Some(BinaryOp::Shl),
            Token::AndAssign => combined = Some(BinaryOp::And),
            Token::OrAssign  => combined = Some(BinaryOp::Or),
            Token::XorAssign => combined = Some(BinaryOp::Xor),
            _                => (),
        }

        if let Some(combined) = combined {
            let _      = self.lexer.eat();
            let second = self.parse_expression();

            stmt = Some(Stmt::Assign {
                variable: expr.clone(),
                value:    TypedExpr::new(Expr::Binary {
                    left:  Box::new(expr.clone()),
                    op:    combined,
                    right: Box::new(second),
                })
            });
        }

        stmt.unwrap_or(Stmt::Expr(expr))
    }

    fn parse_declaration(&mut self) -> Stmt {
        let decl_ty = self.parse_ty();
        let name    = self.lexer.eat_identifier().to_string();

        let mut ty    = decl_ty;
        let mut array = None;

        if self.lexer.current() == &Token::BracketOpen {
            let _ = self.lexer.eat();

            array = Some(self.parse_expression());
            ty    = ty.ptr();

            self.lexer.eat_expect(&Token::BracketClose);
        }

        let mut value = None;

        if self.lexer.current() == &Token::Assign {
            let _ = self.lexer.eat();

            value = Some(self.parse_expression());
        }

        Stmt::Declare {
            ty,
            decl_ty,
            name,
            array,
            value,
        }
    }

    fn parse_if(&mut self) -> Stmt {
        let _ = self.lexer.eat_expect(&Token::Keyword(Keyword::If));

        let main_cond = self.parse_paren_expression();
        let main_body = self.parse_body();

        let mut default = None;
        let mut arms    = Vec::new();

        arms.push((main_cond, main_body));

        loop {
            if self.lexer.current() != &Token::Keyword(Keyword::Else) {
                break;
            }

            let _      = self.lexer.eat();
            let elseif = if self.lexer.current() == &Token::Keyword(Keyword::If) {
                let _ = self.lexer.eat();
                true
            } else {
                false
            };

            let mut condition = None;

            if elseif {
                condition = Some(self.parse_paren_expression());
            }

            let body = self.parse_body();

            if let Some(condition) = condition {
                arms.push((condition, body));
            } else {
                default = Some(body);
                break;
            }
        }

        Stmt::If {
            arms,
            default,
        }
    }

    fn parse_for(&mut self) -> Stmt {
        self.lexer.eat_expect(&Token::Keyword(Keyword::For));
        self.lexer.eat_expect(&Token::ParenOpen);

        let mut init      = None;
        let mut condition = None;
        let mut step      = None;

        if self.lexer.current() != &Token::Semicolon {
            init = Some(Box::new(self.parse_statement()));
        }

        self.lexer.eat_expect(&Token::Semicolon);

        if self.lexer.current() != &Token::Semicolon {
            condition = Some(self.parse_expression());
        }

        self.lexer.eat_expect(&Token::Semicolon);

        if self.lexer.current() != &Token::ParenClose {
            step = Some(Box::new(self.parse_statement()));
        }

        self.lexer.eat_expect(&Token::ParenClose);

        let body = self.parse_body();

        Stmt::For {
            init,
            condition,
            step,
            body,
        }
    }

    fn parse_statement(&mut self) -> Stmt {
        match self.lexer.current() {
            x if Ty::from_token(x).is_some() => self.parse_declaration(),
            Token::Keyword(Keyword::If)      => self.parse_if(),
            Token::Keyword(Keyword::For)     => self.parse_for(),
            Token::Keyword(Keyword::Return)  => {
                let _ = self.lexer.eat();

                let value = if self.lexer.current() != &Token::Semicolon {
                    Some(self.parse_expression())
                } else {
                    None
                };

                Stmt::Return(value)
            }
            Token::Keyword(Keyword::While) => {
                let _    = self.lexer.eat();
                let cond = self.parse_paren_expression();
                let body = self.parse_body();

                Stmt::While {
                    condition: cond,
                    body,
                }
            }
            Token::Keyword(Keyword::Continue) => {
                self.lexer.eat();
                Stmt::Continue
            }
            Token::Keyword(Keyword::Break) => {
                self.lexer.eat();
                Stmt::Break
            }
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_body(&mut self) -> Body {
        self.lexer.eat_expect(&Token::BraceOpen);

        let mut body = Vec::new();

        while self.lexer.current() != &Token::BraceClose {
            let stmt = self.parse_statement();

            let require_semicolon = match stmt {
                Stmt::While { .. } | Stmt::If { .. } | Stmt::For { .. } => {
                    false
                }
                _ => true,
            };

            if require_semicolon {
                self.lexer.eat_expect(&Token::Semicolon);
            }

            body.push(stmt);
        }

        self.lexer.eat_expect(&Token::BraceClose);

        body
    }

    fn parse_function(&mut self) -> Function {
        let return_ty = self.parse_ty();
        let name      = self.lexer.eat_identifier().to_string();
        let mut args  = Vec::new();

        self.parse_argument_list(|parser| {
            let ty   = parser.parse_ty();
            let name = parser.lexer.eat_identifier().to_string();

            args.push((name, ty));
        });

        let body = self.parse_body();

        Function {
            prototype: FunctionPrototype {
                name,
                args,
                return_ty,
            },
            body,
        }
    }

    fn parse_functions(&mut self) -> Vec<Function> {
        let mut functions = Vec::new();

        while self.lexer.current() != &Token::Eof {
            functions.push(self.parse_function());
        }

        functions
    }
}

pub fn parse(source: &str) -> ParsedModule {
    let     lexer     = Lexer::new(source);
    let mut parser    = Parser::new(lexer);
    let     functions = parser.parse_functions();

    ParsedModule {
        functions,
    }
}
