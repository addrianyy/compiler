mod print;

use crate::lexer::{Keyword, Token, Literal, IntegerSuffix, Lexer};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    Ref,
    Deref,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Mod,
    Div,
    Shr,
    Shl,
    And,
    Or,
    Xor,
    Equal,
    NotEqual,
    Gt,
    Lt,
    Gte,
    Lte,
}

impl UnaryOp {
    fn from_token(token: &Token) -> Option<UnaryOp> {
        Some(match token {
            Token::Sub => UnaryOp::Neg,
            Token::Not => UnaryOp::Not,
            Token::And => UnaryOp::Ref,
            Token::Mul => UnaryOp::Deref,
            _          => return None,
        })
    }
}

impl BinaryOp {
    fn from_token(token: &Token) -> Option<BinaryOp> {
        Some(match token {
            Token::Add      => BinaryOp::Add,
            Token::Sub      => BinaryOp::Sub,
            Token::Mul      => BinaryOp::Mul,
            Token::Div      => BinaryOp::Div,
            Token::Shr      => BinaryOp::Shr,
            Token::Shl      => BinaryOp::Shl,
            Token::And      => BinaryOp::And,
            Token::Or       => BinaryOp::Or,
            Token::Xor      => BinaryOp::Xor,
            Token::Equal    => BinaryOp::Equal,
            Token::NotEqual => BinaryOp::NotEqual,
            Token::Gt       => BinaryOp::Gt,
            Token::Lt       => BinaryOp::Lt,
            Token::Gte      => BinaryOp::Gte,
            Token::Lte      => BinaryOp::Lte,
            _               => return None,
        })
    }

    fn precedence(&self) -> i32 {
        match self {
            BinaryOp::Mul   | BinaryOp::Mod | BinaryOp::Div                => 60,
            BinaryOp::Add   | BinaryOp::Sub                                => 50,
            BinaryOp::Shl   | BinaryOp::Shr                                => 40,
            BinaryOp::Gt    | BinaryOp::Lt | BinaryOp::Gte | BinaryOp::Lte => 35,
            BinaryOp::Equal | BinaryOp::NotEqual                           => 33,
            BinaryOp::And                                                  => 30,
            BinaryOp::Xor                                                  => 20,
            BinaryOp::Or                                                   => 10,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    Void,
    Ptr(Box<Ty>),
}

impl Ty {
    pub fn strip_pointer(&self) -> Option<Ty> {
        if let Ty::Ptr(ty) = self {
            Some(*ty.clone())
        } else {
            None
        }
    }

    pub fn is_arithmetic_type(&self) -> bool {
        match self {
            Ty::Ptr(..) | Ty::Void => false,
            _                      => true,
        }
    }

    pub fn is_nonvoid_ptr(&self) -> bool {
        match self {
            Ty::Ptr(ty) => **ty != Ty::Void,
            _           => false,
        }
    }

    pub fn is_void(&self) -> bool {
        matches!(self, Ty::Void)
    }

    fn from_token(token: &Token) -> Option<Self> {
        Some(match token {
            Token::Keyword(Keyword::U8)   => Ty::U8,
            Token::Keyword(Keyword::U16)  => Ty::U16,
            Token::Keyword(Keyword::U32)  => Ty::U32,
            Token::Keyword(Keyword::U64)  => Ty::U64,
            Token::Keyword(Keyword::I8)   => Ty::I8,
            Token::Keyword(Keyword::I16)  => Ty::I16,
            Token::Keyword(Keyword::I32)  => Ty::I32,
            Token::Keyword(Keyword::I64)  => Ty::I64,
            Token::Keyword(Keyword::Void) => Ty::Void,
            _                             => return None,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Variable(String),
    Unary {
        op:    UnaryOp,
        value: Box<TypedExpr>,
    },
    Binary {
        left:  Box<TypedExpr>,
        op:    BinaryOp,
        right: Box<TypedExpr>,
    },
    Number {
        value: u64,
        ty:    Option<Ty>,
    },
    Array {
        array: Box<TypedExpr>,
        index: Box<TypedExpr>,
    },
    Call {
        target: String,
        args:   Vec<TypedExpr>,
    },
    Cast {
        value: Box<TypedExpr>,
        ty:    Ty,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedExpr {
    pub ty:   Option<Ty>,
    pub expr: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Assign {
        variable: TypedExpr, 
        value:    TypedExpr,
    },
    While {
        condition: TypedExpr,
        body:      Body,
    },
    If {
        arms:    Vec<(TypedExpr, Body)>,
        default: Option<Body>,
    },
    Declare {
        /// Actual type.
        ty:       Ty,
        /// Declaration type.
        decl_ty:  Ty,
        name:     String,
        value:    Option<TypedExpr>,
        array:    Option<TypedExpr>,
    },
    Return(Option<TypedExpr>),
    Expr(TypedExpr),
}

pub type Body = Vec<Stmt>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncProto {
    pub name:      String,
    pub args:      Vec<(String, Ty)>,
    pub return_ty: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Func {
    pub proto: FuncProto,
    pub body:  Body,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedModule {
    pub functions: Vec<Func>,
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

            ty    = Ty::Ptr(Box::new(ty));
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

        TypedExpr {
            expr: Expr::Call {
                target,
                args,
            },
            ty: None,
        }
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

                TypedExpr {
                    expr: Expr::Number {
                        value,
                        ty: ty.clone(),
                    },
                    ty,
                }
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
                    TypedExpr {
                        expr: Expr::Variable(ident),
                        ty:   None,
                    }
                }
            }
            Token::ParenOpen => {
                let _ = self.lexer.eat();

                if let Some(_) = Ty::from_token(self.lexer.current()) {
                    let ty   = self.parse_ty();
                    let _    = self.lexer.eat_expect(&Token::ParenClose);
                    let expr = self.parse_primary_expression();

                    TypedExpr {
                        expr: Expr::Cast {
                            value: Box::new(expr),
                            ty,
                        },
                        ty: None,
                    }
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

            result = TypedExpr {
                expr: Expr::Array {
                    array: Box::new(result),
                    index: Box::new(index),
                },
                ty: None,
            }
        }

        result
    }

   fn parse_binary_expression(&mut self, precedence: i32, mut left: TypedExpr) -> TypedExpr {
        let get_token_precedence = |parser: &Self| {
            BinaryOp::from_token(parser.lexer.current())
                .map(|op| op.precedence())
                .unwrap_or(-1)
        };

        loop {
            let next_precedence = get_token_precedence(self);
            if next_precedence < precedence {
                return left;
            }

            let op = BinaryOp::from_token(self.lexer.current()).unwrap();
            let _  = self.lexer.eat();

            let mut right = self.parse_primary_expression();

            if next_precedence < get_token_precedence(self) {
                right = self.parse_binary_expression(next_precedence + 1, right);
            }

            left = TypedExpr {
                expr: Expr::Binary {
                    left:  Box::new(left),
                    right: Box::new(right),
                    op,
                },
                ty: None,
            };
        }
    }

    fn parse_expression(&mut self) -> TypedExpr {
        let left = self.parse_primary_expression();
        let expr = self.parse_binary_expression(0, left);

        expr
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

        TypedExpr { 
            expr: Expr::Unary {
                op, 
                value: Box::new(expr),
            },
            ty: None,
        }
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
                value:    TypedExpr {
                    expr: Expr::Binary {
                        left:  Box::new(expr.clone()),
                        op:    combined,
                        right: Box::new(second),
                    },
                    ty: None,
                }
            });
        }

        stmt.unwrap_or(Stmt::Expr(expr))
    }

    fn parse_declaration(&mut self) -> Stmt {
        let _       = self.lexer.eat_expect(&Token::Keyword(Keyword::Let));
        let name    = self.lexer.eat_identifier().to_string();
        let _       = self.lexer.eat_expect(&Token::Colon);
        let decl_ty = self.parse_ty();
        let mut ty  = decl_ty.clone();

        let mut array = None;

        if self.lexer.current() == &Token::BracketOpen {
            let _ = self.lexer.eat();

            array = Some(self.parse_expression());
            ty    = Ty::Ptr(Box::new(ty));

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

    fn parse_statement(&mut self) -> Stmt {
        match self.lexer.current() {
            Token::Keyword(Keyword::Let)    => self.parse_declaration(),
            Token::Keyword(Keyword::If)     => self.parse_if(),
            Token::Keyword(Keyword::Return) => {
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
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_body(&mut self) -> Body {
        self.lexer.eat_expect(&Token::BraceOpen);

        let mut body = Vec::new();

        while self.lexer.current() != &Token::BraceClose {
            let stmt = self.parse_statement();

            let require_semicolon = match stmt {
                Stmt::While { .. } | Stmt::If { .. } => {
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

    fn parse_function(&mut self) -> Func {
        self.lexer.eat_expect(&Token::Keyword(Keyword::Function));

        let name     = self.lexer.eat_identifier().to_string();
        let mut args = Vec::new();

        self.parse_argument_list(|parser| {
            let name = parser.lexer.eat_identifier().to_string();
            let _    = parser.lexer.eat_expect(&Token::Colon);
            let ty   = parser.parse_ty();

            args.push((name, ty));
        });

        let mut return_ty = Ty::Void;

        if self.lexer.current() == &Token::Arrow {
            let _     = self.lexer.eat();
            return_ty = self.parse_ty();
        }

        let body = self.parse_body();

        Func {
            proto: FuncProto {
                name,
                args,
                return_ty,
            },
            body,
        }
    }

    fn parse_functions(&mut self) -> Vec<Func> {
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
