use lexer::{Keyword, Token, IntegerSuffix};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    Ref,
    Deref,
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
}

impl BinaryOp {
    fn from_token(token: &Token) -> Option<BinaryOp> {
        None
    }

    fn precedence(&self) -> i32 {
        panic!()
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Variable(String),
    Deref(Box<Expr>),
    Unary {
        op:    UnaryOp,
        value: Box<Expr>,
    },
    Binary {
        left:  Box<Expr>,
        op:    BinaryOp,
        right: Box<Expr>,
    },
    Number {
        value:  u64,
        suffix: IntegerSuffix,
    },
    Array {
        array: Box<Expr>,
        index: Box<Expr>,
    },
    Call {
        target: String,
        args:   Vec<Expr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Assign {
        variable: Expr, 
        value:    Expr,
    },
    While {
        condition: Expr,
        body:      Vec<Stmt>,
    },
    If {
        condition: Expr,
        body:      Vec<Stmt>,
    },
    Declare {
        ty:    Ty,
        name:  String,
        value: Option<Expr>,
        array: Option<(Ty, usize)>,
    },
    Expr(Expr),
}

pub struct Parser {
    lexer: crate::lexer::Lexer,
}

use crate::lexer;

#[derive(Clone, Debug, PartialEq, Eq)]
struct FuncProto {
    name:      String,
    args:      Vec<(String, Ty)>,
    return_ty: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Func {
    proto: FuncProto,
    body:  Vec<Stmt>,
}

impl Parser {
    pub fn new(lexer: lexer::Lexer) -> Self {
        let mut x = Self {
            lexer
        };

        x.parse_function();

        x
    }

    fn parse_ty(&mut self) -> Ty {
        let mut ty = match self.lexer.eat_keyword() {
            lexer::Keyword::U8   => Ty::U8,
            lexer::Keyword::U16  => Ty::U16,
            lexer::Keyword::U32  => Ty::U32,
            lexer::Keyword::U64  => Ty::U64,
            lexer::Keyword::I8   => Ty::I8,
            lexer::Keyword::I16  => Ty::I16,
            lexer::Keyword::I32  => Ty::I32,
            lexer::Keyword::I64  => Ty::I64,
            lexer::Keyword::Void => Ty::Void,
            x                    => panic!("Invalid type keyword {:?}.", x),
        };

        loop {
            if self.lexer.current() != &lexer::Token::Mul {
                break;
            }

            ty = Ty::Ptr(Box::new(ty));

            let _ = self.lexer.eat();
        }

        ty
    }

    fn parse_primary_expression(&mut self) -> Expr {
        let current = self.lexer.current();

        if let Some(unary) = UnaryOp::from_token(current) {
            return self.parse_unary_expression(unary);
        }

        panic!()
    }

   fn parse_binary_expression(&mut self, precedence: i32, mut left: Expr) -> Expr {
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

            left = Expr::Binary {
                left:  Box::new(left),
                right: Box::new(right),
                op,
            };
        }
    }

    fn parse_expression(&mut self) -> Expr {
        panic!()
    }

    fn parse_unary_expression(&mut self, op: UnaryOp) -> Expr {
        let _    = self.lexer.eat();
        let expr = self.parse_expression();

        Expr::Unary {
            op, 
            value: Box::new(expr),
        }
    }

    fn parse_statement(&mut self) -> Stmt {
        panic!()
    }

    fn parse_body(&mut self) -> Vec<Stmt> {
        self.lexer.eat_expect(&Token::BraceOpen);

        let mut body = Vec::new();

        while self.lexer.current() != &Token::BraceClose {
            body.push(self.parse_statement());
        }

        self.lexer.eat_expect(&Token::BraceClose);

        body
    }

    fn parse_function(&mut self) -> Func {
        self.lexer.eat_expect(&Token::Keyword(Keyword::Function));

        let name = self.lexer.eat_identifier().to_string();

        self.lexer.eat_expect(&Token::ParenOpen);

        let mut args = Vec::new();

        loop {
            let current = self.lexer.current();
            if current == &Token::ParenClose {
                let _ = self.lexer.eat();
                break;
            }

            let arg_name = self.lexer.eat_identifier().to_string();

            self.lexer.eat_expect(&Token::Colon);

            let arg_ty = self.parse_ty();

            args.push((arg_name, arg_ty));

            let current = self.lexer.current();
            if current == &Token::Comma {
                let _ = self.lexer.eat();
            } else {
                assert!(current == &Token::ParenClose, "Expected comma or closing paren.");
            }
        }

        let mut return_ty = Ty::Void;

        if self.lexer.current() == &Token::Arrow {
            let _ = self.lexer.eat();

            return_ty = self.parse_ty();
        }

        let body = self.parse_body();

        let proto = FuncProto {
            name,
            args,
            return_ty,
        };

        let func = Func {
            proto,
            body,
        };

        println!("{:?}", func);

        panic!()
    }
}
