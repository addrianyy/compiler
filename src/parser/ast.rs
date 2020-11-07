use super::ty::Ty;
use super::lexer::Token;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    Ref,
    Deref,
}

impl UnaryOp {
    pub(super) fn from_token(token: &Token) -> Option<UnaryOp> {
        Some(match token {
            Token::Sub => UnaryOp::Neg,
            Token::Not => UnaryOp::Not,
            Token::And => UnaryOp::Ref,
            Token::Mul => UnaryOp::Deref,
            _          => return None,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

impl BinaryOp {
    pub(super) fn from_token(token: &Token) -> Option<BinaryOp> {
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

    pub(super) fn precedence(&self) -> i32 {
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
        ty:    Ty,
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
pub enum Stmt {
    Assign {
        variable: TypedExpr,
        value:    TypedExpr,
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
    While {
        condition: TypedExpr,
        body:      Body,
    },
    If {
        arms:    Vec<(TypedExpr, Body)>,
        default: Option<Body>,
    },
    For {
        init:      Option<Box<Stmt>>,
        condition: Option<TypedExpr>,
        step:      Option<Box<Stmt>>,
        body:      Body,
    },
    Return(Option<TypedExpr>),
    Expr(TypedExpr),
    Break,
    Continue,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedExpr {
    pub ty:   Option<Ty>,
    pub expr: Expr,
}

impl TypedExpr {
    pub(super) fn new(expr: Expr) -> Self {
        Self {
            ty: None,
            expr,
        }
    }
}

impl std::ops::Deref for TypedExpr {
    type Target = Expr;

    fn deref(&self) -> &Expr {
        &self.expr
    }
}

pub type Body        = Vec<Stmt>;
pub type BodyRef<'a> = &'a [Stmt];
