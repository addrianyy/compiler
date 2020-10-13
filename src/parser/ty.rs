use std::fmt;

use super::lexer::{Token, Keyword};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TyKind {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    Void,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Ty {
    kind:        TyKind,
    indirection: usize,
}

impl Ty {
    pub const U8:   Ty = Ty { kind: TyKind::U8,   indirection: 0 };
    pub const U16:  Ty = Ty { kind: TyKind::U16,  indirection: 0 };
    pub const U32:  Ty = Ty { kind: TyKind::U32,  indirection: 0 };
    pub const U64:  Ty = Ty { kind: TyKind::U64,  indirection: 0 };
    pub const I8:   Ty = Ty { kind: TyKind::I8,   indirection: 0 };
    pub const I16:  Ty = Ty { kind: TyKind::I16,  indirection: 0 };
    pub const I32:  Ty = Ty { kind: TyKind::I32,  indirection: 0 };
    pub const I64:  Ty = Ty { kind: TyKind::I64,  indirection: 0 };

    #[allow(non_upper_case_globals)]
    pub const Void: Ty = Ty { kind: TyKind::Void, indirection: 0 };

    pub(super) fn from_token(token: &Token) -> Option<Self> {
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

    pub fn ptr(&self) -> Ty {
        Ty {
            kind:        self.kind,
            indirection: self.indirection + 1,
        }
    }

    pub fn strip_pointer(&self) -> Option<Ty> {
        Some(Ty {
            kind:        self.kind,
            indirection: self.indirection.checked_sub(1)?,
        })
    }

    pub fn is_arithmetic_type(&self) -> bool {
        self.indirection == 0 && self.kind != TyKind::Void
    }

    pub fn is_pointer(&self) -> bool {
        self.indirection > 0
    }

    pub fn is_signed(&self) -> bool {
        if self.is_pointer() {
            return false;
        }

        matches!(self.kind, TyKind::I8 | TyKind::I16 | TyKind::I32 | TyKind::I64)
    }

    pub fn is_nonvoid_ptr(&self) -> bool {
        if !self.is_pointer() {
            return false;
        }

        if self.indirection == 1 && self.kind == TyKind::Void {
            return false;
        }

        true
    }

    pub fn size(&self) -> usize {
        if self.is_pointer() {
            return 8;
        }

        match self.kind {
            TyKind::I8  | TyKind::U8  => 1,
            TyKind::I16 | TyKind::U16 => 2,
            TyKind::I32 | TyKind::U32 => 4,
            TyKind::I64 | TyKind::U64 => 8,
            TyKind::Void              => panic!("Cannot get size of void."),
        }
    }

    pub fn destructure(&self) -> (TyKind, usize) {
        (self.kind, self.indirection)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            TyKind::U8   => write!(f, "u8")?,
            TyKind::U16  => write!(f, "u16")?,
            TyKind::U32  => write!(f, "u32")?,
            TyKind::U64  => write!(f, "u64")?,
            TyKind::I8   => write!(f, "i8")?,
            TyKind::I16  => write!(f, "i16")?,
            TyKind::I32  => write!(f, "i32")?,
            TyKind::I64  => write!(f, "i64")?,
            TyKind::Void => write!(f, "void")?,
        }

        for _ in 0..self.indirection {
            write!(f, "*")?;
        }

        Ok(())
    }
}
