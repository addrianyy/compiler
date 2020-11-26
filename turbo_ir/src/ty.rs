#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(super) enum TypeKind {
    U1,
    U8,
    U16,
    U32,
    U64,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Type {
    pub(super) kind:        TypeKind,
    pub(super) indirection: usize,
}

impl Type {
    pub const U1:  Type = Type { kind: TypeKind::U1,  indirection: 0 };
    pub const U8:  Type = Type { kind: TypeKind::U8,  indirection: 0 };
    pub const U16: Type = Type { kind: TypeKind::U16, indirection: 0 };
    pub const U32: Type = Type { kind: TypeKind::U32, indirection: 0 };
    pub const U64: Type = Type { kind: TypeKind::U64, indirection: 0 };

    pub fn with_indirection(self, indirection: usize) -> Type {
        Self {
            kind: self.kind,
            indirection,
        }
    }

    pub fn ptr(self) -> Self {
        Self {
            kind:        self.kind,
            indirection: self.indirection + 1,
        }
    }

    pub fn strip_ptr(self) -> Option<Self> {
        Some(Self {
            kind:        self.kind,
            indirection: self.indirection.checked_sub(1)?,
        })
    }

    pub fn is_pointer(&self) -> bool {
        self.indirection > 0
    }

    pub fn is_arithmetic(&self) -> bool {
        self.indirection == 0 && self.kind != TypeKind::U1
    }

    pub fn size(&self) -> usize {
        if self.is_pointer() {
            return 8;
        }

        match self.kind {
            TypeKind::U1  => panic!("Cannot get size of U1."),
            TypeKind::U8  => 1,
            TypeKind::U16 => 2,
            TypeKind::U32 => 4,
            TypeKind::U64 => 8,
        }
    }

    pub fn size_bits(&self) -> usize {
        if self.is_pointer() {
            return 64;
        }

        match self.kind {
            TypeKind::U1  => 1,
            TypeKind::U8  => 8,
            TypeKind::U16 => 16,
            TypeKind::U32 => 32,
            TypeKind::U64 => 64,
        }
    }

    pub fn bitmask(&self) -> u64 {
        if self.is_pointer() {
            return 0xffff_ffff_ffff_ffff;
        }

        match self.kind {
            TypeKind::U1  => 1,
            TypeKind::U8  => 0xff,
            TypeKind::U16 => 0xffff,
            TypeKind::U32 => 0xffffffff,
            TypeKind::U64 => 0xffff_ffff_ffff_ffff,
        }
    }
}
