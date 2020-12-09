#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Keyword {
    Void,
    Undefined,
    Null,
    True,
    False,
    U1,
    U8,
    U16,
    U32,
    U64,
    Neg,
    Not,
    Add,
    Sub,
    Mul,
    Umod,
    Udiv,
    Smod,
    Sdiv,
    Shr,
    Shl,
    Sar,
    And,
    Or,
    Xor,
    Cmp,
    Eq,
    Ne,
    Ugt,
    Ugte,
    Sgt,
    Sgte,
    Load,
    Store,
    Call,
    Branch,
    Bcond,
    Stackalloc,
    Ret,
    Gep,
    To,
    Zext,
    Sext,
    Trunc,
    Bitcast,
    Select,
    Phi,
    Alias,
    Nop,
}

impl Keyword {
    fn from_identifier(identifier: &str) -> Option<Keyword> {
        Some(match identifier {
            "void"       => Keyword::Void,
            "undefined"  => Keyword::Undefined,
            "null"       => Keyword::Null,
            "true"       => Keyword::True,
            "false"      => Keyword::False,
            "u1"         => Keyword::U1,
            "u8"         => Keyword::U8,
            "u16"        => Keyword::U16,
            "u32"        => Keyword::U32,
            "u64"        => Keyword::U64,
            "neg"        => Keyword::Neg,
            "not"        => Keyword::Not,
            "add"        => Keyword::Add,
            "sub"        => Keyword::Sub,
            "mul"        => Keyword::Mul,
            "umod"       => Keyword::Umod,
            "udiv"       => Keyword::Udiv,
            "smod"       => Keyword::Smod,
            "sdiv"       => Keyword::Sdiv,
            "shr"        => Keyword::Shr,
            "shl"        => Keyword::Shl,
            "sar"        => Keyword::Sar,
            "and"        => Keyword::And,
            "or"         => Keyword::Or,
            "xor"        => Keyword::Xor,
            "cmp"        => Keyword::Cmp,
            "eq"         => Keyword::Eq,
            "ne"         => Keyword::Ne,
            "ugt"        => Keyword::Ugt,
            "ugte"       => Keyword::Ugte,
            "sgt"        => Keyword::Sgt,
            "sgte"       => Keyword::Sgte,
            "load"       => Keyword::Load,
            "store"      => Keyword::Store,
            "call"       => Keyword::Call,
            "branch"     => Keyword::Branch,
            "bcond"      => Keyword::Bcond,
            "stackalloc" => Keyword::Stackalloc,
            "ret"        => Keyword::Ret,
            "gep"        => Keyword::Gep,
            "to"         => Keyword::To,
            "zext"       => Keyword::Zext,
            "sext"       => Keyword::Sext,
            "trunc"      => Keyword::Trunc,
            "bitcast"    => Keyword::Bitcast,
            "select"     => Keyword::Select,
            "phi"        => Keyword::Phi,
            "alias"      => Keyword::Alias,
            "nop"        => Keyword::Nop,
            _            => return None,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    Identifier(String),
    Keyword(Keyword),
    Literal(i64),

    Colon,
    Comma,
    Star,
    Assign,

    ParenOpen,
    ParenClose,
    BraceOpen,
    BraceClose,
    BracketOpen,
    BracketClose,

    Eof,
}

pub struct Lexer {
    cursor: usize,
    tokens: Vec<Token>,
}

impl Lexer {
    pub fn new(mut source: &str) -> Self {
        const STATIC_TOKENS: &[(&str, Token)] = &[
            ("(", Token::ParenOpen),
            (")", Token::ParenClose),
            ("{", Token::BraceOpen),
            ("}", Token::BraceClose),
            ("[", Token::BracketOpen),
            ("]", Token::BracketClose),
            (":", Token::Colon),
            (",", Token::Comma),
            ("*", Token::Star),
            ("=", Token::Assign),
        ];

        let mut tokens = Vec::new();

        'lex_next: while !source.is_empty() {
            source = source.trim_start();

            if source.is_empty() {
                break;
            }

            if source.starts_with("//") {
                source = &source[2..];

                let mut end = source.len();

                for (index, ch) in source.char_indices() {
                    if ch == '\n' || ch == '\r' {
                        end = index + ch.len_utf8();
                        break;
                    }
                }

                source = &source[end..];

                continue 'lex_next;
            }

            for (string, token) in STATIC_TOKENS {
                if source.starts_with(string) {
                    source = &source[string.len()..];

                    tokens.push(token.clone());

                    continue 'lex_next;
                }
            }

            let ch = source.chars().next().unwrap();
            if  ch.is_numeric() || ch == '-' {
                const VALID_DEC: &[char] = &['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
                const VALID_HEX: &[char] = &['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
                    'a', 'b', 'c', 'd', 'e', 'f', 'A', 'B', 'C', 'D', 'E', 'F'];

                let negative = ch == '-';

                let offset = match negative {
                    true  => 1,
                    false => 0,
                };

                let (valid, base) = match source[offset..].starts_with("0x") {
                    true => {
                        assert!(!negative, "Negative hex literals are not supported.");

                        source = &source[2..];

                        (VALID_HEX, 16)
                    }
                    false => (VALID_DEC, 10),
                };

                let end = source[offset..].find(|ch: char| !valid.iter().any(|x| *x == ch))
                    .unwrap_or_else(|| source.len() - offset) + offset;

                let literal = &source[..end];
                let literal = i64::from_str_radix(literal, base)
                    .expect("Invalid number literal.");

                source = &source[end..];

                tokens.push(Token::Literal(literal));

                continue 'lex_next;
            }

            let end = source.find(|ch: char| !ch.is_alphanumeric() && ch != '_')
                .unwrap_or_else(|| source.len());

            let identifier = &source[..end];

            source = &source[end..];

            assert!(!identifier.is_empty(), "Invalid state: {}.", source);

            let token = match Keyword::from_identifier(identifier) {
                Some(keyword) => Token::Keyword(keyword),
                None          => Token::Identifier(identifier.to_string()),
            };

            tokens.push(token);
        }

        Lexer {
            tokens,
            cursor: 0,
        }
    }

    pub fn cursor(&self) -> usize {
        self.cursor
    }

    pub fn set_cursor(&mut self, cursor: usize) {
        self.cursor = cursor;
    }

    fn token(&self, cursor: usize) -> &Token {
        const EOF: Token = Token::Eof;

        if cursor >= self.tokens.len() {
            return &EOF;
        }

        &self.tokens[cursor]
    }

    pub fn eat(&mut self) -> &Token {
        let cursor = self.cursor;

        self.cursor += 1;

        self.token(cursor)
    }

    pub fn current(&self) -> &Token {
        self.token(self.cursor)
    }

    #[track_caller]
    pub fn eat_keyword(&mut self) -> Keyword {
        let token = self.eat();

        if let Token::Keyword(expected) = token {
            *expected
        } else {
            panic!("Expected keyword, got {:?}.", token);
        }
    }

    #[track_caller]
    pub fn eat_identifier(&mut self) -> &str {
        let token = self.eat();

        if let Token::Identifier(expected) = token {
            expected
        } else {
            panic!("Expected identifier, got {:?}.", token);
        }
    }

    #[track_caller]
    pub fn eat_expect(&mut self, expected: &Token) {
        let token = self.eat();

        if token != expected {
            panic!("Expected {:?}, got {:?}.", expected, token);
        }
    }
}
