#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Keyword {
    Void,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    For,
    While,
    If,
    Else,
    Break,
    Continue,
    Return,
    Extern,
}

impl Keyword {
    fn from_ident(ident: &str) -> Option<Keyword> {
        Some(match ident {
            "void"     => Keyword::Void,
            "u8"       => Keyword::U8,
            "u16"      => Keyword::U16,
            "u32"      => Keyword::U32,
            "u64"      => Keyword::U64,
            "i8"       => Keyword::I8,
            "i16"      => Keyword::I16,
            "i32"      => Keyword::I32,
            "i64"      => Keyword::I64,
            "for"      => Keyword::For,
            "while"    => Keyword::While,
            "if"       => Keyword::If,
            "else"     => Keyword::Else,
            "break"    => Keyword::Break,
            "continue" => Keyword::Continue,
            "return"   => Keyword::Return,
            "extern"   => Keyword::Extern,
            _          => return None,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntegerSuffix {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Literal {
    Char(u8),
    String(String),
    Number {
        value:  u64,
        suffix: Option<IntegerSuffix>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    Identifier(String),
    Keyword(Keyword),
    Literal(Literal),

    Colon,
    Semicolon,
    Comma,

    ParenOpen,
    ParenClose,
    BraceOpen,
    BraceClose,
    BracketOpen,
    BracketClose,

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
    Not,
    Assign,

    AddAssign,
    SubAssign,
    MulAssign,
    ModAssign,
    DivAssign,
    ShrAssign,
    ShlAssign,
    AndAssign,
    OrAssign,
    XorAssign,

    Equal,
    NotEqual,
    Gt,
    Lt,
    Gte,
    Lte,

    Eof,
}

pub struct Lexer {
    cursor: isize,
    tokens: Vec<Token>,
}

impl Lexer {
    pub fn new(mut source: &str) -> Self {
        const STATIC_TOKENS: &[(&str, Token)] = &[
            (">>=", Token::ShrAssign),
            ("<<=", Token::ShlAssign),

            ("==", Token::Equal),
            ("!=", Token::NotEqual),
            (">=", Token::Gte),
            ("<=", Token::Lte),

            ("+=", Token::AddAssign),
            ("-=", Token::SubAssign),
            ("*=", Token::MulAssign),
            ("%=", Token::ModAssign),
            ("/=", Token::DivAssign),
            ("&=", Token::AndAssign),
            ("|=", Token::OrAssign),
            ("^=", Token::XorAssign),

            (">>", Token::Shr),
            ("<<", Token::Shl),

            ("+",  Token::Add),
            ("-",  Token::Sub),
            ("*",  Token::Mul),
            ("%",  Token::Mod),
            ("/",  Token::Div),
            ("&",  Token::And),
            ("|",  Token::Or),
            ("^",  Token::Xor),
            ("~",  Token::Not),
            ("=",  Token::Assign),

            ("(",  Token::ParenOpen),
            (")",  Token::ParenClose),
            ("{",  Token::BraceOpen),
            ("}",  Token::BraceClose),
            ("[",  Token::BracketOpen),
            ("]",  Token::BracketClose),

            (",",  Token::Comma),
            (":",  Token::Colon),
            (";",  Token::Semicolon),
            (">",  Token::Gt),
            ("<",  Token::Lt),
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

            match source.chars().next().expect("Source is empty for some reason.") {
                '\'' => {
                    source = &source[1..];

                    // TODO: improve this, properly handle escapes.
                    let end    = source.find(|c: char| c == '\'').unwrap();
                    let inside = &source[..end];

                    source = &source[end + 1..];

                    assert!(inside.len() == 1);
                    let ch = inside.bytes().next().unwrap();

                    tokens.push(Token::Literal(Literal::Char(ch)));

                    continue 'lex_next;
                }
                '\"' => {
                    source = &source[1..];

                    let mut escaped = false;
                    let mut end     = None;
                    let mut literal = String::new();

                    for (index, ch) in source.char_indices() {
                        if !escaped {
                            match ch {
                                '\\' => {
                                    escaped = true;
                                    continue;
                                }
                                '\"' => {
                                    end = Some(index + ch.len_utf8());
                                    break;
                                }
                                _ => literal.push(ch),
                            }
                        } else {
                            match ch {
                                '\"' | '\\' => (),
                                _           => {
                                    panic!("Invalid string escaped character {}.", ch);
                                }
                            }

                            literal.push(ch);
                        }

                        escaped = false;
                    }

                    let end = end.expect("Non-closed quote.");
                    source = &source[end..];

                    tokens.push(Token::Literal(Literal::String(literal)));

                    continue 'lex_next;
                }
                x if x.is_numeric() => {
                    #[derive(PartialEq, Eq)]
                    enum Base {
                        Dec,
                        Bin,
                        Hex,
                    }

                    let mut base = Base::Dec;

                    if source.starts_with("0x") {
                        source = &source[2..];
                        base   = Base::Hex;
                    } else if source.starts_with("0b") {
                        source = &source[2..];
                        base   = Base::Bin;
                    }

                    const VALID_BIN: &[char] = &['0', '1'];
                    const VALID_DEC: &[char] = &['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
                    const VALID_HEX: &[char] = &['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
                        'a', 'b', 'c', 'd', 'e', 'f', 'A', 'B', 'C', 'D', 'E', 'F'];

                    let valid = match base {
                        Base::Dec => VALID_DEC,
                        Base::Bin => VALID_BIN,
                        Base::Hex => VALID_HEX,
                    };

                    let mut has_dot = false;
                    let mut literal = String::new();

                    for (index, ch) in source.char_indices() {
                        if ch == '_' {
                            continue;
                        }

                        if ch == '.' {
                            assert!(base == Base::Dec,
                                    "Only decimal float literals are supported.");
                            assert!(!has_dot, "Multiple dots in float literal.");

                            has_dot = true;
                        } else if valid.iter().find(|x| **x == ch).is_none() {
                            source = &source[index..];
                            break;
                        }

                        literal.push(ch);
                    }

                    if !has_dot {
                        const SUFFIXES: &[(&str, IntegerSuffix)]  = &[
                            ("u8",  IntegerSuffix::U8),
                            ("u16", IntegerSuffix::U16),
                            ("u32", IntegerSuffix::U32),
                            ("u64", IntegerSuffix::U64),
                            ("i8",  IntegerSuffix::I8),
                            ("i16", IntegerSuffix::I16),
                            ("i32", IntegerSuffix::I32),
                            ("i64", IntegerSuffix::I64),
                        ];

                        let mut int_suffix = None;

                        for (string, suffix) in SUFFIXES {
                            if source.starts_with(string) {
                                source     = &source[string.len()..];
                                int_suffix = Some(suffix.clone());

                                break;
                            }
                        }

                        let base = match base {
                            Base::Bin => 2,
                            Base::Dec => 10,
                            Base::Hex => 16,
                        };

                        let value = u64::from_str_radix(&literal, base)
                            .expect("Invalid number literal.");

                        tokens.push(Token::Literal(Literal::Number {
                            suffix: int_suffix,
                            value,
                        }));
                    } else {
                        panic!("Float literals are not yet supported.");
                    }

                    continue 'lex_next;
                }
                _ => (),
            }

            let end = source.find(|c: char| !c.is_alphanumeric() && c != '_')
                .unwrap_or_else(|| source.len());
            let ident = &source[..end];

            source = &source[end..];

            assert!(!ident.is_empty(), "Invalid state: {}.", source);

            let token = match Keyword::from_ident(ident) {
                Some(keyword) => Token::Keyword(keyword),
                None          => Token::Identifier(ident.to_string()),
            };

            tokens.push(token);
        }

        if false {
            for token in &tokens {
                println!("{:?}", token);
            }
        }

        Lexer {
            tokens,
            cursor: 0,
        }
    }

    fn token(&self, cursor: isize) -> &Token {
        const EOF: Token = Token::Eof;

        if cursor < 0 || cursor as usize >= self.tokens.len() {
            return &EOF;
        }

        &self.tokens[cursor as usize]
    }

    pub fn eat(&mut self) -> &Token {
        let cursor = self.cursor;

        self.cursor += 1;

        self.token(cursor)
    }

    pub fn restore(&mut self, count: usize) {
        assert!(count > 0);

        self.cursor -= count as isize;
    }

    pub fn current(&self) -> &Token {
        self.token(self.cursor)
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
