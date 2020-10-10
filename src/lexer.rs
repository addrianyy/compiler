#[derive(Clone, Debug)]
pub enum Keyword {
    Function,
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
}

impl Keyword {
    fn from_ident(ident: &str) -> Option<Keyword> {
        let keyword = match ident {
            "fn"    => Keyword::Function,
            "void"  => Keyword::Void,
            "u8"    => Keyword::U8,
            "u16"   => Keyword::U16,
            "u32"   => Keyword::U32,
            "u64"   => Keyword::U64,
            "i8"    => Keyword::I8,
            "i16"   => Keyword::I16,
            "i32"   => Keyword::I32,
            "i64"   => Keyword::I64,
            "for"   => Keyword::For,
            "while" => Keyword::While,
            "if"    => Keyword::If,
            _       => return None,
        };

        Some(keyword)
    }
}

#[derive(Clone, Debug)]
pub enum Token {
    Identifier(String),
    Keyword(Keyword),

    Literal {

    },

    Colon,
    Semicolon,

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
}

pub struct Lexer<'a> {
    source: &'a str,
}

impl<'a> Lexer<'a> {
    pub fn lex(mut source: &'a str) {
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
            ("!",  Token::Not),
            ("=",  Token::Assign),

            ("(",  Token::ParenOpen),
            (")",  Token::ParenClose),
            ("{",  Token::BraceOpen),
            ("}",  Token::BraceClose),
            ("[",  Token::BracketOpen),
            ("]",  Token::BracketClose),

            (":",  Token::Colon),
            (";",  Token::Semicolon),
            (">",  Token::Gt),
            ("<",  Token::Lt),
        ];

        let mut tokens = Vec::new();

        'lex_next: while !source.is_empty() {
            let mut skip = 0;

            for (index, ch) in source.char_indices() {
                if !ch.is_whitespace() {
                    break
                }

                skip = index + ch.len_utf8();
            }

            let skip = source.find(|ch| !ch.is_whitespace()).unwrap_or(source.len());

            source = &source[skip..];

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

            if source.chars().next().unwrap().is_numeric() {
                panic!()
            }

            let end   = source.find(|c: char| c.is_whitespace()).unwrap_or(source.len());
            let ident = &source[..end];

            source = &source[end..];

            let token = match Keyword::from_ident(ident) {
                Some(keyword) => Token::Keyword(keyword),
                None          => Token::Identifier(ident.to_string()),
            };

            tokens.push(token);
        }
    }
}

