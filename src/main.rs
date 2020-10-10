mod lexer;

fn main() {
    let source = std::fs::read_to_string("test/1.tc").unwrap();

    lexer::Lexer::lex(&source);
}
