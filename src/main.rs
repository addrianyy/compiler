mod lexer;
mod parser;

fn main() {
    let source = std::fs::read_to_string("test/1.tc").unwrap();

    let lexer = lexer::Lexer::lex(&source);
    let parser = parser::Parser::new(lexer);
}
