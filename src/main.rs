mod lexer;
mod parser;

fn main() {
    let source = std::fs::read_to_string("test/1.tc").unwrap();
    let module = parser::parse(&source);

    module.print(&mut std::io::stdout()).unwrap();
}
