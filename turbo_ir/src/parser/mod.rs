// Workaround for clippy bug.
#![allow(clippy::unnecessary_wraps)]

mod lexer;

use lexer::{Lexer, Token, Keyword};
use crate::{Value, Label, Type, LargeKeyMap, Module, Instruction, IntPredicate,
            BinaryOp, Map, Function, UnaryOp, Cast};

impl Keyword {
    fn to_type(&self) -> Option<Type> {
        Some(match self {
            Keyword::U1  => Type::U1,
            Keyword::U8  => Type::U8,
            Keyword::U16 => Type::U16,
            Keyword::U32 => Type::U32,
            Keyword::U64 => Type::U64,
            _            => return None,
        })
    }

    fn to_unary_operator(&self) -> Option<UnaryOp> {
        Some(match self {
            Keyword::Neg  => UnaryOp::Neg,
            Keyword::Not  => UnaryOp::Not,
            _             => return None,
        })
    }

    fn to_binary_operator(&self) -> Option<BinaryOp> {
        Some(match self {
            Keyword::Add  => BinaryOp::Add,
            Keyword::Sub  => BinaryOp::Sub,
            Keyword::Mul  => BinaryOp::Mul,
            Keyword::Umod => BinaryOp::ModU,
            Keyword::Udiv => BinaryOp::DivU,
            Keyword::Smod => BinaryOp::ModS,
            Keyword::Sdiv => BinaryOp::DivS,
            Keyword::Shr  => BinaryOp::Shr,
            Keyword::Shl  => BinaryOp::Shl,
            Keyword::Sar  => BinaryOp::Sar,
            Keyword::And  => BinaryOp::And,
            Keyword::Or   => BinaryOp::Or,
            Keyword::Xor  => BinaryOp::Xor,
            _             => return None,
        })
    }

    fn to_int_predicate(&self) -> Option<IntPredicate> {
        Some(match self {
            Keyword::Eq   => IntPredicate::Equal,
            Keyword::Ne   => IntPredicate::NotEqual,
            Keyword::Ugt  => IntPredicate::GtU,
            Keyword::Ugte => IntPredicate::GteU,
            Keyword::Sgt  => IntPredicate::GtS,
            Keyword::Sgte => IntPredicate::GteS,
            _             => return None,
        })
    }

    fn to_cast(&self) -> Option<Cast> {
        Some(match self {
            Keyword::Zext    => Cast::ZeroExtend,
            Keyword::Sext    => Cast::SignExtend,
            Keyword::Trunc   => Cast::Truncate,
            Keyword::Bitcast => Cast::Bitcast,
            _                => return None,
        })
    }
}

#[derive(Default)]
struct FunctionContext {
    values: LargeKeyMap<String, Value>,
    labels: LargeKeyMap<String, Label>,
    types:  Map<Value, Type>,
}

impl FunctionContext {
    fn label(&mut self, label_name: &str, ir: &mut Module) -> Label {
        if let Some(label) = self.labels.get(label_name) {
            return *label;
        }

        let label = ir.create_label();

        self.labels.insert(label_name.to_string(), label);

        label
    }

    fn value(&mut self, value_name: &str, ir: &mut Module) -> Value {
        if let Some(value) = self.values.get(value_name) {
            return *value;
        }

        let value = ir.function_mut(ir.active_point().function).allocate_value();

        self.values.insert(value_name.to_string(), value);

        value
    }

    fn switch_label(&mut self, label_name: &str, ir: &mut Module) {
        let label = if self.labels.is_empty() {
            let label = ir.entry_label();

            self.labels.insert(label_name.to_string(), label);

            label
        } else {
            self.label(label_name, ir)
        };

        ir.switch_label(label);
    }

    fn force_type(&mut self, value: Value, ty: Type) {
        if let Some(before) = self.types.insert(value, ty) {
            assert_eq!(before, ty, "{} type mistmatch ({} vs {}).", value, before, ty);
        }
    }
}

struct Parser {
    lexer:             Lexer,
    functions:         LargeKeyMap<String, Function>,
    function_contexts: Map<Function, FunctionContext>,
    function_cursors:  Map<Function, usize>,
}

impl Parser {
    fn new(source: &str) -> Self {
        Self {
            lexer:             Lexer::new(source),
            functions:         LargeKeyMap::default(),
            function_contexts: Map::default(),
            function_cursors:  Map::default(),
        }
    }

    fn comma(&mut self) {
        self.lexer.eat_expect(&Token::Comma);
    }

    fn parse_argument_list(&mut self, open: Token, close: Token,
                           mut callback: impl FnMut(&mut Self)) {
        self.lexer.eat_expect(&open);

        loop {
            if self.lexer.current() == &close {
                self.lexer.eat();
                break;
            }

            callback(self);

            let current = self.lexer.current();

            if current == &Token::Comma {
                self.lexer.eat();
            } else {
                assert_eq!(current, &close, "Expected comma or closing paren \
                           in argument list. Got {:?}.", current);
            }
        }
    }

    fn parse_type_keyword(&mut self, keyword: Keyword) -> Type {
        let mut ty = keyword.to_type().expect("Expected type keyword.");

        loop {
            if self.lexer.current() != &Token::Star {
                break;
            }

            ty = ty.ptr();

            self.lexer.eat();
        }

        ty
    }

    fn parse_type(&mut self) -> Type {
        let keyword = self.lexer.eat_keyword();

        self.parse_type_keyword(keyword)
    }

    fn parse_return_type(&mut self) -> Option<Type> {
        if self.lexer.current() == &Token::Keyword(Keyword::Void) {
            self.lexer.eat();

            return None;
        }

        Some(self.parse_type())
    }

    fn parse_label(&mut self, cx: &mut FunctionContext, ir: &mut Module) -> Label {
        cx.label(self.lexer.eat_identifier(), ir)
    }

    fn parse_value(&mut self, ty: Type, cx: &mut FunctionContext, ir: &mut Module) -> Value {
        let value = match self.lexer.current() {
            Token::Keyword(Keyword::Undefined) => {
                self.lexer.eat();

                ir.function_mut(ir.active_point().function).undefined_value(ty)
            }
            Token::Identifier(_) => {
                if let Token::Identifier(identifier) = self.lexer.eat() {
                    cx.value(identifier, ir)
                } else {
                    unreachable!()
                }
            }
            Token::Keyword(Keyword::Null)  |
            Token::Keyword(Keyword::True)  |
            Token::Keyword(Keyword::False) |
            Token::Literal(..) => {
                let constant = self.parse_constant(ty);

                ir.iconst(constant, ty)
            }
            x => panic!("Unexpected token when parsing value: {:?}.", x),
        };

        cx.force_type(value, ty);

        value
    }

    fn parse_constant(&mut self, ty: Type) -> u64 {
        match self.lexer.eat() {
            &Token::Keyword(keyword) => {
                match keyword {
                    Keyword::True | Keyword::False => {
                        assert_eq!(ty, Type::U1, "true/false constants can be only used for U1.");

                        (keyword == Keyword::True) as u64
                    }
                    Keyword::Null => {
                        assert!(ty.is_pointer(), "null constant can be only used for pointers.");

                        0
                    }
                    _ => panic!("Invalid constant keyword {:?}.", keyword),
                }
            }
            Token::Literal(literal) => {
                let literal = *literal;

                macro_rules! fits_within {
                    ($value: expr, $type: ty) => {
                        $value as i64 <= <$type>::MAX as i64 &&
                            $value as i64 >= <$type>::MIN as i64
                    }
                }

                let fits = match ty {
                    Type::U1  => literal == 0 || literal == 1,
                    Type::U8  => fits_within!(literal, i8),
                    Type::U16 => fits_within!(literal, i16),
                    Type::U32 => fits_within!(literal, i32),
                    _         => fits_within!(literal, i64),
                };

                assert!(fits, "Literal {} doesn't fit in {}.", literal, ty);

                literal as u64
            }
            x => panic!("Unexpected token when parsing constant: {:?}.", x),
        }
    }

    fn parse_call(&mut self, destination: Option<Value>, cx: &mut FunctionContext,
                  ir: &mut Module) -> Instruction {
        let return_ty = self.parse_return_type();
        let name      = self.lexer.eat_identifier();
        let function  = self.functions[name];

        assert_eq!(destination.is_some(), return_ty.is_some(), "Call return type mismatch.");

        if let Some(destination) = destination {
            cx.force_type(destination, return_ty.unwrap());
        }

        let mut arguments = Vec::new();

        self.parse_argument_list(Token::ParenOpen, Token::ParenClose, |parser| {
            let argument_ty = parser.parse_type();
            let argument    = parser.parse_value(argument_ty, cx, ir);

            arguments.push(argument);
        });

        Instruction::Call {
            dst:  destination,
            func: function,
            args: arguments,
        }
    }

    fn parse_non_returning_instruction(&mut self, keyword: Keyword, cx: &mut FunctionContext,
                                       ir: &mut Module) -> Instruction {
        macro_rules! value {
            ($type: expr) => { self.parse_value($type, cx, ir) }
        }

        macro_rules! label {
            () => { self.parse_label(cx, ir) }
        }

        match keyword {
            Keyword::Store => {
                let ptr_ty = self.parse_type();
                let ptr    = value!(ptr_ty);

                self.comma();

                let value_ty = self.parse_type();
                let value    = value!(value_ty);

                Instruction::Store {
                    ptr,
                    value,
                }
            }
            Keyword::Branch => {
                let target = label!();

                Instruction::Branch {
                    target,
                }
            }
            Keyword::Bcond => {
                let cond_ty = self.parse_type();
                let cond    = value!(cond_ty);

                self.comma();

                let on_true = label!();

                self.comma();

                let on_false = label!();

                Instruction::BranchCond {
                    cond,
                    on_true,
                    on_false,
                }
            }
            Keyword::Ret => {
                let value = self.parse_return_type().map(|ty| value!(ty));

                Instruction::Return {
                    value,
                }
            }
            Keyword::Call => self.parse_call(None, cx, ir),
            Keyword::Nop  => Instruction::Nop,
            _ => panic!("Unexpected keyword for non-returning instruction: {:?}.", keyword),
        }
    }

    fn parse_returning_instruction(&mut self, keyword: Keyword, output: String,
                                   cx: &mut FunctionContext, ir: &mut Module) -> Instruction {
        macro_rules! value {
            ($type: expr) => { self.parse_value($type, cx, ir) }
        }

        let dst = cx.value(&output, ir);

        if let Some(op) = keyword.to_unary_operator() {
            let ty    = self.parse_type();
            let value = value!(ty);

            return Instruction::ArithmeticUnary {
                dst,
                op,
                value,
            };
        }

        if let Some(op) = keyword.to_binary_operator() {
            let ty = self.parse_type();

            let a = value!(ty);

            self.comma();

            let b = value!(ty);

            return Instruction::ArithmeticBinary {
                dst,
                a,
                op,
                b,
            };
        }

        if let Some(cast) = keyword.to_cast() {
            let value_ty = self.parse_type();
            let value    = value!(value_ty);

            self.lexer.eat_expect(&Token::Keyword(Keyword::To));

            let dest_ty = self.parse_type();

            return Instruction::Cast {
                dst,
                cast,
                value,
                ty: dest_ty,
            };
        }

        match keyword {
            Keyword::Icmp => {
                let pred = self.lexer.eat_keyword()
                    .to_int_predicate()
                    .expect("Expected int predicate.");

                let ty = self.parse_type();

                let a = value!(ty);

                self.comma();

                let b = value!(ty);

                Instruction::IntCompare {
                    dst,
                    a,
                    pred,
                    b,
                }
            }
            Keyword::Load => {
                let dst_ty = self.parse_type();

                self.comma();

                let ptr_ty = self.parse_type();
                let ptr    = value!(ptr_ty);

                cx.force_type(dst, dst_ty);

                Instruction::Load {
                    dst,
                    ptr,
                }
            }
            Keyword::Stackalloc => {
                let ty       = self.parse_type();
                let mut size = 1;

                if self.lexer.current() == &Token::Comma {
                    self.lexer.eat();

                    size = self.parse_constant(Type::U64) as usize;
                }

                Instruction::StackAlloc {
                    dst,
                    ty,
                    size,
                }
            }
            Keyword::Gep => {
                let source_ty = self.parse_type();
                let source    = value!(source_ty);

                self.comma();

                let index_ty = self.parse_type();
                let index    = value!(index_ty);

                Instruction::GetElementPtr {
                    dst,
                    index,
                    source,
                }
            }
            Keyword::Select => {
                let cond_ty = self.parse_type();
                let cond    = value!(cond_ty);

                self.comma();

                let value_ty = self.parse_type();

                let on_true = value!(value_ty);

                self.comma();

                let on_false = value!(value_ty);

                Instruction::Select {
                    dst,
                    cond,
                    on_true,
                    on_false,
                }
            }
            Keyword::Phi => {
                let ty           = self.parse_type();
                let mut incoming = Vec::new();

                self.parse_argument_list(Token::BracketOpen, Token::BracketClose, |parser| {
                    let label = parser.parse_label(cx, ir);

                    parser.lexer.eat_expect(&Token::Colon);

                    let value = parser.parse_value(ty, cx, ir);

                    incoming.push((label, value));
                });

                Instruction::Phi {
                    dst,
                    incoming,
                }
            }
            Keyword::Alias => {
                let value_ty = self.parse_type();
                let value    = value!(value_ty);

                Instruction::Alias {
                    dst,
                    value,
                }
            }
            Keyword::Call => {
                self.parse_call(Some(dst), cx, ir)
            }
            _ => panic!("Unexpected keyword for returning instruction: {:?}.", keyword),
        }
    }

    fn parse_function_body(&mut self, cx: &mut FunctionContext, ir: &mut Module) {
        self.lexer.eat_expect(&Token::BraceOpen);

        let mut has_label = false;

        while self.lexer.current() != &Token::BraceClose {
            let mut instruction = None;

            match self.lexer.eat() {
                &Token::Keyword(keyword) => {
                    assert!(has_label, "Instruction isn't part of any block.");

                    instruction = Some(self.parse_non_returning_instruction(keyword, cx, ir));
                }
                Token::Identifier(identifier) => {
                    let identifier = identifier.to_string();

                    match self.lexer.eat() {
                        Token::Assign => {
                            assert!(has_label, "Instruction isn't part of any block.");

                            let keyword = self.lexer.eat_keyword();

                            instruction = Some(self.parse_returning_instruction(keyword,
                                                                                identifier,
                                                                                cx, ir));
                        }
                        Token::Colon => {
                            cx.switch_label(&identifier, ir);

                            has_label = true;
                        }
                        x => panic!("Unexpected token after identifier \
                                     in function body: {:?}.", x),
                    }
                }
                x => panic!("Unexpected token in function body: {:?}.", x),
            }

            if let Some(instruction) = instruction {
                let active_point = ir.active_point();

                ir.function_mut(active_point.function)
                    .insert(active_point.label, instruction);
            }
        }

        self.lexer.eat_expect(&Token::BraceClose);
    }

    fn parse_function_prototype(&mut self, ir: &mut Module) {
        let return_ty = self.parse_return_type();
        let name      = self.lexer.eat_identifier().to_string();

        let mut arguments = Vec::new();

        self.parse_argument_list(Token::ParenOpen, Token::ParenClose, |parser| {
            let ty       = parser.parse_type();
            let argument = parser.lexer.eat_identifier().to_string();

            arguments.push((ty, argument));
        });

        let argument_types: Vec<_> = arguments.iter()
            .map(|(ty, _)| *ty)
            .collect();

        let function = ir.create_function(&name, return_ty, argument_types);
        let cursor   = self.lexer.cursor();

        ir.switch_function(function);

        let mut cx = FunctionContext::default();

        for (index, (_, argument_name)) in arguments.into_iter().enumerate() {
            cx.values.insert(argument_name, ir.argument(index));
        }

        self.lexer.eat_expect(&Token::BraceOpen);

        while self.lexer.eat() != &Token::BraceClose {}

        assert!(self.functions.insert(name.to_string(), function).is_none(),
                "Multiple functions with the same name ({}).", name);

        assert!(self.function_contexts.insert(function, cx).is_none(),
                "Function {} already has context.", name);

        assert!(self.function_cursors.insert(function, cursor).is_none(),
                "Function {} already has cursor.", name);
    }

    fn parse_functions(&mut self, ir: &mut Module) {
        while self.lexer.current() != &Token::Eof {
            self.parse_function_prototype(ir);
        }

        let cursors = std::mem::take(&mut self.function_cursors);

        for (function, cursor) in cursors {
            let mut cx = self.function_contexts.remove(&function)
                .expect("Function doesn't have context for some reason.");

            ir.switch_function(function);
            self.lexer.set_cursor(cursor);
            self.parse_function_body(&mut cx, ir);

            assert!(self.function_contexts.insert(function, cx).is_none(),
                    "Context already exists.");
        }
    }
}

pub fn parse(source: &str) -> Module {
    let mut parser = Parser::new(source);
    let mut ir     = Module::new();

    parser.parse_functions(&mut ir);

    ir.finalize();

    for (&function, cx) in &parser.function_contexts {
        let function_data = ir.function(function);

        for (value, ty) in &cx.types {
            let actual = function_data.value_type(*value);

            assert_eq!(actual, *ty, "{}: {} type mistmatch (user {} vs infered {}).",
                       function_data.prototype.name, value, ty, actual);
        }
    }

    ir
}
