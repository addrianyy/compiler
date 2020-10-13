mod parser;
mod compiler;
mod ir;

fn main() {
    let source       = std::fs::read_to_string("test/1.tc").unwrap();
    let parsed       = parser::parse(&source);
    let mut compiled = compiler::compile(&parsed);

    compiled.ir.optimize();

    for (_, function) in &compiled.functions {
        compiled.ir.dump_function_text(*function, &mut std::io::stdout()).unwrap();
    }

    let mcode = compiled.ir.generate_machine_code();
    
    for (prototype, function) in &compiled.functions {
        let buffer = mcode.function_buffer(*function);
        let name   = &prototype.name;

        std::fs::write(format!("mcode/{}.bin", name), buffer).unwrap();

        if name == "main" {
            let mut buffer = [1u8, 2u8, 3u8, 0u8];
            
            type Func = extern "win64" fn(*mut u8) -> i32;

            let result = unsafe {
                let func = mcode.function_ptr::<Func>(*function);

                func(buffer.as_mut_ptr())
            };

            println!("return value: {}. buffer: {:?}", result, buffer);
        }
    }


    /*
    let mut ir = ir::Module::new();

    let func = ir.create_function("abc123", None, vec![]);
    ir.switch_function(func);


    let a    = ir.iconst(999u32, ir::Type::U64);
    let b    = ir.iconst(1324u32, ir::Type::U64);
    let c    = ir.arithmetic_binary(b, ir::BinaryOp::Add, a);
    let d    = ir.arithmetic_unary(ir::UnaryOp::Neg, c);
    ir.ret(None);

    ir.finalize();

    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();

    let mcode = ir.generate_machine_code();
    
    std::fs::write("mcode/test.bin", mcode.function_buffer(func)).unwrap();
    */



    /*
    let c    = ir.iconst(999u32, ir::Type::U64);
    let x    = ir.iconst(1324u32, ir::Type::U64);
    let d    = ir.arithmetic_binary(c, ir::BinaryOp::Add, x);
    ir.ret(Some(d));

    ir.finalize();
    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    ir.test();
    */

    /*
    let mut module = ir::Module::new();

    let func = module.create_function("abc123", Some(ir::Type::U16),
                                      vec![ir::Type::U64.ptr(); 3]);

    module.switch_function(func);

    let arg1 = module.argument(0);
    let arg2 = module.argument(1);
    let arg3 = module.argument(2);
    let v1   = module.load(arg1);
    let v2   = module.load(arg2);
    let c    = module.iconst(999u32, ir::Type::U64);
    let v1   = module.arithmetic_binary(v1, ir::BinaryOp::Xor, c);
    let res  = module.int_compare(v1, ir::IntPredicate::GtS, v2);
    let x    = module.get_element_ptr(arg2, v1);

    let true_label  = module.create_label();
    let false_label = module.create_label();
    let merge_label = module.create_label();

    module.branch_cond(res, true_label, false_label);

    {
        module.switch_label(true_label);

        let c = module.iconst(12u32, ir::Type::U64);
        let d = module.iconst(55u64, ir::Type::U64);
        let lol = module.select(res, c, d);
        module.store(arg3, c);
        module.branch(merge_label);
    }

    {
        module.switch_label(false_label);

        let c = module.iconst(19u32, ir::Type::U64);
        module.store(arg3, c);
        module.branch(merge_label);
    }

    module.switch_label(merge_label);
    let c = module.iconst(1337u32, ir::Type::U16);
    let x = module.cast(c, ir::Type::U32, ir::Cast::ZeroExtend);
    let d = module.cast(x, ir::Type::U8, ir::Cast::Truncate);
    let d = module.iconst(1337u32, ir::Type::U64);
    let u = module.cast(d, ir::Type::U64.ptr().ptr(), ir::Cast::Bitcast);
    module.ret(Some(c));

    module.finalize();

    module.dump_function_graph(func, "graphs/test.svg");
    module.dump_function_text(func, &mut std::io::stdout());
    */
}
