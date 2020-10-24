mod parser;
mod compiler;
mod runtimelib;

fn recreate_directory(path: &str) {
    let _ = std::fs::remove_dir_all(path);

    std::fs::create_dir_all(path).unwrap_or_else(|err| {
        panic!("Failed to recreate {}. {:?}", path, err);
    });
}

fn main() {
    let source       = std::fs::read_to_string("test/1.tc").unwrap();
    let parsed       = parser::parse(&source);
    let mut compiled = compiler::compile(&parsed);

    compiled.ir.optimize();

    recreate_directory("mcode");
    recreate_directory("graphs");

    for (prototype, function) in &compiled.functions {
        let name = &prototype.name;

        compiled.ir.dump_function_text(*function, &mut std::io::stdout()).unwrap();
        compiled.ir.dump_function_graph(*function, &format!("graphs/{}.svg", name));

        println!();
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
    use turbo_ir as ir;

    let mut ir = ir::Module::new();

    let func = ir.create_function("test", Some(ir::Type::U32), vec![ir::Type::U32]);

    ir.switch_function(func);

    let arg = ir.argument(0);

    let arg = ir.argument(0);
    let a   = ir.iconst(1u32, ir::Type::U32);
    let b   = ir.iconst(0u32, ir::Type::U32);
    let c   = ir.iconst(2u32, ir::Type::U32);

    let la = ir.create_label();
    let lb = ir.create_label();
    let ex = ir.create_label();

    let cond = ir.compare_eq(arg, c);
    ir.branch_cond(cond, la, lb);

    ir.switch_label(la);
    ir.branch(ex);

    ir.switch_label(lb);
    ir.branch(ex);

    ir.switch_label(ex);
    ir.ret(Some(c));


    ir.finalize();
    ir.optimize();

    /*
    let mcode  = ir.generate_machine_code();
    let buffer = mcode.function_buffer(func);

    std::fs::write("asm_dump.bin", buffer).unwrap();
    */

    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    */

    /*
    let mut ir = ir::Module::new();

    let func = ir.create_function("test", Some(ir::Type::U64), vec![ir::Type::U16]);
    ir.switch_function(func);

    let arg  = ir.argument(0);

    /*
    let zero = ir.iconst(0u32, ir::Type::U16);
    let ones = ir.iconst(u16::MAX, ir::Type::U16);
    let two  = ir.iconst(2u32, ir::Type::U16);
    */

    let x = ir.zero_extend(arg, ir::Type::U32);
    let x = ir.zero_extend(x, ir::Type::U64);
    ir.ret(Some(x));

    ir.finalize();
    ir.optimize();


    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    */

    /*
    let mut ir = ir::Module::new();

    let func = ir.create_function("test", Some(ir::Type::U16), vec![ir::Type::U16]);
    ir.switch_function(func);

    let arg  = ir.argument(0);
    let zero = ir.iconst(0u32, ir::Type::U16);

    let x = ir.iconst(12u32, ir::Type::U16);
    let y = ir.iconst(33u32, ir::Type::U16);

    let result = ir.compare_eq(arg, zero);
    let result = ir.select(result, x, y);
    let result = ir.compare_eq(result, y);

    {
        let a = ir.iconst(1337u32, ir::Type::U16);
        let b = ir.iconst(420u32, ir::Type::U16);
        let end = ir.select(result, a, b);
        ir.ret(Some(end));
    }

    ir.finalize();
    ir.optimize();


    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    */

    /*
    let mut ir = ir::Module::new();

    let func = ir.create_function("test", Some(ir::Type::U16), Vec::new());
    ir.switch_function(func);

    /*
    let a = ir.iconst(255u64, ir::Type::U8);
    let b = ir.iconst(255u64, ir::Type::U8);

    let value = ir.arithmetic_binary(a, ir::BinaryOp::Add, b);
    let value = ir.arithmetic_unary(ir::UnaryOp::Not, value);
    */


    let x = ir.iconst(15u8, ir::Type::U8);
    let y = ir.iconst(112u8, ir::Type::U8);
    let d = ir.iconst(88u8, ir::Type::U8);

    let a = ir.iconst(123u8, ir::Type::U8);
    let a = ir.arithmetic_binary(a, ir::BinaryOp::Add, d);
    let b = ir.iconst(223u8, ir::Type::U8);


    let r = ir.int_compare(a, ir::IntPredicate::GtU, b);
    /*
    let v = ir.select(r, x, y);
    let value = ir.cast(v, ir::Type::U16, ir::Cast::SignExtend);
    */

    let la = ir.create_label();
    let lb = ir.create_label();

    ir.branch_cond(r, la, lb);

    {
        ir.switch_label(la);
        let x= ir.iconst(1u8, ir::Type::U16);
        ir.ret(Some(x));
    }

    {
        ir.switch_label(lb);
        let x= ir.iconst(0u8, ir::Type::U16);
        ir.ret(Some(x));
    }


    //ir.ret(Some(value));

    ir.finalize();
    ir.optimize();


    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    */
}
