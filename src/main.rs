mod parser;
mod compiler;
mod ir;
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
