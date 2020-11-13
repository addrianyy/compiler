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

    let passes = &[
        turbo_ir::passes::const_propagate(),
        turbo_ir::passes::remove_ineffective_operations(),
        turbo_ir::passes::simplify_cfg(),
        turbo_ir::passes::simplify_compares(),
        turbo_ir::passes::simplify_expressions(),
        turbo_ir::passes::remove_dead_code(),
        turbo_ir::passes::memory_to_ssa(),
        turbo_ir::passes::deduplicate_precise(),
        turbo_ir::passes::remove_known_loads_precise(),
        turbo_ir::passes::remove_dead_stores_precise(),
        turbo_ir::passes::undefined_propagate(),
        turbo_ir::passes::minimize_phis(),
        turbo_ir::passes::branch_to_select(),
        turbo_ir::passes::reorder(),
        turbo_ir::passes::x86reorder(),
    ];

    compiled.ir.optimize(passes, false);

    recreate_directory("mcode");
    recreate_directory("graphs");

    for (prototype, function) in &compiled.functions {
        let name = &prototype.name;

        compiled.ir.dump_function_text_stdout(*function);
        compiled.ir.dump_function_graph(*function, &format!("graphs/{}.svg", name));

        println!();
    }

    let mcode = compiled.ir.generate_machine_code(&turbo_ir::backends::X86Backend);

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

        if name == "sum" {
            type Func = extern "win64" fn(i32) -> i32;

            let result = unsafe {
                let func = mcode.function_ptr::<Func>(*function);

                func(5)
            };

            println!("return value: {}.", result);
        }
    }

    /*
    use turbo_ir as ir;
    let mut ir = ir::Module::new();

    let func = ir.create_function("test", Some(ir::Type::U32), vec![ir::Type::U16]);

    ir.switch_function(func);
    let arg = ir.argument(0);

    let x = ir.zero_extend(arg, ir::Type::U64);
    let y = ir.truncate(x, ir::Type::U32);

    ir.ret(Some(y));


    ir.finalize();
    ir.optimize();
    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    */

        /*
    use turbo_ir as ir;
    let mut ir = ir::Module::new();

    let func = ir.create_function("test", None, vec![ir::Type::U32.ptr()]);

    ir.switch_function(func);
    let arg = ir.argument(0);

    let x = ir.create_label();
    let y = ir.create_label();
    let z = ir.create_label();
    let w = ir.create_label();
    ir.branch(x);

    ir.switch_label(x);

    let loaded = ir.load(arg);

    let val    = ir.iconst(123u32, ir::Type::U32);
    let cond =  ir.compare_ne(loaded, val);
    ir.store(arg, val);
    ir.branch_cond(cond, z, y);


    ir.switch_label(z);
    let one    = ir.iconst(1u32, ir::Type::U32);
    let added  = ir.add(loaded, one);
    ir.store(arg, added);
    ir.branch(w);
    ir.switch_label(w);
    ir.branch(x);


    ir.switch_label(y);
    let val    = ir.iconst(888u32, ir::Type::U32);
    ir.store(arg, val);
    ir.ret(None);


    ir.finalize();
    ir.optimize();
    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    */

        /*
    use turbo_ir as ir;
    let mut ir = ir::Module::new();

    let func = ir.create_function("test", Some(ir::Type::U32), vec![ir::Type::U32]);

    ir.switch_function(func);
    */


        /*
    use turbo_ir as ir;
    let mut ir = ir::Module::new();

    let func = ir.create_function("test", None, vec![ir::Type::U1]);
    ir.switch_function(func);

    let x = ir.create_label();
    let y = ir.create_label();

    let cond = ir.argument(0);

    ir.branch(x);
    ir.switch_label(x);
    ir.branch(y);

    ir.switch_label(y);
    ir.branch_cond(cond, x, y);


    ir.finalize();
    ir.optimize();
    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    */

    /*
    let entry     = ir.entry_label();
    let body      = ir.create_label();
    let body_tmp  = ir.create_label();
    let exit      = ir.create_label();

    let count = ir.argument(0);
    let zero  = ir.iconst(0u32, ir::Type::U32);

    ir.branch(body);
    ir.switch_label(body);
    let iter      = ir.phi();
    let sum       = ir.phi();
    let next_sum  = ir.add(sum, iter);
    let one       = ir.iconst(1u32, ir::Type::U32);
    let next_iter = ir.add(iter, one);
    let five      = count; //ir.iconst(8u32, ir::Type::U32);
    let cond      = ir.compare_ne(next_iter, five);
    ir.branch_cond(cond, body_tmp, exit);

    ir.switch_label(body_tmp);
    ir.branch(body);

    ir.add_phi_incoming(iter, entry, zero);
    ir.add_phi_incoming(iter, body_tmp,  next_iter);

    ir.add_phi_incoming(sum, entry, zero);
    ir.add_phi_incoming(sum, body_tmp,  next_sum);

    ir.switch_label(exit);
    ir.ret(Some(next_sum));
    */

    /*
    let body = ir.create_label();
    let exit = ir.create_label();

    let iter = ir.stack_alloc(ir::Type::U32, 1);
    let sum  = ir.stack_alloc(ir::Type::U32, 1);

    let zero  = ir.iconst(0u32, ir::Type::U32);
    let one   = ir.iconst(1u32, ir::Type::U32);
    let count = ir.argument(0);

    ir.store(iter, zero);
    ir.store(sum,  zero);

    ir.branch(body);
    ir.switch_label(body);

    let citer = ir.load(iter);
    let csum  = ir.load(sum);

    let next_iter = ir.add(citer, one);
    let next_sum  = ir.add(csum, citer);

    ir.store(iter, next_iter);
    ir.store(sum,  next_sum);

    let cond = ir.compare_ne(next_iter, count);
    ir.branch_cond(cond, body, exit);

    ir.switch_label(exit);

    let result = ir.load(sum);
    ir.ret(Some(result));


    ir.finalize();
    ir.optimize();
    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    ir.dump_function_graph(func, "graphs/test.svg");

    println!();


    let mcode = ir.generate_machine_code();
    let buffer = mcode.function_buffer(func);
    std::fs::write("asm_dump.bin", buffer).unwrap();

    {
        type Func = extern "win64" fn(i32) -> i32;

        println!("Executing");

        let result = unsafe {
            let func = mcode.function_ptr::<Func>(func);

            func(5)
        };

        println!("return value: {}.", result);
    }
    */

    /*
    use turbo_ir as ir;
    let mut ir = ir::Module::new();
    let func = ir.create_function("test", Some(ir::Type::U32), vec![ir::Type::U32]);

    ir.switch_function(func);

    let entry  = ir.entry_label();
    let truel  = ir.create_label();
    let falsel = ir.create_label();
    let exit   = ir.create_label();

    let cond = ir.iconst(1u8, ir::Type::U1);
    ir.branch_cond(cond, truel, falsel);

    ir.switch_label(truel);
    let truev = ir.iconst(33u32, ir::Type::U32);
    ir.branch(exit);

    ir.switch_label(falsel);
    let falsev = ir.iconst(88u32, ir::Type::U32);
    ir.branch(exit);

    ir.switch_label(exit);
    let ret = ir.phi();
    ir.add_phi_incoming(ret, truel, truev);
    ir.add_phi_incoming(ret, falsel, falsev);
    ir.ret(Some(ret));

    ir.finalize();
    ir.optimize();
    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    */





    /*
    use turbo_ir as ir;

    let mut ir = ir::Module::new();

    let func = ir.create_function("test", Some(ir::Type::U1), vec![ir::Type::U1.ptr()]);

    ir.switch_function(func);
    */
    /*
    let null = ir.iconst(0u32, ir::Type::U32.ptr());
    let arg1 = ir.argument(1);
    let xd  = ir.compare_eq(arg, null);

    ir.ret(Some(xd));

    ir.finalize();
    ir.optimize();
    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();

    let mcode = ir.generate_machine_code();
    let buffer = mcode.function_buffer(func);
    std::fs::write("asm_dump.bin", buffer).unwrap();
    */

    /*
    let arg  = ir.argument(0);
    let x = ir.iconst(1u32, ir::Type::U1);
    let idx = ir.iconst(2u32, ir::Type::U32);
    let v = ir.get_element_ptr(arg, idx);
    ir.store(v, x);

    let c = ir.iconst(0u32, ir::Type::U1);
    ir.ret(Some(c));

    ir.finalize();
    ir.optimize();
    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();

    let mcode = ir.generate_machine_code();
    let buffer = mcode.function_buffer(func);
    std::fs::write("asm_dump.bin", buffer).unwrap();
    */

    /*
    use turbo_ir as ir;

    let mut ir = ir::Module::new();

    let func = ir.create_function("test", Some(ir::Type::U32), vec![ir::Type::U32,
                                                                    ir::Type::U32.ptr()]);

    ir.switch_function(func);

    let arg0 = ir.argument(0);
    let arg1 = ir.argument(1);

    let v = ir.iconst(123u32, ir::Type::U32);
    let x = ir.iconst(333u32, ir::Type::U32);
    ir.store(arg1, v);

    let la = ir.create_label();
    let lb = ir.create_label();

    let xxx = ir.compare_ne(arg0, x);
    ir.branch_cond(xxx, la, lb);

    {
        ir.switch_label(la);
        ir.store(arg1, x);
        let dd = ir.load(arg1);
        ir.ret(Some(dd));
    }

    {
        ir.switch_label(lb);
        let dd = ir.load(arg1);
        ir.ret(Some(dd));
    }

    ir.finalize();
    ir.optimize();
    ir.dump_function_text(func, &mut std::io::stdout()).unwrap();
    */

    //let cond = it.compare_ne(arg0, x);



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
