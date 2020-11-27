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
        turbo_ir::passes::optimize_known_bits(),
        turbo_ir::passes::propagate_block_invariants(),
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
}
