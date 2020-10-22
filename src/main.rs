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
}
