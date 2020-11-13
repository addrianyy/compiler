use std::time::Instant;
use std::fs::File;

use turbo_ir as ir;

extern "win64" fn read_char() -> u8 {
    panic!()
}

extern "win64" fn print_char(ch: u8) {
    print!("{}", ch as char);
}

fn main() {
    let program = std::fs::read_to_string("mandel.bf").unwrap();
    let mut ir  = ir::Module::new();

    let input = unsafe {
        ir.create_external_function("read_char", Some(ir::Type::U8),
                                    vec![], read_char as usize)
    };

    let output = unsafe {
        ir.create_external_function("print_char", None,
                                    vec![ir::Type::U8], print_char as usize)
    };

    let function = ir.create_function("main", None, vec![ir::Type::U8.ptr()]);

    ir.switch_function(function);

    let buffer = ir.argument(0);

    let pos_one_u8  = ir.iconst(1u8,                 ir::Type::U8);
    let neg_one_u8  = ir.iconst(1u8.wrapping_neg(),  ir::Type::U8);
    let pos_one_u64 = ir.iconst(1u64,                ir::Type::U64);
    let neg_one_u64 = ir.iconst(1u64.wrapping_neg(), ir::Type::U64);
    let zero        = ir.iconst(0u8,                 ir::Type::U8);

    let index = {
        let index = ir.stack_alloc(ir::Type::U64, 1);
        let init  = ir.iconst(0u32, ir::Type::U64);

        ir.store(index, init);

        index
    };

    macro_rules! get {
        () => {{
            let index = ir.load(index);
            let ptr   = ir.get_element_ptr(buffer, index);

            ir.load(ptr)
        }}
    }

    macro_rules! set {
        ($value: expr) => {{
            let value = $value;
            let index = ir.load(index);
            let ptr   = ir.get_element_ptr(buffer, index);

            ir.store(ptr, value);
        }}
    }

    let mut loops = Vec::new();

    for ch in program.chars() {
        match ch {
            '>' | '<' => {
                let value = match ch {
                    '>' => pos_one_u64,
                    '<' => neg_one_u64,
                    _   => unreachable!(),
                };

                let i = ir.load(index);
                let i = ir.add(i, value);

                ir.store(index, i);
            }
            '+' | '-' => {
                let value = match ch {
                    '+' => pos_one_u8,
                    '-' => neg_one_u8,
                    _   => unreachable!(),
                };

                let new = get!();
                let new = ir.add(new, value);

                set!(new);
            }
            ',' => {
                let value = ir.call(input, vec![]).unwrap();

                set!(value);
            }
            '.' => {
                let value = get!();

                ir.call(output, vec![value]);
            }
            '[' => {
                let header = ir.create_label();
                let body   = ir.create_label();
                let after  = ir.create_label();

                ir.branch(header);
                ir.switch_label(header);

                let value = get!();
                let cond  = ir.compare_ne(value, zero);

                ir.branch_cond(cond, body, after);
                ir.switch_label(body);

                loops.push((header, after));
            }
            ']' => {
                let (header, after) = loops.pop().unwrap();

                ir.branch(header);
                ir.switch_label(after);
            }
            _ => {},
        }
    }

    assert!(loops.is_empty(), "Unmatched loops.");

    ir.ret(None);
    ir.finalize();

    let passes = &[
        turbo_ir::passes::const_propagate(),
        turbo_ir::passes::remove_ineffective_operations(),
        turbo_ir::passes::simplify_cfg(),
        turbo_ir::passes::simplify_compares(),
        turbo_ir::passes::simplify_expressions(),
        turbo_ir::passes::remove_dead_code(),
        turbo_ir::passes::memory_to_ssa(),
        turbo_ir::passes::deduplicate_fast(),
        //turbo_ir::passes::remove_known_loads_fast(),
        //turbo_ir::passes::remove_dead_stores_fast(),
        turbo_ir::passes::undefined_propagate(),
        turbo_ir::passes::minimize_phis(),
        turbo_ir::passes::branch_to_select(),
        //turbo_ir::passes::reorder(),
        turbo_ir::passes::x86reorder(),
    ];

    println!("Optimizing...");

    ir.optimize(passes, true);
    ir.dump_function_text(function, &mut File::create("result.turboir").unwrap()).unwrap();

    type Func = unsafe extern "win64" fn(*mut u8);

    let machine_code = ir.generate_machine_code(&ir::backends::X86Backend);
    let function_ptr = unsafe {
        machine_code.function_ptr::<Func>(function)
    };

    let mut buffer = vec![0u8; 30 * 1000];

    std::fs::write("asm_dump.bin", machine_code.function_buffer(function)).unwrap();

    println!("Running...");

    let start = Instant::now();

    unsafe {
        function_ptr(buffer.as_mut_ptr());
    }

    let elapsed = start.elapsed().as_secs_f64();

    println!("Executed in {}s.", elapsed);
}
