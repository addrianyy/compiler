use std::io;

use turbo_ir as ir;

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args()
        .skip(1)
        .collect();

    if let Some(source_path) = args.get(0) {
        let source = std::fs::read_to_string(source_path)?;
        let module = ir::Module::parse_from_source(&source);

        module.for_each_local_function(|_prototype, function| {
            module.dump_function_text(function, &mut io::stdout())
                .expect("Writing to stdout failed.");

            println!();
        });
    } else {
        println!("No TurboIR source file provided.");
    }

    Ok(())
}
