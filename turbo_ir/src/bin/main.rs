use turbo_ir as ir;

use ir::passes::IRPass;

use std::io;
use std::collections::HashSet;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct PassID(usize);

struct PassRegistry {
    passes: Vec<(&'static str, IRPass)>,
}

impl PassRegistry {
    fn new() -> Self {
        let passes = vec![
            ("remove-ineff",  ir::passes::remove_ineffective_operations()),
            ("expr-simplify", ir::passes::simplify_expressions()),
            ("dse",           ir::passes::remove_dead_stores()),
            ("rle",           ir::passes::remove_known_loads()),
            ("cmp-simplify",  ir::passes::simplify_compares()),
            ("select",        ir::passes::branch_to_select()),
            ("dce",           ir::passes::remove_dead_code()),
            ("constprop",     ir::passes::const_propagate()),
            ("mem2ssa",       ir::passes::memory_to_ssa()),
            ("cfg-simplify",  ir::passes::simplify_cfg()),
            ("dedup",         ir::passes::deduplicate()),
            ("reorder",       ir::passes::reorder()),
            ("x86reorder",    ir::passes::x86reorder()),
        ];

        Self { passes }
    }

    fn pass_by_name(&self, pass_name: &str) -> Option<PassID> {
        for (index, (name, _)) in self.passes.iter().enumerate() {
            if *name == pass_name {
                return Some(PassID(index));
            }
        }

        None
    }

    fn all_passes(&self) -> Vec<PassID> {
        (0..self.passes.len())
            .map(|id| PassID(id))
            .collect()
    }

    fn pass(&self, pass_id: PassID) -> IRPass {
        self.passes[pass_id.0].1
    }
}

enum Request {
    Add,
    Remove,
}

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args()
        .skip(1)
        .collect();

    if let Some(source_path) = args.get(0) {
        let source     = std::fs::read_to_string(source_path)?;
        let mut module = ir::Module::parse_from_source(&source);
        let registry   = PassRegistry::new();

        let mut passes: HashSet<PassID> = HashSet::new();

        for argument in &args[1..] {
            let request = if argument.starts_with("+") {
                Request::Add
            } else if argument.starts_with("-") {
                Request::Remove
            } else {
                println!("Unknown argument: {}.", argument);
                std::process::exit(-1);
            };

            match &argument[1..] {
                "all" => {
                    for pass in registry.all_passes() {
                        match request {
                            Request::Add    => passes.insert(pass),
                            Request::Remove => passes.remove(&pass),
                        };
                    }
                }
                name => {
                    let pass = registry.pass_by_name(name).unwrap_or_else(|| {
                        println!("Unrecognised IR pass: {}.", name);
                        std::process::exit(-1);
                    });

                    match request {
                        Request::Add    => passes.insert(pass),
                        Request::Remove => passes.remove(&pass),
                    };
                }
            }
        }

        let passes: Vec<IRPass> = passes.into_iter()
            .map(|pass| registry.pass(pass))
            .collect();

        module.optimize(&passes, false);

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
