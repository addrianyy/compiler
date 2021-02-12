use turbo_ir as ir;

use ir::passes::IRPass;

use std::io;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct PassID(usize);

struct PassRegistry {
    passes: Vec<(&'static str, IRPass)>,
}

impl PassRegistry {
    fn new() -> Self {
        let passes = vec![
            ("opopt",         ir::passes::remove_ineffective_operations()),
            ("expr-simplify", ir::passes::simplify_expressions()),
            ("undefprop",     ir::passes::undefined_propagate()),
            ("dse",           ir::passes::remove_dead_stores_precise()),
            ("rle",           ir::passes::remove_known_loads_precise()),
            ("dse-fast",      ir::passes::remove_dead_stores_fast()),
            ("rle-fast",      ir::passes::remove_known_loads_fast()),
            ("cmp-simplify",  ir::passes::simplify_compares()),
            ("invprop",       ir::passes::propagate_block_invariants()),
            ("select",        ir::passes::branch_to_select()),
            ("dce",           ir::passes::remove_dead_code()),
            ("constprop",     ir::passes::const_propagate()),
            ("mem2ssa",       ir::passes::memory_to_ssa()),
            ("phimin",        ir::passes::minimize_phis()),
            ("cfg-simplify",  ir::passes::simplify_cfg()),
            ("dedup",         ir::passes::deduplicate_precise()),
            ("dedup-fast",    ir::passes::deduplicate_fast()),
            ("bitopt",        ir::passes::optimize_known_bits()),
            ("reorder",       ir::passes::reorder()),
            ("greorder",      ir::passes::global_reorder()),
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
            .map(PassID)
            .collect()
    }

    fn pass(&self, pass_id: PassID) -> IRPass {
        self.passes[pass_id.0].1
    }
}

#[derive(PartialEq, Eq)]
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

        let mut passes: Vec<PassID> = Vec::new();

        macro_rules! remove_pass {
            ($pass: expr) => {{
                if let Some(position) = passes.iter().position(|&pass| pass == $pass) {
                    passes.remove(position);
                }
            }}
        }

        macro_rules! add_pass {
            ($pass: expr) => {{
                if !passes.iter().any(|&pass| pass == $pass) {
                    passes.push($pass);
                }
            }}
        }

        let mut stats = false;

        for argument in &args[1..] {
            let request = if argument.starts_with('+') {
                Request::Add
            } else if argument.starts_with('-') {
                Request::Remove
            } else {
                println!("Unknown argument: {}.", argument);
                std::process::exit(-1);
            };

            match &argument[1..] {
                "all" => {
                    for pass in registry.all_passes() {
                        match request {
                            Request::Add    => add_pass!(pass),
                            Request::Remove => remove_pass!(pass),
                        };
                    }
                }
                name => {
                    if name == "stats" {
                        stats = request == Request::Add;
                    } else {
                        let pass = registry.pass_by_name(name).unwrap_or_else(|| {
                            println!("Unrecognised IR pass: {}.", name);
                            std::process::exit(-1);
                        });

                        match request {
                            Request::Add    => add_pass!(pass),
                            Request::Remove => remove_pass!(pass),
                        };
                    }
                }
            }
        }

        let passes: Vec<IRPass> = passes.into_iter()
            .map(|pass| registry.pass(pass))
            .collect();

        let pass_manager = ir::PassManager::with_passes(&passes);

        module.optimize(&pass_manager, stats);

        module.for_each_local_function(|_prototype, function| {
            module.dump_function_text_stdout(function);

            println!();
        });
    } else {
        println!("No TurboIR source file provided.");
    }

    Ok(())
}
