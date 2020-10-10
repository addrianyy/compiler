use std::io::{self, Write};

use super::{FunctionData, Instruction, Label, Map, Set};

fn save_svg_graph(graph_desc: &str, output_path: &str) {
    use std::process::{Command, Stdio};
    use std::io::Write;

    let mut process = Command::new("dot")
        .args(&["-Tsvg", "-o", output_path])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to run `dot`.");

    {
        let stdin = process.stdin.as_mut()
            .expect("Getting `dot` stdin failed.");

        stdin.write_all(graph_desc.as_bytes())
            .expect("Writing to `dot` stdin failed.");
    }

    let output = process.wait_with_output()
        .expect("Waiting for `dot` failed.");

    let no_output = output.stderr.is_empty() && output.stdout.is_empty();
    if !no_output {
        println!("{}", String::from_utf8_lossy(&output.stdout));
        println!("{}", String::from_utf8_lossy(&output.stderr));
    }

    assert!(output.status.success() && no_output,
        "`dot` failed to generate graph.");
}

impl FunctionData {
    fn function_prototype(&self) -> String {
        let return_type;

        match self.prototype.return_type {
            Some(ty) => return_type = format!("{}", ty),
            None     => return_type = String::from("void"),
        }

        let mut name = format!("func {} {}(", return_type, self.prototype.name);

        for index in 0..self.prototype.arguments.len() {
            name.push_str(&format!("{} {}", self.prototype.arguments[index],
                                    self.argument_values[index]));

            if index != self.prototype.arguments.len() - 1 {
                name.push_str(", ");
            }
        }

        name.push(')');

        name
    }

    fn instruction_string(&self, instruction: &Instruction) -> String {
        let mut buffer = Vec::new();
        self.print_instruction(&mut buffer, instruction).unwrap();

        String::from_utf8(buffer).unwrap()
    }

    pub fn dump_graph(&self, path: &str) {
        let mut dotgraph = String::new();

        dotgraph.push_str("digraph G {\n");

        let labels = self.traverse_bfs(Label(0), true);

        for label in labels.into_iter() {
            let insts      = &self.blocks[&label];
            let targets    = self.targets(label);

            let name = match label {
                Label(0) => self.function_prototype(),
                _        => format!("{}", label),
            };

            dotgraph.push_str(&format!(r#"{} [shape=box fontname="Consolas" label="{}\n"#,
                label, name));

            if label == Label(0) {
                dotgraph.push_str(&format!(r#"\n{}\n"#, label));
            }

            for (inst_idx, inst) in insts.iter().enumerate() {
                dotgraph.push_str(&format!("{:>3}: {}\\l", inst_idx,
                                           self.instruction_string(inst)));
            }

            dotgraph.push_str("\"];\n");

            let targets     = self.targets(label);
            let conditional = targets.len() == 2;

            for (i, target) in targets.iter().enumerate() {
                let color = match i {
                    0 if conditional => "green",
                    1 if conditional => "red",
                    _                => "blue",
                };

                dotgraph.push_str(&format!("{} -> {} [color={}];\n", label, target, color));
            }
        }

        dotgraph.push_str("}\n");

        save_svg_graph(&dotgraph, path);
    }

    pub fn dump_text<W: Write>(&self, w: &mut W) -> io::Result<()> {
        writeln!(w, "{} {{", self.function_prototype())?;

        let labels = self.traverse_bfs(Label(0), true);
        let indent = "  ";

        for label in labels.into_iter() {
            writeln!(w, "{}:", label)?;

            for inst in &self.blocks[&label] {
                writeln!(w, "{}{}", indent, self.instruction_string(inst))?;
            }

            writeln!(w)?;
        }

        writeln!(w, "}}")?;

        Ok(())
    }
}
