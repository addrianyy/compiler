use std::io::{self, Write};

use super::{FunctionData, Instruction, Label, Value};
use super::display::IRFormatter;

#[cfg(windows)]
fn stdout_use_colors() -> bool {
    // TODO: Check on Windows if stdout is redirected to file.
    true
}

#[cfg(unix)]
fn stdout_use_colors() -> bool {
    extern "C" {
        fn isatty(fd: i32) -> i32;
    }

    unsafe {
        isatty(1) == 1
    }
}

struct BlankFormatter;

impl IRFormatter for BlankFormatter {
    fn fmt_value(&self, value: Value) -> String {
        format!("{}", value)
    }

    fn fmt_type(&self, name: String) -> String {
        name
    }

    fn fmt_inst(&self, name: String) -> String {
        name
    }

    fn fmt_label(&self, label: Label) -> String {
        format!("{}", label)
    }

    fn fmt_literal(&self, literal: String) -> String {
        literal
    }

    fn fmt_function(&self, name: &str) -> String {
        name.to_owned()
    }
}

struct ConsoleFormatter;

impl IRFormatter for ConsoleFormatter {
    fn fmt_value(&self, value: Value) -> String {
        format!("\x1b[1;33m{}\x1b[0m", value)
    }

    fn fmt_type(&self, name: String) -> String {
        format!("\x1b[1;34m{}\x1b[0m", name)
    }

    fn fmt_inst(&self, name: String) -> String {
        format!("\x1b[1;32m{}\x1b[0m", name)
    }

    fn fmt_label(&self, label: Label) -> String {
        format!("\x1b[1;37m{}\x1b[0m", label)
    }

    fn fmt_literal(&self, literal: String) -> String {
        literal
    }

    fn fmt_function(&self, name: &str) -> String {
        name.to_owned()
    }
}

impl FunctionData {
    fn prototype_representation(&self, formatter: &dyn IRFormatter) -> String {
        let return_type = match self.prototype.return_type {
            Some(ty) => formatter.fmt_type(format!("{}", ty)),
            None     => formatter.fmt_type(String::from("void")),
        };

        let mut name = format!("{} {}(", return_type,
                               formatter.fmt_function(&self.prototype.name));

        for index in 0..self.prototype.arguments.len() {
            name.push_str(&format!("{} {}",
                formatter.fmt_type(format!("{}", self.prototype.arguments[index])),
                formatter.fmt_value(self.argument_values[index])
            ));

            if index != self.prototype.arguments.len() - 1 {
                name.push_str(", ");
            }
        }

        name.push(')');

        name
    }

    fn instruction_string(&self, instruction: &Instruction,
                          formatter: &dyn IRFormatter) -> String {
        let mut buffer = Vec::new();

        self.print_instruction(&mut buffer, instruction, formatter).unwrap();

        String::from_utf8(buffer).unwrap()
    }

    pub fn dump_graph(&self, path: &str) {
        let formatter    = &BlankFormatter;
        let mut dotgraph = String::new();

        dotgraph.push_str("digraph G {\n");

        for label in self.reachable_labels() {
            let instructions = &self.blocks[&label];
            let targets      = self.targets(label);

            let name = if label == self.entry() {
                self.prototype_representation(formatter)
            } else {
                format!("{}:", formatter.fmt_label(label))
            };

            dotgraph.push_str(&format!(r#"{} [shape=box fontname="Consolas" label="{}\n"#,
                                       label, name));

            if label == self.entry() {
                dotgraph.push_str(&format!(r#"\n{}:\n"#, formatter.fmt_label(label)));
            }

            for (inst_id, instruction) in instructions.iter().enumerate() {
                dotgraph.push_str(&format!("{:>3}: {}\\l", inst_id,
                                           self.instruction_string(instruction, formatter)));
            }

            dotgraph.push_str("\"];\n");

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

        crate::dot::save_graph(&dotgraph, path);
    }

    pub fn dump_text_formatter<W: Write>(&self, w: &mut W,
                                         formatter: &dyn IRFormatter) -> io::Result<()> {
        writeln!(w, "{} {{", self.prototype_representation(formatter))?;

        let     indent = "  ";
        let mut first  = true;

        for label in self.reachable_labels_dfs() {
            if !first {
                writeln!(w)?;
            }

            first = false;

            writeln!(w, "{}:", formatter.fmt_label(label))?;

            for instruction in &self.blocks[&label] {
                writeln!(w, "{}{}", indent, self.instruction_string(instruction, formatter))?;
            }
        }

        writeln!(w, "}}")?;

        Ok(())
    }

    pub fn dump_text<W: Write>(&self, w: &mut W) -> io::Result<()> {
        self.dump_text_formatter(w, &BlankFormatter)
    }

    pub fn dump_text_stdout(&self) {
        let formatter: &dyn IRFormatter = if stdout_use_colors() {
            &ConsoleFormatter
        } else {
            &BlankFormatter
        };

        self.dump_text_formatter(&mut std::io::stdout(), formatter)
            .expect("Failed to write to stdout.");
    }
}
