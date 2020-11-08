use std::io::{self, Write};

use super::{FunctionData, Instruction, Label, Value};
use super::display::IRFormatter;

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
    fn prototype_representation<F: IRFormatter>(&self, formatter: &F) -> String {
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

    fn instruction_string<F: IRFormatter>(&self, instruction: &Instruction,
                                          formatter: &F) -> String {
        let mut buffer = Vec::new();

        self.print_instruction(&mut buffer, instruction, formatter).unwrap();

        String::from_utf8(buffer).unwrap()
    }

    pub fn dump_graph(&self, path: &str) {
        let formatter    = &BlankFormatter;
        let mut dotgraph = String::new();

        dotgraph.push_str("digraph G {\n");

        for label in self.reachable_labels() {
            let insts      = &self.blocks[&label];
            let targets    = self.targets(label);

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

            for (inst_idx, inst) in insts.iter().enumerate() {
                dotgraph.push_str(&format!("{:>3}: {}\\l", inst_idx,
                                           self.instruction_string(inst, formatter)));
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

        super::dot::save_svg_graph(&dotgraph, path);
    }

    pub fn dump_text<W: Write>(&self, w: &mut W) -> io::Result<()> {
        let formatter = &ConsoleFormatter;

        writeln!(w, "{} {{", self.prototype_representation(formatter))?;

        let     indent = "  ";
        let mut first  = true;

        for label in self.reachable_labels() {
            if !first {
                writeln!(w)?;
            }

            first = false;

            writeln!(w, "{}:", formatter.fmt_label(label))?;

            for inst in &self.blocks[&label] {
                writeln!(w, "{}{}", indent, self.instruction_string(inst, formatter))?;
            }
        }

        writeln!(w, "}}")?;

        Ok(())
    }
}
