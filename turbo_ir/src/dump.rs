use std::io::{self, Write};

use super::{FunctionData, Instruction, Label};

impl FunctionData {
    fn prototype_representation(&self) -> String {
        let return_type;

        match self.prototype.return_type {
            Some(ty) => return_type = format!("{}", ty),
            None     => return_type = String::from("void"),
        }

        let mut name = format!("{} {}(", return_type, self.prototype.name);

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

        for label in self.reachable_labels() {
            let insts      = &self.blocks[&label];
            let targets    = self.targets(label);

            let name = match label {
                Label(0) => self.prototype_representation(),
                _        => format!("{}", label),
            };

            dotgraph.push_str(&format!(r#"{} [shape=box fontname="Consolas" label="{}:\n"#,
                                       label, name));

            if label == Label(0) {
                dotgraph.push_str(&format!(r#"\n{}\n"#, label));
            }

            for (inst_idx, inst) in insts.iter().enumerate() {
                dotgraph.push_str(&format!("{:>3}: {}\\l", inst_idx,
                                           self.instruction_string(inst)));
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
        writeln!(w, "{} {{", self.prototype_representation())?;

        let     indent = "  ";
        let mut first  = true;

        for label in self.reachable_labels() {
            if !first {
                writeln!(w)?;
            }

            first = false;

            writeln!(w, "{}:", label)?;

            for inst in &self.blocks[&label] {
                writeln!(w, "{}{}", indent, self.instruction_string(inst))?;
            }
        }

        writeln!(w, "}}")?;

        Ok(())
    }
}
