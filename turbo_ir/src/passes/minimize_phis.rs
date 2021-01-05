use std::cmp::Ordering;
use crate::{FunctionData, Map, Set, Value, Instruction, Location, CapacityExt};

#[derive(Default)]
struct PhisGraph {
    edges:    Map<Value, Set<Value>>,
    vertices: Vec<Value>,
}

impl PhisGraph {
    fn add_vertex(&mut self, value: Value) {
        self.vertices.push(value);
        self.edges.insert(value, Set::default());
    }

    fn add_edge(&mut self, from: Value, to: Value) {
        self.edges.get_mut(&from).unwrap().insert(to);
    }

    #[allow(unused)]
    fn dump(&self, path: &str) {
        let mut dotgraph = String::from("digraph G {\n");

        for &vertex in &self.vertices {
            dotgraph.push_str(&format!("{}\n", vertex));
        }

        for (from, to) in &self.edges {
            for to in to {
                dotgraph.push_str(&format!("{} -> {};\n", from, to));
            }
        }

        dotgraph.push_str("}\n");

        crate::dot::save_graph(&dotgraph, path);
    }

    fn scc(&self) -> Vec<Vec<Value>> {
        let mut indices = Map::default();

        // Assign index to every vertex.
        for (index, vertex) in self.vertices.iter().enumerate() {
            indices.insert(*vertex, index);
        }

        #[derive(Clone)]
        struct VertexData {
            index:      Option<usize>,
            lowlink:    usize,
            on_stack:   bool,
        }

        struct Data<'a> {
            index:    usize,
            vertices: Vec<VertexData>,
            stack:    Vec<Value>,
            sccs:     &'a mut Vec<Vec<Value>>,
        }

        fn visit(graph: &PhisGraph, vertex: Value, data: &mut Data, indices: &Map<Value, usize>) {
            macro_rules! vertex {
                ($vertex: expr) => {
                    data.vertices[indices[&$vertex]]
                };
            }

            // Skip vertex if it was already visited.
            if vertex!(vertex).index.is_some() {
                return;
            }

            let v_index = data.index;

            vertex!(vertex).index    = Some(v_index);
            vertex!(vertex).lowlink  = v_index;
            vertex!(vertex).on_stack = true;

            data.stack.push(vertex);
            data.index += 1;

            for &other in &graph.edges[&vertex] {
                match vertex!(other).index {
                    None => {
                        visit(graph, other, data, indices);

                        vertex!(vertex).lowlink = std::cmp::min(
                            vertex!(vertex).lowlink,
                            vertex!(other).lowlink,
                        );
                    }
                    Some(other_index) => {
                        if vertex!(other).on_stack {
                            let v_lowlink = &mut vertex!(vertex).lowlink;

                            *v_lowlink = std::cmp::min(*v_lowlink, other_index);
                        }
                    }
                }
            }

            if let Some(vertex_index) = vertex!(vertex).index {
                if vertex!(vertex).lowlink == vertex_index {
                    let mut cur_scc = Vec::new();

                    loop {
                        let w = data.stack.pop().unwrap();

                        vertex!(w).on_stack = false;

                        cur_scc.push(w);

                        if indices[&w] == indices[&vertex] {
                            break;
                        }
                    }

                    data.sccs.push(cur_scc);
                }
            }
        }

        let mut sccs = Vec::new();

        {
            let map = vec![
                VertexData {
                    index:    None,
                    lowlink:  !0,
                    on_stack: false,
                };
                self.vertices.len()
            ];

            let mut data = Data {
                index:    0,
                vertices: map,
                stack:    Vec::new(),
                sccs:     &mut sccs,
            };

            for &vertex in &self.vertices {
                visit(self, vertex, &mut data, &indices);
            }
        }

        sccs
    }
}

struct PhiData {
    operands: Set<Value>,
    location: Location,
}

type PhisData = Map<Value, PhiData>;

fn minimize_phis(function: &mut FunctionData, phis_data: &PhisData, phis: Set<Value>) -> bool {
    let mut graph = PhisGraph::default();

    // Add all PHIs as vertices in the graph.
    for &value in &phis {
        graph.add_vertex(value);
    }

    // Connect PHIs which reference each other.
    for &value in &phis {
        for &operand in &phis_data[&value].operands {
            // If operand of this PHI is another PHI value then we need to connect them.
            if phis.contains(&operand) {
                graph.add_edge(value, operand);
            }
        }
    }

    let mut minimized = false;

    // Get all SCCs and try to minimize them one at a time.
    for scc in graph.scc() {
        minimized |= process_scc(function, phis_data, &scc);
    }

    minimized
}

fn process_scc(function: &mut FunctionData, phis_data: &PhisData, scc: &[Value]) -> bool {
    // If there is only one PHI in the SCC than it is already in the simplest posssible form.
    if scc.len() == 1 {
        return false;
    }

    let mut outer = Set::default();
    let mut inner = Set::default();

    // Go through all PHIs in the SCC.
    for &phi in scc {
        let mut is_inner = true;

        // Get all operands outside SCC that this PHI references.
        for &operand in &phis_data[&phi].operands {
            if !scc.iter().any(|&v| v == operand) {
                outer.insert(operand);
                is_inner = false;
            }
        }

        // If this PHI references only values inside the SCC then we have sub-SCC that we will
        // try to optimize later.
        if is_inner {
            inner.insert(phi);
        }
    }

    match outer.len().cmp(&1) {
        Ordering::Equal => {
            // All PHIs in the SCC reference each other and one other value.
            // We can optimize PHIs to just reference that other value.

            // Get that other value.
            let value = outer.into_iter().next().unwrap();

            // Replace all PHIs in the cycle to aliases to other value.
            for &phi in scc {
                let location = phis_data[&phi].location;

                *function.instruction_mut(location) = Instruction::Alias {
                    dst: phi,
                    value,
                };
            }

            true
        }
        Ordering::Greater => {
            // PHIs in the SCC reference each other and more than one other value.
            // Try minimizing SCC of PHIs which don't reference other values.
            minimize_phis(function, phis_data, inner)
        }
        Ordering::Less => false,
    }
}

pub struct MinimizePhisPass;

impl super::Pass for MinimizePhisPass {
    fn name(&self) -> &str {
        "phi minimization"
    }

    fn time(&self) -> crate::timing::TimedBlock {
        crate::timing::minimize_phis()
    }

    fn run_on_function(&self, function: &mut FunctionData) -> bool {
        let mut phis_data = Map::default();
        let mut phis      = Set::default();

        // Minimize cyclic PHIs to create minimal SSA form.
        // entry:
        //   bcond u1 v0, block_1, block_2
        //
        // block_1:
        //   v2 = phi u32 [entry: v1, block_2: v3]
        //   branch block_2
        //
        // block_2:
        //   v3 = phi u32 [block_1: v2, entry: v1]
        //   bcond u1 v0, block_1, block_3
        //
        // To:
        // entry:
        //   bcond u1 v0, block_1, block_2
        //
        // block_1:
        //   branch block_2
        //
        // block_2:
        //   bcond u1 v0, block_1, block_3

        // Collect all information about PHI instructions in the function.
        function.for_each_instruction(|location, instruction| {
            if let Instruction::Phi { dst, incoming } = instruction {
                let mut operands = Set::new_with_capacity(incoming.len());

                for (_, incoming) in incoming {
                    operands.insert(*incoming);
                }

                let data = PhiData {
                    location,
                    operands,
                };

                phis.insert(*dst);
                phis_data.insert(*dst, data);
            }
        });

        // Minimize cyclic PHIs.
        minimize_phis(function, &phis_data, phis)
    }
}
