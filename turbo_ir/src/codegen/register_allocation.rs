use crate::{FunctionData, Value, Location, Label, Map, Set, ConstType,
            Dominators, FlowGraph, CapacityExt, Instruction};
use super::Backend;

const DEBUG_ALLOCATOR: bool = false;
const ALLOCATOR_INFO:  bool = false;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Place {
    Argument(usize),
    StackSlot(usize),
    Register(usize),
    Constant(usize),
}

pub struct RegisterAllocation {
    pub allocation:     Map<Value, Place>,
    pub used_registers: Set<usize>,
    pub skips:          Set<Location>,
    pub slots:          usize,
}

impl RegisterAllocation {
    pub fn get(&self, location: Location, value: Value) -> Place {
        self.allocation.get(&value).copied().unwrap_or_else(|| {
            panic!("Cannot resolve {} at location {:?}", value, location)
        })
    }
}

struct LivenessContext<'a> {
    function:      &'a FunctionData,
    flow_incoming: &'a FlowGraph,
}

#[derive(Default)]
struct Liveness {
    values: Map<Value, ValueLiveness>,
}

impl Liveness {
    fn value_dies(&self, location: Location, value: Value) -> bool {
        self.values[&value].value_dies(location)
    }

    fn dump(&self, function: &FunctionData) {
        for (value, liveness) in &self.values {
            println!("{}", value);
            println!("  {} [{}:{}] [creation]", liveness.creation_block,
                     liveness.creation_start, liveness.creation_end);

            for (block, interval) in liveness.intervals.iter() {
                if interval.end == function.blocks[&block].len() {
                    println!("  {} [whole]", block);
                } else {
                    println!("  {} [0:{}]", block, interval.end);
                }
            }

            println!();
        }
    }
}

struct Interval {
    /// Instruction ID where value was last used in the block. Equal to block size if
    /// value is used in successors too.
    end: usize,
}

struct ValueLiveness {
    /// Block where value was created.
    creation_block: Label,

    /// Instruction ID where value was created.
    creation_start: usize,

    /// Instruction ID where value was last used in the block. Equal to block size if
    /// value is used in successors too.
    creation_end: usize,

    intervals: Map<Label, Interval>,

    holes: Set<usize>,
}

impl ValueLiveness {
    fn new(creation: Location) -> Self {
        // Create liveness state with empty interval.
        Self {
            creation_block: creation.label(),
            creation_start: creation.index(),
            creation_end:   creation.index(),
            intervals:      Map::default(),
            holes:          Set::default(),
        }
    }

    fn add_usage_internal(&mut self, location: Location, is_phi: bool) -> bool {
        // Mark value as used at `location`. This will not make predecessors aware of
        // value liveness.

        // Check if this value is used in the same block its created.
        if location.label() == self.creation_block {
            if !is_phi {
                // Make sure that the value is not used before being created.
                assert!(location.index() > self.creation_start,
                        "Value is used before being created.");
            } else {
                // As a special case, PHIs can change creation_start.
                self.creation_start = usize::min(self.creation_start, location.index());
            }

            // Update last usage index in creation block.
            self.creation_end = usize::max(self.creation_end, location.index());

            // No more work needed.
            return false;
        }

        if let Some(interval) = self.intervals.get_mut(&location.label()) {
            // This value was already used in `location.block()`. Update last usage index.
            interval.end = usize::max(interval.end, location.index());

            // No more work needed.
            return false;
        }

        // This value wasn't marked as used in `location.block()`. Create a new interval for it.

        self.intervals.insert(location.label(), Interval {
            end: location.index(),
        });

        // Return true so `add_usage` will handle changing liveness of this value for
        // predecessors.
        true
    }

    fn add_usage(&mut self, location: Location, cx: &LivenessContext) {
        time!(add_value_usage);

        // Mark value as used at `location`. If this is the first time value is used
        // in `location.block()` we need to also mark value as used in every predecessor.

        if self.add_usage_internal(location, false) {
            let mut work_list = vec![location.label()];

            // First time used in this block. Mark value as used in predecessors.
            while let Some(block) = work_list.pop() {
                for &predecessor in &cx.flow_incoming[&block] {
                    // We inform that value is used in other blocks by setting
                    // it's last use index to block length.
                    let length = cx.function.blocks[&predecessor].len();

                    // Mark as used and check if we need to mark value as used in
                    // predecessors of this predecessor.
                    if self.add_usage_internal(Location::new(predecessor, length), false) {
                        work_list.push(predecessor);
                    }
                }
            }
        }
    }

    fn value_dies(&self, location: Location) -> bool {
        time!(value_dies);

        // This code assumes that if value is used in block successors, it's `end` usage index is
        // equal to block size.

        if location.label() == self.creation_block {
            // Check if `location` is part of hole in the creator block.
            if self.holes.contains(&location.index()) {
                return true;
            }

            // `location` is in the same block where value was created. This value dies
            // if last use is before or on instruction at `location`.
            return self.creation_end <= location.index();
        }

        if let Some(interval) = self.intervals.get(&location.label()) {
            // We have found interval that describes usage for block of interest.
            // This value dies if last use is before or on instruction at `location`.
            //return self.intervals[*idx].end <= location.index();
            return interval.end <= location.index();
        }

        // This value doesn't live in this block.
        true
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct VirtualRegister(u32);

#[derive(Clone, Default)]
struct VirtualRegisters {
    value_to_register: Map<Value, VirtualRegister>,
    registers:         Map<VirtualRegister, Set<Value>>,
    next_register:     VirtualRegister,
}

impl VirtualRegisters {
    fn allocate(&mut self) -> VirtualRegister {
        let register = self.next_register;

        self.next_register = VirtualRegister(register.0 + 1);
        self.registers.insert(register, Set::default());

        register
    }

    fn map(&mut self, value: Value, register: VirtualRegister) {
        self.value_to_register.insert(value, register);
        self.registers.get_mut(&register).unwrap().insert(value);
    }

    fn value_register(&self, value: Value) -> VirtualRegister {
        self.value_to_register[&value]
    }

    fn register_values(&self, register: VirtualRegister) -> &Set<Value> {
        &self.registers[&register]
    }

    fn get(&self, value: Value) -> Option<VirtualRegister> {
        self.value_to_register.get(&value).cloned()
    }

    fn uniquely_map_rest(&mut self, function: &FunctionData) {
        time!(uniquely_map_rest);

        for value in 0..function.value_count() {
            let value = Value(value as u32);

            // If we already don't have VR for this Value, create and assign one.
            if self.value_to_register.get(&value).is_none() {
                let register = self.allocate();

                self.map(value, register);
            }
        }
    }
}

type Entity = VirtualRegister;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Color(u32);

#[derive(Default)]
struct Coloring {
    vertex_color: Map<Entity, Color>,
    color_list:   Vec<Color>,
    next_color:   Color,
}

impl Coloring {
    fn pick_color(&mut self, unusable: Set<Color>) -> Color {
        time!(pick_color);

        // Try to use already known color if possible.
        for &color in &self.color_list {
            // Return first usable color from the list.
            if !unusable.contains(&color) {
                return color;
            }
        }

        // Out of colors. Create a new one.
        let color = self.next_color;

        self.next_color = Color(color.0 + 1);
        self.color_list.push(color);

        color
    }
}

#[derive(Default)]
struct InterferenceGraph {
    edges:          Map<Entity, Set<Entity>>,
    vertices:       Vec<Entity>,
    vertices_dedup: Set<Entity>,
}

impl InterferenceGraph {
    fn add_vertex(&mut self, entity: Entity) {
        // It's possible that somebody has already added that vertex. That's
        // not an error, just don't add it again.
        if self.vertices_dedup.insert(entity) {
            self.vertices.push(entity);
            self.edges.insert(entity, Set::default());
        }
    }

    fn add_edge(&mut self, e1: Entity, e2: Entity) {
        // Register always interferes with itself.
        if e1 == e2 {
            return;
        }

        // Insert edge from `e1` to `e2`.
        self.edges.get_mut(&e1).unwrap().insert(e2);

        // Insert edge from `e2` to `e1`.
        self.edges.get_mut(&e2).unwrap().insert(e1);
    }

    fn unique_edges(&self) -> Set<(Entity, Entity)> {
        time!(unique_edges);

        let mut result = Set::default();

        for (&entity, links) in &self.edges {
            for &other in links {
                let mut e1 = entity;
                let mut e2 = other;

                // Make edge format canonical, so (from, to) and (to, from) will become
                // the same thing.
                if e1 > e2 {
                    std::mem::swap(&mut e1, &mut e2);
                }

                result.insert((e1, e2));
            }
        }

        result
    }

    fn interfere_and_nonequal(&self, e1: Entity, e2: Entity) -> bool {
        // We return false if e1 == e2.
        self.edges[&e1].contains(&e2)
    }

    fn coloring_order(&self) -> Vec<Entity> {
        time!(coloring_order);

        // https://staame.wordpress.com/2014/12/17/simple-chordal-graph-coloring/

        let mut max_index = 0;

        for &vertex in &self.vertices {
            if vertex.0 > max_index {
                max_index = vertex.0;
            }
        }

        // Assign weight of 0 for all vertices.
        let mut weights = vec![0; max_index as usize + 1];

        // Empty elimination order.
        let mut elimination_ordering = Vec::with_capacity(self.vertices.len());

        // Start with all vertices queued for processing.
        let mut queue: Vec<_> = self.vertices.iter()
            .copied()
            .collect();

        while !queue.is_empty() {
            let mut heaviest = None;

            // Find vertex in the queue with highest weight.
            for (index, &vertex) in queue.iter().enumerate() {
                let weight  = weights[vertex.0 as usize];
                let heavier = match heaviest {
                    Some((_, _, other_weight)) => weight > other_weight,
                    None                       => true,
                };

                if heavier {
                    heaviest = Some((index, vertex, weight));
                }
            }

            // Get vertex from the queue with maximum weight.
            let heaviest = heaviest.expect("Failed to find heaviest vertex.");

            // Get all neighbours of the vertex with maximum weight.
            let adjacent = &self.edges[&heaviest.1];

            // Remove vertex from the queue and append it to perfect elimination order.
            queue.remove(heaviest.0);
            elimination_ordering.push(heaviest.1);

            // Increase weights of all neighbour vertices.
            for vertex in adjacent {
                weights[vertex.0 as usize] += 1;
            }
        }

        elimination_ordering
    }

    fn color(&self) -> Coloring {
        time!(color);

        // Get optimal ordering for greedy coloring algorithm.
        let order = self.coloring_order();

        // Make sure that optimal ordering we got is valid.
        assert_eq!(order.len(), self.vertices.len(), "Order doesn't include all \
                   vertices in the graph.");

        let mut coloring = Coloring::default();

        for vertex in order {
            let mut used = Set::default();

            // Get a list of colors that are used by neighbours and therafore are unsuitable
            // for coloring this vertex.
            for &neighbour in &self.edges[&vertex] {
                // It's possible that this neighbour doesn't have a color assigned yet.
                // In this case just skip it.
                if let Some(&color) = coloring.vertex_color.get(&neighbour) {
                    used.insert(color);
                }
            }

            // Pick a valid color for this vertex.
            let color = coloring.pick_color(used);

            // Color this vertex.
            assert!(coloring.vertex_color.insert(vertex, color).is_none(),
                    "Vertex color was assigned multiple times.");
        }

        // Make sure that we actually colored everything.
        assert_eq!(coloring.vertex_color.len(), self.vertices.len(),
                   "Not all vertices were colored.");

        coloring
    }
}

impl FunctionData {
    fn liveness(&self, _dominators: &Dominators, labels: &[Label]) -> Liveness {
        time!(liveness);

        let mut liveness = Liveness::default();

        let flow_incoming = self.flow_graph_incoming();
        let cx            = LivenessContext {
            function:      self,
            flow_incoming: &flow_incoming,
        };

        self.for_each_instruction_with_labels(labels, |location, instruction| {
            if let Some(value) = instruction.created_value() {
                // Create a new, empty liveness state for output value.
                assert!(liveness.values.insert(value, ValueLiveness::new(location)).is_none(),
                        "Value created multiple times.");
            }

            // PHI incoming values will be handled later.
            if let Instruction::Phi { .. } = instruction {
                return;
            }

            for input in instruction.read_values() {
                // Ignore all special values.
                if self.is_value_special(input) {
                    continue;
                }

                // Get liveness state for this input value.
                let input_liveness = liveness.values.get_mut(&input)
                    .expect("Failed to get liveness state for value.");

                // Mark that this value is used at `location`.
                input_liveness.add_usage(location, &cx);
            }
        });

        let mut special_phi_uses = Vec::new();

        // Now handle PHI input values.
        self.for_each_instruction_with_labels(labels, |location, instruction| {
            if let Instruction::Phi { incoming, .. } = instruction {
                // All PHI input values will be mapped to the same register.
                //
                // It is important that we properly set liveness of PHI inputs. There are
                // two things which we need to take care of.
                //
                // 1. PHI inputs must live to the end of block which predeceses PHI.
                // 2. PHI inputs must live in PHI block to the correct PHI instruction.
                //
                // Register allocator must handle use before creation for PHI instructions.

                for (label, value) in incoming {
                    // Get liveness state for this incoming value.
                    let value_liveness = liveness.values.get_mut(&value)
                        .expect("Failed to get liveness state for value.");

                    let length = self.blocks[&label].len();

                    // Make incoming value live to the end of the block (case 1).
                    value_liveness.add_usage(Location::new(*label, length), &cx);

                    // Queue use of value in PHI block (case 2).
                    special_phi_uses.push((location, *value));
                }
            }
        });

        let creators = self.value_creators_with_labels(labels);

        // Handle uses of incoming values in PHI blocks.
        for (location, value) in special_phi_uses {
            // Get liveness state for this incoming value.
            let value_liveness = liveness.values.get_mut(&value)
                .expect("Failed to get liveness state for value.");

            // We don't want to use `add_usage` here because it will propagate uses
            // to all predecessors which we don't want for PHI incoming values. Therefore we
            // use internal function which won't modify liveness in predecessors.
            value_liveness.add_usage_internal(location, true);

            // If PHI input value is defined in the same block it's used its lifetime
            // will be set to whole block. This is not good. This value will live
            // from block start to PHI instruction and then from definition to end of block.
            // Make holes in creator block to represent this.
            let creator = creators[&value];
            if  creator.label() == location.label() {
                for inst_id in location.index()..creator.index() {
                    value_liveness.holes.insert(inst_id);
                }
            }
        }

        liveness
    }

    fn dump_interference_graph(&self, interference: &InterferenceGraph, coloring: &Coloring,
                               register_to_values: &Map<VirtualRegister, Set<Value>>) {
        const COLOR_LIST: &[&str] = &[
            "#e6194B",
            "#3cb44b",
            "#ffe119",
            "#4363d8",
            "#f58231",
            "#911eb4",
            "#42d4f4",
            "#f032e6",
            "#bfef45",
            "#fabed4",
            "#469990",
            "#dcbeff",
            "#9A6324",
            "#fffac8",
            "#800000",
            "#aaffc3",
            "#808000",
            "#ffd8b1",
            "#000075",
            "#a9a9a9",
            "#ffffff",
        ];

        let mut dotgraph = String::from("graph G {\n");

        // If there are too many VRs we need to fall back to numbering instead of coloring.
        let can_use_colors = coloring.color_list.len() <= COLOR_LIST.len();

        for &vertex in &interference.vertices {
            let color  = coloring.vertex_color[&vertex];
            let values = &register_to_values[&vertex];
            let label  = {
                // Create a label for given VR. Take coalescing into account.
                let mut label = String::new();
                let mut first = true;

                for &value in values {
                    if !first {
                        label.push_str(", ");
                    }

                    label.push_str(&format!("{}", value));

                    first = false;
                }

                if values.len() == 1 {
                    label
                } else {
                    format!("Coalesced({})", label)
                }
            };

            // We need to use differenct colors and labels if we don't use coloring.
            let (color, label) = match can_use_colors {
                true  => (COLOR_LIST[color.0 as usize], label),
                false => ("#9999FF", format!("{} [R{}]", label, color.0)),
            };

            // Output dot vertex.
            let def = format!("{} [style = filled; fillcolor = \"{}\"; label = \"{}\"];\n",
                              vertex.0, color, label);

            dotgraph.push_str(&def);
        }

        // Connect vertices.
        for (e1, e2) in interference.unique_edges() {
            dotgraph.push_str(&format!("{} -- {};\n", e1.0, e2.0));
        }

        dotgraph.push_str("}\n");

        crate::dot::save_svg_graph(&dotgraph, &format!("graphs/interference_{}.svg",
                                                       self.prototype.name));
    }

    fn interference_graph(
        &self,
        bfs_labels:         &[Label],
        virtual_registers:  &VirtualRegisters,
        liveness:           &Liveness,
        dominators:         &Dominators,
        constants:          &Map<Value, i64>,
    ) -> InterferenceGraph {
        time!(interference_graph);

        // State of used values for each block.
        let mut block_alloc_state: Map<Label, Vec<Value>> =
            Map::new_with_capacity(self.blocks.len());

        // Entry block starts with empty state.
        block_alloc_state
            .entry(self.entry())
            .or_insert_with(Default::default);

        let get_entity = |value: Value| {
            // Register allocation entity is not a Value, it's a VirtualRegister.
            virtual_registers.value_register(value)
        };

        let mut interference = InterferenceGraph::default();
        let mut to_free: Vec<Value> = Vec::new();

        for &label in bfs_labels {
            // If there is no register usage state for this block then take one
            // from immediate dominator (as we can only use values originating from it).
            #[allow(clippy::map_entry)]
            if !block_alloc_state.contains_key(&label) {
                let idom   = dominators[&label];
                let allocs = block_alloc_state[&idom].clone();

                block_alloc_state.insert(label, allocs);
            }

            let block_allocs = block_alloc_state.get_mut(&label).unwrap();
            let block        = &self.blocks[&label];

            // PHI values can be used before being defined so we must make them alive
            // in this block.
            for instruction in block.iter() {
                if let Instruction::Phi { incoming, .. } = instruction {
                    for (_, value) in incoming {
                        // Make PHI input value alive if it's currently not.
                        if block_allocs.iter().position(|x| x == value).is_none() {
                            block_allocs.push(*value);
                        }
                    }
                }
            }

            // Process register usage for every instruction in the block.
            for (inst_id, instruction) in block.iter().enumerate() {
                let location = Location::new(label, inst_id);

                to_free.clear();

                // Get a list of all values which aren't used anymore and can be freed.
                for &value in block_allocs.iter() {
                    if liveness.value_dies(location, value) {
                        to_free.push(value);
                    }
                }

                // Free all queued values.
                for &value in &to_free {
                    // Get index of unused value.
                    let item = block_allocs.iter()
                        .position(|&x| x == value)
                        .unwrap();

                    block_allocs.remove(item);
                }

                if let Some(output) = instruction.created_value() {
                    // Skip optimizable constants.
                    if constants.get(&output).is_some() {
                        continue;
                    }

                    // Get RA entity of value to allocate.
                    let output_entity = get_entity(output);

                    // Because of coalescing it's possible that `output_entity` is already in
                    // the interference graph. In this case it won't be added.
                    interference.add_vertex(output_entity);

                    // Newly created VR interferes with all currently alive VRs.
                    for &value in block_allocs.iter() {
                        interference.add_edge(output_entity, get_entity(value));
                    }

                    // Add allocated value to usage state.
                    block_allocs.push(output);
                }
            }
        }

        interference
    }

    fn map_virtual_registers(
        &self,
        bfs_labels: &[Label],
        liveness:   &Liveness,
        dominators: &Dominators,
        constants:  &Map<Value, i64>,
    ) -> VirtualRegisters {
        time!(map_virtual_registers);

        let mut virtual_registers = VirtualRegisters::default();

        // Given a PHI instruction, every input must be mapped to the same
        // register. This won't create problems because `rewrite_phis` should make
        // copies of all incoming values for PHIs.
        self.for_each_instruction(|_location, instruction| {
            if let Instruction::Phi { incoming, .. } = instruction {
                let register = virtual_registers.allocate();

                // Map all inputs to the same register.
                for (_, value) in incoming {
                    virtual_registers.map(*value, register);
                }
            }
        });

        // Save initial Value->Register mapping for PHI values only.
        let phi_registers = virtual_registers.clone();

        // Uniquely map all other values.
        virtual_registers.uniquely_map_rest(self);

        // Build interference graph which is required for coalescing.
        let interference = self.interference_graph(
            bfs_labels,
            &virtual_registers,
            liveness,
            dominators,
            constants,
        );

        // Given a sequence:
        // v5 = add v4, v1
        // If it's the last usage of v4 then v5 and v4 should be allocated in the same
        // register. To make this possible we an make abstraction over Values - VirtualRegisters.
        // In this case v4 and v5 will get assigned the same VirtualRegister.

        let     interference_registers = virtual_registers;
        let mut virtual_registers      = phi_registers;

        let mut coalesce_values = |v1: Value, v2: Value| {
            time!(coalesce_values);
            // Try to assign the same VirtualRegister to both Values.

            let v1_vr = virtual_registers.get(v1).ok_or(v1);
            let v2_vr = virtual_registers.get(v2).ok_or(v2);

            // TODO: Improve this.

            match (v1_vr, v2_vr) {
                (Ok(_), Ok(_)) => {
                    // Either values are already coalesced or they are in different VRs.
                    // We cannot do anything here.

                    false
                }
                (Ok(map_register), Err(value)) | (Err(value), Ok(map_register)) => {
                    let mut valid = true;

                    // We need to make sure that `value` doesn't interfere
                    // with any value mapped to `map_register`.

                    // Get old VR for `value`.
                    let value_register = interference_registers.value_register(value);

                    // Go through all values mapped to `map_register`.
                    for &other in virtual_registers.register_values(map_register) {
                        let other_register = interference_registers.value_register(other);

                        // Make sure that nothing in `map_register` interferes with value.
                        if interference.interfere_and_nonequal(value_register, other_register) {
                            valid = false;
                            break;
                        }
                    }

                    if valid {
                        virtual_registers.map(value, map_register);
                    }

                    valid
                }
                (Err(_), Err(_)) => {
                    // Both Values don't have assigned VirtualRegister.

                    // Get old VirtualRegisters for given Values.
                    let v1_old = interference_registers.value_register(v1);
                    let v2_old = interference_registers.value_register(v2);

                    // Make sure that values can be merged.
                    assert!(!interference.interfere_and_nonequal(v1_old, v2_old),
                            "Tried to coalesce overlapping values.");

                    let register = virtual_registers.allocate();

                    // Assign the same new VR for both Values.
                    virtual_registers.map(v1, register);
                    virtual_registers.map(v2, register);

                    true
                }
            }
        };

        loop {
            let mut did_something = false;

            // Coalesce Values by assigning the same VirtualRegisters to them.
            self.for_each_instruction(|location, instruction| {
                if let Some(output) = instruction.created_value() {
                    if let Some(&input) = instruction.read_values().get(0) {
                        // We cannot coalesce special values or constants.
                        if self.is_value_special(input)     ||
                            constants.get(&input).is_some() ||
                            constants.get(&output).is_some() {
                            return;
                        }

                        // If first operand dies after this instruction we can coalesce
                        // it with output Value.
                        if liveness.value_dies(location, input) && coalesce_values(output, input) {
                            did_something = true;
                        }
                    }
                }
            });

            if !did_something {
                break;
            }
        }

        // Values which are left will get unique VirtualRegisters.
        virtual_registers.uniquely_map_rest(self);

        virtual_registers
    }

    fn rewrite_phis(&mut self, labels: &[Label]) {
        time!(rewrite_phis);

        // label_0:
        //   v1 = u32 0
        //   branch label_1
        //
        // label_1:
        //   v2 = phi u32 [label_0: v1, label_1: v6]
        //   v3 = phi u32 [label_0: v1, label_1: v4]
        //   v4 = add u32 v3, v2
        //   v5 = u32 1
        //   v6 = add u32 v2, v5
        //   v7 = u32 6
        //   v8 = icmp ne u32 v6, v7
        //   bcond u1 v8, label_1, label_2
        //
        // label_2:
        //   ret u32 v3
        //
        // Will get rewritten to:
        // label_0:
        //   v1 = u32 0
        //   v9 = alias u32 v1
        //   v11 = alias u32 v1
        //   branch label_1
        //
        // label_1:
        //   v2 = phi u32 [label_0: v9, label_1: v10]
        //   v3 = phi u32 [label_0: v11, label_1: v12]
        //   v4 = add u32 v3, v2
        //   v5 = u32 1
        //   v6 = add u32 v2, v5
        //   v7 = u32 6
        //   v10 = alias u32 v6
        //   v12 = alias u32 v4
        //   v8 = icmp ne u32 v6, v7
        //   bcond u1 v8, label_1, label_2
        //
        // label_2:
        //   ret u32 v3

        let mut phis = Vec::new();

        // Get list of all PHIs in the function.
        self.for_each_instruction_with_labels(labels, |location, instruction| {
            if let Instruction::Phi { dst, incoming } = instruction {
                phis.push((location, *dst, incoming.clone()));
            }
        });

        let has_phis = !phis.is_empty();

        for (phi_location, phi_dst, incoming) in phis {
            let mut new_incoming = Vec::new();

            // Rewrite all incoming values. Even though we are inserting new instructions
            // it's fine to use the same locations. PHIs must be first instructions in the
            // block so insertions won't affect position of them.
            for (label, value) in incoming {
                // All incoming values from PHI will be mapped to the same VirtualRegister.
                // To avoid interference problems we will copy every incoming value to
                // another value with `alias` and use these new aliased values.

                // Allocate alias value.
                let value_type = self.value_type(value);
                let alias      = self.allocate_typed_value(value_type);

                let body = self.blocks.get_mut(&label).unwrap();

                // Calculate where to insert new alias instruction.
                let index = if body.len() == 1 {
                    0
                } else {
                    // To help x86 backend try to not put alias inbetween icmp and bcond.
                    if let Instruction::IntCompare { dst, .. } = body[body.len() - 2] {
                        if dst != value {
                            body.len() - 2
                        } else {
                            // Can't do this ;(.
                            body.len() - 1
                        }
                    } else {
                        // Always second last instruction.
                        body.len() - 1
                    }
                };

                // Insert alias which will copy PHI incoming value.
                body.insert(index, Instruction::Alias {
                    dst: alias,
                    value,
                });

                // Add aliased value to PHI incoming values.
                new_incoming.push((label, alias));
            }

            // Create new PHI with modified incoming values.
            let new_phi = Instruction::Phi {
                dst:      phi_dst,
                incoming: new_incoming,
            };

            // Replace old PHI with rewritten one.
            *self.instruction_mut(phi_location) = new_phi;
        }

        if has_phis {
            // If we have rewritten PHIs make sure we didn't break anything.
            self.validate_ssa();

            if DEBUG_ALLOCATOR {
                println!("Rewritten PHIs: ");

                self.dump_text_stdout();

                println!();
            }
        }
    }

    fn rewrite_arguments(&mut self, labels: &[Label]) {
        time!(rewrite_arguments);

        let usage_counts = self.usage_counts();
        let arguments    = self.argument_values.clone();

        let mut aliases = Map::default();

        for argument in arguments {
            if usage_counts[argument.index()] > 5 {
                let ty    = self.value_type(argument);
                let value = self.allocate_typed_value(ty);

                aliases.insert(argument, value);
            }
        }

        if !aliases.is_empty() {
            self.for_each_instruction_with_labels_mut(labels, |_, instruction| {
                instruction.transform_inputs(|value| {
                    if let Some(new) = aliases.get(value) {
                        *value = *new;
                    }
                });
            });

            // TODO: Use LCA on dominator tree to find the best insertion point.
            let entry_body = self.blocks.get_mut(&self.entry()).unwrap();

            for (old, new) in aliases {
                entry_body.insert(0, Instruction::Alias {
                    dst:   new,
                    value: old,
                });
            }
        }
    }

    fn constants_and_skips(&self, backend: &dyn Backend, labels: &[Label])
        -> (Map<Value, i64>, Set<Location>)
    {
        time!(constants_and_skips);

        let mut constants = Map::default();
        let mut skips     = Set::default();

        let creators = self.value_creators_with_labels(labels);
        let users    = self.users_with_labels(labels);

        for (value, (ty, constant)) in self.constant_values_with_labels(labels) {
            // Sign extend constant to 64 bit value.
            let constant = match ConstType::new(ty) {
                ConstType::U1  => (constant & 1) as i64,
                ConstType::U8  => constant as u8  as i8  as i64,
                ConstType::U16 => constant as u16 as i16 as i64,
                ConstType::U32 => constant as u32 as i32 as i64,
                ConstType::U64 => constant as i64,
            };

            let users: Vec<&Instruction> = users.get(&value).map(|users| {
                users
                    .iter()
                    .map(|location| self.instruction(*location))
                    .collect()
            }).unwrap_or_else(Vec::new);

            if backend.can_inline_constant(self, value, constant, &users) {
                // This is optimizable constant, add it to the list.
                constants.insert(value, constant);
                skips.insert(creators[&value]);
            }
        }

        (constants, skips)
    }

    pub(super) fn allocate_registers(&mut self, backend: &dyn Backend) -> RegisterAllocation {
        time!(allocate_registers);

        let hardware_registers = backend.hardware_registers();
        let labels             = self.reachable_labels();

        self.rewrite_phis(&labels);
        self.rewrite_arguments(&labels);

        // Get all constant values and all `iconst` instructions that we can skip.
        let (constants, skips) = self.constants_and_skips(backend, &labels);

        let dominators = self.dominators();
        let liveness   = self.liveness(&dominators, &labels);

        if DEBUG_ALLOCATOR {
            println!("Values liveness: ");

            liveness.dump(self);

            println!();
        }

        // Map Values to VirtualRegisters.
        let virtual_registers = self.map_virtual_registers(
            &labels,
            &liveness,
            &dominators,
            &constants,
        );

        // Build interference graph for given Value->VR mapping.
        let interference = self.interference_graph(
            &labels,
            &virtual_registers,
            &liveness,
            &dominators,
            &constants,
        );

        let coloring           = interference.color();
        let required_registers = coloring.color_list.len();

        if DEBUG_ALLOCATOR || ALLOCATOR_INFO {
            println!("{}: Colored interference graph with {} colors. HR: {}.",
                     self.prototype.name, coloring.color_list.len(), hardware_registers);
        }

        if DEBUG_ALLOCATOR {
            // Dump colored interference graph to the file.
            self.dump_interference_graph(&interference, &coloring,
                                         &virtual_registers.registers);
        }

        let usage_counts = self.usage_counts();

        let colors = if required_registers > hardware_registers {
            // We can't fit all VRs in hardware registers. We need to move some VRs to
            // the memory. Get usage counts to figure out best candidates.

            let mut usages: Map<Color, usize> = Map::default();

            for (&register, &color) in coloring.vertex_color.iter() {
                for &value in virtual_registers.register_values(register) {
                    *usages.entry(color).or_insert(0) +=
                        usage_counts[value.index()] as usize;
                }
            }

            assert_eq!(usages.len(), required_registers, "Color count mismatch.");

            let mut usages: Vec<(Color, usize)> = usages.into_iter().collect();

            // Sort colors so that most frequently used is at the beginning of the list.
            usages.sort_by_key(|(_, usages)| std::cmp::Reverse(*usages));

            // Create a list of colors.
            usages.into_iter().map(|(color, _)| color).collect()
        } else {
            // Order of colors doesn't matter here, all VRs are going to be allocated
            // in hardware registers.
            coloring.color_list.clone()
        };

        // Get numer of stack slots required. This basically calculates how many
        // VRs don't fit in hardware registers.
        let mut stack_slots = colors.len().saturating_sub(hardware_registers);

        let mut color_to_place = Map::default();
        let mut used_registers = Set::default();

        // Map colors to places.
        for (index, color) in colors.into_iter().enumerate() {
            let place = if index < hardware_registers {
                used_registers.insert(index);

                // This color fits in register.
                Place::Register(index)
            } else {
                // This color needs to be put in memory.
                Place::StackSlot(index - hardware_registers)
            };

            assert!(color_to_place.insert(color, place).is_none(),
                    "Color has assigned multiple places.");
        }

        let mut value_to_place = Map::default();

        // Remove all layers of abstractions to get finally Value to Place mapping.
        for (&value, &register) in &virtual_registers.value_to_register {
            if let Some(&color) =  coloring.vertex_color.get(&register) {
                // Get place assigned to this color.
                let place = color_to_place[&color];

                if DEBUG_ALLOCATOR {
                    println!("{} -> {:?}", value, place);
                }

                assert!(value_to_place.insert(value, place).is_none(),
                        "Multiple places assigned to the value.");
            }

            // There is no coloring for this value. Either it's an argument
            // or this value is dead.
        }

        // Fill in optimized constants.
        for (&value, &constant) in &constants {
            // Assign constant to this value.
            assert!(value_to_place.insert(value, Place::Constant(constant as usize)).is_none(),
                    "Multiple places assigned to the value.");
        }

        // Fill in places of function arguments.
        for (index, argument) in self.argument_values.iter().enumerate() {
            assert!(value_to_place.insert(*argument, Place::Argument(index)).is_none(),
                    "Argument is already assigned.");
        }

        // Fill in places of undefined values to whatever place is available.
        for &value in self.undefined_set.iter() {
            // Skip unused values.
            if usage_counts[value.index()] == 0 {
                continue;
            }

            // Skip values which place was assigned due to coalescing.
            if value_to_place.get(&value).is_some() {
                continue;
            }

            // Pick first place available.
            let place = if hardware_registers > 0 {
                Place::Register(0)
            } else {
                if stack_slots == 0 {
                    stack_slots += 1;
                }

                Place::StackSlot(0)
            };

            value_to_place.insert(value, place);
        }

        RegisterAllocation {
            allocation: value_to_place,
            slots:      stack_slots,
            used_registers,
            skips,
        }
    }
}
