use super::{FunctionData, Value, Location, Label, Map, Set,
            Dominators, FlowGraph, CapacityExt};

const DEBUG_ALLOCATOR: bool = true;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Place {
    Argument(usize),
    StackSlot(usize),
    Register(usize),
}

pub struct RegisterAllocation {
    //pub allocation: Map<Location, Map<Value, Place>>,
    pub allocation: Map<Value, Place>,
    pub arguments:  Map<Value, Place>,
    pub used_regs:  Set<usize>,
    pub slots:      usize,
}

impl RegisterAllocation {
    pub fn get(&self, location: Location, value: Value) -> Place {
        if let Some(place) = self.arguments.get(&value) {
            return *place;
        }

        /*
        self.allocation[&location].get(&value).copied()
            .unwrap_or_else(|| panic!("Cannot resolve {} at location {:?}", value, location))
        */

        self.allocation.get(&value).copied()
            .unwrap_or_else(|| panic!("Cannot resolve {} at location {:?}", value, location))
    }
}

struct LivenessContext<'a> {
    function:      &'a FunctionData,
    dominators:    &'a Dominators,
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
}

struct Interval {
    block: Label,

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

    intervals: Vec<Interval>,
}

impl ValueLiveness {
    fn new(creation: Location) -> Self {
        // Create liveness state with empty interval.
        Self {
            creation_block: creation.label(),
            creation_start: creation.index(),
            creation_end:   creation.index(),
            intervals:      Vec::new(),
        }
    }

    fn add_usage_internal(&mut self, location: Location, cx: &LivenessContext) -> bool {
        // Mark value as used at `location`. This will not make predecessors aware of
        // value liveness.

        // Check if this value is used in the same block its created.
        if location.label() == self.creation_block {
            // Make sure that the value is not used before being created.
            assert!(location.index() > self.creation_start,
                    "Value is used before being created.");

            // Update last usage index in creation block.
            self.creation_end = usize::max(self.creation_end, location.index());

            // No more work needed.
            return false;
        }

        for interval in &mut self.intervals {
            if interval.block == location.label() {
                // This value was already used in `location.block()`. Update last usage index.
                interval.end = usize::max(interval.end, location.index());

                // No more work needed.
                return false;
            }
        }

        // This value wasn't marked as used in `location.block()`. Create a new interval for it.

        // Make sure that this value can be used at `location`.
        let creation = Location::new(self.creation_block, self.creation_start);
        let valid    = cx.function.validate_path(cx.dominators, creation, location);
        assert!(valid, "This value cannot be used at that location.");

        self.intervals.push(Interval {
            block: location.label(),
            end:   location.index(),
        });

        // Return true so `add_usage` will handle changing liveness of this value for
        // predecessors.
        true
    }

    fn add_usage(&mut self, location: Location, cx: &LivenessContext) {
        // Mark value as used at `location`. If this is the first time value is used
        // in `location.block()` we need to also mark value as used in every predecessor.

        if self.add_usage_internal(location, cx) {
            let mut work_list = vec![location.label()];

            // First time used in this block. Mark it as used in predecessors.
            while let Some(block) = work_list.pop() {
                for &predecessor in &cx.flow_incoming[&block] {
                    // We inform that value is used in other blocks by setting
                    // it's last use index to block length.
                    let length = cx.function.blocks[&predecessor].len();

                    // Mark as used and check if we need to mark value as used in
                    // predecessors of this predecessor.
                    if self.add_usage_internal(Location::new(predecessor, length), cx) {
                        work_list.push(predecessor);
                    }
                }
            }
        }
    }

    fn value_dies(&self, location: Location) -> bool {
        // This code assumes that if value is used in block successors, it's `end` usage index is
        // equal to block size.

        if location.label() == self.creation_block {
            // `location` is in the same block where value was created. This value dies
            // if last use is before or on instruction at `location`.
            return self.creation_end <= location.index();
        }

        for interval in &self.intervals {
            if interval.block == location.label() {
                // We have found interval that describes usage for block of interest.
                // This value dies if last use is before or on instruction at `location`.
                return interval.end <= location.index();
            }
        }

        // This value doesn't live in this block.
        true
    }
}

type Entity = VirtualRegister;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct VirtualRegister(u32);

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
        // It's invalid to create cycle like this.
        assert!(e1 != e2, "Two edge sides are the same.");

        // Insert edge from `e1` to `e2`.
        self.edges.get_mut(&e1).unwrap().insert(e2);

        // Insert edge from `e2` to `e1`.
        self.edges.get_mut(&e2).unwrap().insert(e1);
    }

    fn unique_edges(&self) -> Set<(Entity, Entity)> {
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

    fn coloring_order(&self, reverse: bool) -> Vec<Entity> {
        // https://staame.wordpress.com/2014/12/17/simple-chordal-graph-coloring/

        let mut elimination_ordering = Vec::new();
        let mut weights              = Map::default();

        // Start with all vertices queued for processing.
        let mut queue: Set<_> = self.vertices.iter()
            .copied()
            .collect();

        // Assign weight of 0 for all vertices.
        for &vertex in &queue {
            assert!(weights.insert(vertex, 0).is_none(),
                    "Multiple weigths for single vertex.");
        }

        while !queue.is_empty() {
            let mut heaviest = None;

            // Find vertex in the queue with highest weight.
            for &vertex in &queue {
                let weight  = weights[&vertex];
                let heavier = match heaviest {
                    Some((_, other_weight)) => weight > other_weight,
                    None                    => true,
                };

                if heavier {
                    heaviest = Some((vertex, weight));
                }
            }

            // Get vertex from the queue with maximum weight.
            let heaviest = heaviest.expect("Failed to find heaviest vertex.").0;

            // Get all neighbours of the vertex with maximum weight.
            let adjacent = self.edges[&heaviest].clone();

            // Remove vertex from the queue and append it to perfect elimination order.
            queue.remove(&heaviest);
            elimination_ordering.push(heaviest);

            // Increase weights of all neighbour vertices which are still in the queue.
            for vertex in adjacent.intersection(&queue) {
                *weights.get_mut(&vertex).unwrap() += 1;
            }
        }

        // In theory you should reverse perfect elimination ordering to
        // get optimal coloring order.
        if reverse {
            elimination_ordering.into_iter().rev().collect()
        } else {
            elimination_ordering
        }
    }

    fn color_internal(&self, reverse: bool) -> Coloring {
        // Get optimal ordering for greedy coloring algorithm.
        let order = self.coloring_order(reverse);

        // Make sure that optimal ordering we got is valid.
        assert!(order.len() == self.vertices.len(), "Order doesn't include all \
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
        assert!(coloring.vertex_color.len() == self.vertices.len(),
                "Not all vertices were colored.");

        coloring
    }

    fn color(&self) -> Coloring {
        // Reversed PEO should give better results but I am not sure. Let's try both
        // to make sure that that's actually the case.\
        // TODO: Remove this when we are sure about the results.
        let normal   = self.color_internal(false);
        let reversed = self.color_internal(true);

        // Notify user when there is any difference in coloring results.
        assert_eq!(reversed.color_list.len(), normal.color_list.len(),
                   "Reversed PEO gave different graph coloring results than normal one.");

        // Return reversed version by default.
        reversed
    }
}

impl FunctionData {
    #[allow(unused)]
    fn lifetimes(&self) -> Map<Location, Vec<bool>> {
        let mut lifetimes = Map::default();
        let creators      = self.value_creators();

        // For every location in the program create a list of values which are used AFTER
        // instruction at that location.

        for label in self.reachable_labels() {
            // We start without any values used.
            let mut used = vec![false; self.value_count()];

            // Get all reachable blocks from current one.
            let reachable_labels = self.traverse_bfs(label, false);

            // Go through every block that we can reach from current label and get all
            // values which are being used there. This will include ourselves if we can
            // reach ourselves via loop.
            for &target_label in &reachable_labels {
                for instruction in &self.blocks[&target_label] {
                    for input in instruction.read_values() {
                        // We don't care about arguments for now.
                        if self.is_value_argument(input) {
                            continue;
                        }

                        // If value is being used in the same block it's being created
                        // then there is no need to set it as used. It will be recreated.
                        //
                        // If we can reach ourselves via loop:
                        // 1. Value is being created in current block and used before our
                        //    instruction. In this case we don't need to mark it as used
                        //    as it will be recreated.
                        //
                        // 2. Value is being created in current block dominator and used
                        //    before our instruction. In this case we must mark value as
                        //    used.
                        //
                        // TODO: Improve this to handle more cases where value gets recreated.
                        let creator   = creators[&input].label();
                        let recreated = target_label == creator;

                        if !recreated {
                            used[input.index()] = true;
                        }
                    }
                }
            }

            // We have computed all values which are being used in blocks
            // that are reachable from current label. These are common for
            // all instructions in this block. Now calculate per-instruction usage data.
            
            let block = &self.blocks[&label];

            // Go through every instruction and calculate used registers.
            for (inst_id, _) in block.iter().enumerate() {
                // Copy all used value from common data computed above.
                let mut used = used.clone();

                // Get all values which are used AFTER this instruction.
                for instruction in &block[inst_id + 1..] {
                    for input in instruction.read_values() {
                        used[input.index()] = true;
                    }
                }

                // Calculation for this location is now done.
                lifetimes.insert(Location::new(label, inst_id), used);
            }
        }

        lifetimes
    }

    fn liveness(&self, dominators: &Dominators) -> Liveness {
        let mut liveness = Liveness::default();

        let flow_incoming = self.flow_graph_incoming();
        let cx            = LivenessContext {
            function:      self,
            flow_incoming: &flow_incoming,
            dominators,
        };

        self.for_each_instruction(|location, instruction| {
            if let Some(value) = instruction.created_value() {
                // Create a new, empty liveness state for output value.
                assert!(liveness.values.insert(value, ValueLiveness::new(location)).is_none(),
                        "Value created multiple times.");
            }

            for input in instruction.read_values() {
                // Ignore all function arguments.
                if self.is_value_argument(input) {
                    continue;
                }

                // Get liveness state for this input value.
                let input_liveness = liveness.values.get_mut(&input)
                    .expect("Failed to get liveness state for value.");

                // Mark that this value is used at `location`.
                input_liveness.add_usage(location, &cx);
            }
        });

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

        super::dot::save_svg_graph(&dotgraph, &format!("graphs/interference_{}.svg",
                                                       self.prototype.name));
    }

    fn coalesce(&self, liveness: &Liveness) -> Map<Value, VirtualRegister> {
        // Given a sequence:
        // %5 = add %4, %1
        // If it's the last usage of %4 then %5 and %4 should be allocated in the same
        // register. To make this possible we an make abstracion over Values - VirtualRegisters.
        // In this case %4 and %5 will get assigned the same VirtualRegister.

        let mut value_registers = Map::default();
        let mut next_register   = VirtualRegister(0);

        let mut coalesce_values = |v1: Value, v2: Value| {
            // Try to assign the same VirtualRegister to both Values.
            match (value_registers.get(&v1).cloned(), value_registers.get(&v2).cloned()) {
                (Some(_), Some(_)) => {
                    // Either values are already coalesced or they are in different VRs.
                    // We cannot do anything here.
                },
                (Some(r), None) | (None, Some(r)) => {
                    // One Value has already assigned VR, make other one use the same VR.
                    value_registers.insert(v1, r);
                    value_registers.insert(v2, r);
                }
                (None, None) => {
                    let register  = next_register;
                    next_register = VirtualRegister(next_register.0 + 1);

                    // Assign the same new VR for both Values.
                    value_registers.insert(v1, register);
                    value_registers.insert(v2, register);
                }
            }
        };

        // Coalesce Values by assigning the same VirtualRegisters to them.
        self.for_each_instruction(|location, instruction| {
            if let Some(output) = instruction.created_value() {
                if let Some(&input) = instruction.read_values().get(0) {
                    // We cannot coalesce arguments.
                    if self.is_value_argument(input) {
                        return;
                    }

                    // If first operand dies after this instruction we can coalesce
                    // it with output Value.
                    if liveness.value_dies(location, input) {
                        coalesce_values(output, input);
                    }
                }
            }
        });

        // Values which are left will get unique VirtualRegisters.
        for value in 0..self.value_count() {
            let value = Value(value as u32);

            // If we already don't have VR for this Value, create and assign one.
            if value_registers.get(&value).is_none() {
                let register  = next_register;
                next_register = VirtualRegister(next_register.0 + 1);

                value_registers.insert(value, register);
            }
        }

        value_registers
    }

    pub(super) fn allocate_registers(&self, hardware_registers: usize) -> RegisterAllocation {
        let labels     = self.reachable_labels();
        let dominators = self.dominators();
        let liveness   = self.liveness(&dominators);

        // Coalesce values and create VirtualRegisters which will hold Values.
        let value_to_register = self.coalesce(&liveness);

        let mut register_to_values = Map::default();

        // Create reverse mapping from VR to Values.
        for (value, register) in &value_to_register {
            assert!(register_to_values.entry(*register)
                    .or_insert_with(Set::default)
                    .insert(*value));
        }

        // State of used values for each block.
        let mut block_alloc_state: Map<Label, Vec<Value>> =
            Map::new_with_capacity(self.blocks.len());

        // Entry block starts with empty state.
        block_alloc_state
            .entry(Label(0))
            .or_insert_with(Default::default);

        let get_entity = |value: Value| {
            // Register allocation entity is not a Value, it's a VirtualRegister.
            value_to_register[&value]
        };

        let mut interference = InterferenceGraph::default();

        for label in labels {
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

            // Process register usage for every instruction in the block.
            for (inst_id, instruction) in block.iter().enumerate() {
                let location = Location::new(label, inst_id);

                let mut to_free: Vec<Value> = Vec::new();

                // Get a list of all values which aren't used anymore and can be freed.
                for &value in block_allocs.iter() {
                    if liveness.value_dies(location, value) {
                        to_free.push(value);
                    }
                }

                // Free all queued values.
                for value in to_free {
                    // Get index of unused value.
                    let item = block_allocs.iter()
                        .position(|&x| x == value)
                        .unwrap();

                    block_allocs.remove(item);
                }

                if let Some(output) = instruction.created_value() {
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

        let coloring           = interference.color();
        let required_registers = coloring.color_list.len();

        if DEBUG_ALLOCATOR {
            println!("{}: Colored interference graph with {} colors. HR: {}.", 
                     self.prototype.name, coloring.color_list.len(), hardware_registers);

            // Dump colored interference graph to file.
            self.dump_interference_graph(&interference, &coloring,
                                         &register_to_values);
        }

        let colors = if required_registers > hardware_registers {
            // We can't fit all VRs in hardware registers. We need to move some VRs to
            // the memory. Get usage counts to figure out best candidates.

            let usage_counts = self.usage_counts();

            let mut usages: Map<Color, usize> = Map::default();

            for (register, &color) in coloring.vertex_color.iter() {
                for &value in &register_to_values[register] {
                    *usages.entry(color).or_insert(0) +=
                        usage_counts[value.index()] as usize;
                }
            }

            assert!(usages.len() == required_registers, "Color count mismatch.");

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
        let stack_slots = colors.len().saturating_sub(hardware_registers);

        let mut color_to_place = Map::default();
        let mut used_registers = Set::default();

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
        for (&value, &register) in &value_to_register {
            if let Some(&color) =  coloring.vertex_color.get(&register) {
                // Get place assigned to this color.
                let place = color_to_place[&color];

                assert!(value_to_place.insert(value, place).is_none(),
                        "Multiple places assigned to the value.");
            }

            // There is no coloring for this value. Either it's an argument
            // or this value is dead.
        }

        let mut arguments = Map::new_with_capacity(self.argument_values.len());

        // Fill in places of function arguments.
        for (index, argument) in self.argument_values.iter().enumerate() {
            arguments.insert(*argument, Place::Argument(index));
        }

        RegisterAllocation {
            allocation: value_to_place,
            slots:      stack_slots,
            used_regs:  used_registers,
            arguments,
        }
    }

    /*
    pub(super) fn allocate_registers(&self, hardware_registers: usize) -> RegisterAllocation {
        fn stack_pop_prefer(stack: &mut Vec<usize>, prefer: Option<usize>) -> Option<usize> {
            if let Some(prefer) = prefer {
                if let Some(idx) = stack.iter().position(|x| *x == prefer) {
                    stack.remove(idx);

                    return Some(prefer);
                }
            }

            stack.pop()
        }

        #[derive(Default, Clone)]
        struct FreePlaces {
            registers:   Vec<usize>,
            stack_slots: Vec<usize>,
        }

        let mut block_alloc_state:
            Map<Label, (Map<Value, Place>, FreePlaces)> =
                Map::new_with_capacity(self.blocks.len());

        let mut inst_alloc_state:
            Map<Location, Map<Value, Place>> =
                Map::default();

        {
            // At first all hardware registers are usable.

            let entry_state = block_alloc_state
                .entry(Label(0))
                .or_insert_with(Default::default);

            for index in (0..hardware_registers).rev() {
                entry_state.1.registers.push(index);
            }

        }

        let labels     = self.reachable_labels();
        let dominators = self.dominators();
        let lifetimes  = self.lifetimes();

        let mut next_slot = 0;
        let mut used_regs = Set::new_with_capacity(hardware_registers);

        for label in labels {
            // If there is not register allocation state for this block then take one
            // from immediate dominator (as we can only use values originating from it).
            #[allow(clippy::map_entry)]
            if !block_alloc_state.contains_key(&label) {
                let idom   = dominators[&label];
                let allocs = block_alloc_state[&idom].clone();

                block_alloc_state.insert(label, allocs);
            }

            let block_allocs = block_alloc_state.get_mut(&label).unwrap();
            let block        = &self.blocks[&label];

            inst_alloc_state.reserve(block.len());
            block_allocs.0.reserve(block.len() / 2);

            for (inst_id, inst) in block.iter().enumerate() {
                let location = Location::new(label, inst_id);

                let mut inst_allocs                  = block_allocs.0.clone();
                let mut to_free: Vec<(Value, Place)> = Vec::new();

                for (&value, &place) in block_allocs.0.iter() {
                    if !lifetimes[&location][value.index()] {
                        to_free.push((value, place));
                    }
                }

                for (value, place) in to_free {
                    if !matches!(place, Place::Argument(_)) {
                        block_allocs.0.remove(&value);
                    }

                    match place {
                        Place::StackSlot(value) => {
                            block_allocs.1.stack_slots.push(value);
                        }
                        Place::Register(value) => {
                            block_allocs.1.registers.push(value);
                        }
                        Place::Argument(_) => {
                        }
                    }
                }

                if let Some(output) = inst.created_value() {
                    // We will try to allocate output value at the same register as 
                    // first input. This will help to generate better code by backend.
                    let first_input = inst.read_values().get(0).and_then(|value| {
                        // Fix for arguments.
                        inst_allocs.get(&value).cloned()
                    });

                    let preg = if let Some(Place::Register(register)) = first_input {
                        Some(register)
                    } else {
                        None
                    };

                    let pslot = if let Some(Place::StackSlot(slot)) = first_input {
                        Some(slot)
                    } else {
                        None
                    };

                    let register = stack_pop_prefer(&mut block_allocs.1.registers, preg);

                    let place = if let Some(register) = register {
                        used_regs.insert(register);

                        Place::Register(register)
                    } else {
                        let slot = stack_pop_prefer(&mut block_allocs.1.stack_slots, pslot);

                        Place::StackSlot(slot.unwrap_or_else(|| {
                            let slot = next_slot;

                            next_slot += 1;

                            slot
                        }))
                    };

                    block_allocs.0.insert(output, place);
                    inst_allocs.insert(output, place);
                }

                assert!(inst_alloc_state.insert(location, inst_allocs).is_none(), 
                        "Multiple instruction allocation states.");
            }
        }

        let total = next_slot + used_regs.len();

        println!("Regalloc for {} required {} places.", self.prototype.name, total);

        let mut arguments = Map::new_with_capacity(self.argument_values.len());

        for (index, argument) in self.argument_values.iter().enumerate() {
            arguments.insert(*argument, Place::Argument(index));
        }

        RegisterAllocation {
            allocation: inst_alloc_state,
            slots:      next_slot,
            arguments,
            used_regs,
        }
    }
    */
}
