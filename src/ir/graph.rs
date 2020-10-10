use std::collections::VecDeque;

use super::{FunctionData, Label, Map, Set};

pub type FlowGraph = Map<Label, Set<Label>>;

impl FunctionData {
    fn for_each_label_bfs(
        &self,
        start:         Label,
        include_start: bool,
        mut callback:  impl FnMut(Label),
    ) {
        let mut visited = Set::new();
        let mut queue   = VecDeque::new();

        queue.push_back(start);

        let mut is_first       = true;
        let mut included_start = false;

        while !queue.is_empty() {
            let label = queue.pop_front().unwrap();

            let mut no_callback = false;

            if !is_first && !include_start && label == start && !included_start {
                callback(start);
                included_start = true;
                no_callback    = true;
            }

            if !visited.insert(label) {
                continue;
            }

            if (!is_first || include_start) && !no_callback {
                callback(label);
            }

            is_first = false;

            for target in self.targets(label) {
                queue.push_back(target);
            }
        }
    }

    pub(super) fn traverse_bfs(&self, start: Label, include_start: bool) -> Vec<Label> {
        let mut result = Vec::new();

        self.for_each_label_bfs(start, include_start, |label| {
            result.push(label);
        });

        result
    }

    pub(super) fn flow_graph_outgoing(&self) -> FlowGraph {
        let mut flow_graph = Map::new();

        self.for_each_label_bfs(Label(0), true, |label| {
            let entry = flow_graph.entry(label).or_insert_with(Set::new);

            for target in self.targets(label) {
                entry.insert(target);
            }
        });

        flow_graph
    }

    pub(super) fn flow_graph_incoming(&self) -> FlowGraph {
        let mut flow_graph = Map::new();

        self.for_each_label_bfs(Label(0), true, |label| {
            for target in self.targets(label) {
                flow_graph.entry(target)
                    .or_insert_with(Set::new)
                    .insert(label);
            }
        });

        flow_graph.entry(Label(0)).or_insert_with(Set::new);

        flow_graph
    }
}
