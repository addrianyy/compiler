use std::collections::VecDeque;

use super::{FunctionData, Label, Map, Set, CapacityExt};

pub type FlowGraph  = Map<Label, Set<Label>>;
pub type Dominators = Map<Label, Label>;

impl FunctionData {
    fn preferred_capacity(&self, start: Label) -> usize {
        if start == self.entry() {
            self.blocks.len()
        } else {
            0
        }
    }

    fn traverse_dfs_postorder(&self, start: Label) -> Vec<Label> {
        let capacity = self.preferred_capacity(start);

        let mut result   = Vec::with_capacity(capacity);
        let mut stack    = Vec::with_capacity(capacity / 4);
        let mut visited  = Set::new_with_capacity(capacity);
        let mut finished = Set::new_with_capacity(capacity);

        stack.push(start);

        while let Some(&label) = stack.last() {
            if visited.insert(label) {
                for target in self.targets(label) {
                    if !visited.contains(&target) {
                        stack.push(target);
                    }
                }
            } else {
                stack.pop();

                if finished.insert(label) {
                    result.push(label);
                }
            }
        }

        result
    }

    fn intersect(dominators: &[usize], mut finger1: usize, mut finger2: usize) -> usize {
        use std::cmp::Ordering;

        loop {
            match finger1.cmp(&finger2) {
                Ordering::Less    => finger1 = dominators[finger1],
                Ordering::Greater => finger2 = dominators[finger2],
                Ordering::Equal   => return finger1,
            }
        }
    }

    pub(super) fn dominators(&self) -> Dominators {
        let root = self.entry();

        let postorder = self.traverse_dfs_postorder(root);
        let length    = postorder.len();
        let root_idx  = length - 1;

        assert!(length > 0);
        assert_eq!(postorder[root_idx], root);

        let predecessors_map: Vec<Vec<usize>> = {
            let mut predecessors_map = self.flow_graph_incoming();

            let label_to_index: Map<Label, usize> = postorder
                .iter()
                .enumerate()
                .map(|(idx, &label)| (label, idx))
                .collect();

            postorder
                .iter()
                .map(|label| {
                    predecessors_map
                        .remove(label)
                        .map(|predecessors| {
                            predecessors
                                .into_iter()
                                .map(|p| *label_to_index.get(&p).unwrap())
                                .collect()
                        })
                        .unwrap_or_else(Vec::new)
                })
                .collect()
        };

        const UNDEFINED: usize = usize::MAX;

        let mut dominators = vec![UNDEFINED; length];
        dominators[root_idx] = root_idx;

        let mut changed = true;

        while changed {
            changed = false;

            for idx in (0..length - 1).rev() {
                assert_ne!(postorder[idx], root);

                let new_idom_idx = {
                    let mut predecessors = predecessors_map[idx]
                        .iter()
                        .filter(|&&p| dominators[p] != UNDEFINED);

                    let new_idom_idx = predecessors.next().unwrap();

                    predecessors.fold(*new_idom_idx, |new_idom_idx, &predecessor_idx| {
                        Self::intersect(&dominators, new_idom_idx, predecessor_idx)
                    })
                };

                assert!(new_idom_idx < length);

                if new_idom_idx != dominators[idx] {
                    dominators[idx] = new_idom_idx;
                    changed = true;
                }
            }
        }

        assert!(dominators.iter().all(|&dom| dom != UNDEFINED));

        dominators
            .into_iter()
            .enumerate()
            .filter(|(idx, _)| *idx != root_idx)
            .map(|(idx, dom_idx)| (postorder[idx], postorder[dom_idx]))
            .collect()
    }

    fn for_each_label_bfs(
        &self,
        start:         Label,
        include_start: bool,
        mut callback:  impl FnMut(Label),
    ) {
        let capacity = self.preferred_capacity(start);

        let mut visited = Set::new_with_capacity(capacity);
        let mut queue   = VecDeque::with_capacity(capacity / 4);

        queue.push_back(start);

        let mut is_first       = true;
        let mut included_start = false;

        while let Some(label) = queue.pop_front() {
            let mut no_callback = false;

            if is_first {
                assert_eq!(label, start, "Current label must be start if this \
                           is first iteration.");
            }

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
        let mut result = Vec::with_capacity(self.preferred_capacity(start));

        self.for_each_label_bfs(start, include_start, |label| {
            result.push(label);
        });

        result
    }

    pub(super) fn flow_graph_outgoing(&self) -> FlowGraph {
        let mut flow_graph = Map::new_with_capacity(self.blocks.len());

        self.for_each_label_bfs(self.entry(), true, |label| {
            let entry = flow_graph.entry(label).or_insert_with(Set::default);

            for target in self.targets(label) {
                entry.insert(target);
            }
        });

        flow_graph
    }

    pub(super) fn flow_graph_incoming(&self) -> FlowGraph {
        let mut flow_graph = Map::new_with_capacity(self.blocks.len());

        self.for_each_label_bfs(self.entry(), true, |label| {
            for target in self.targets(label) {
                flow_graph.entry(target)
                    .or_insert_with(Set::default)
                    .insert(label);
            }
        });

        flow_graph.entry(self.entry()).or_insert_with(Set::default);

        flow_graph
    }

    pub(super) fn reachable_labels(&self) -> Vec<Label> {
        self.traverse_bfs(self.entry(), true)
    }

    pub(super) fn reachable_labels_dfs(&self) -> Vec<Label> {
        let mut visited = Set::new_with_capacity(self.blocks.len());
        let mut stack   = Vec::with_capacity(self.blocks.len() / 4);
        let mut labels  = Vec::with_capacity(self.blocks.len());

        stack.push(self.entry());

        while let Some(label) = stack.pop() {
            if !visited.insert(label) {
                continue;
            }

            labels.push(label);

            // It is beneficial for codegen to fallthrough to the true label.
            for target in self.targets(label).into_iter().rev() {
                stack.push(target);
            }
        }

        labels
    }
}
