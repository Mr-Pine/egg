use crate::Justification::{Congruence, Rule};
use crate::explain::{Connection, ExplainCache, ExplainNodes, NodeExplanationCache};
use crate::unionfind::UnionFind;
use crate::util::{HashMap, HashSet};
use crate::{
    Analysis, EGraph, Explanation, Id, IterationData, Language, PatternAst, RecExpr, Runner, Subst,
    TreeExplanation, TreeTerm,
};
use alloc::rc::Rc;
use core::fmt::Display;
use std::collections::BinaryHeap;

impl<L, N, IterData> Runner<L, N, IterData>
where
    L: Language + Display,
    N: Analysis<L>,
    IterData: IterationData<L, N>,
{
    pub fn explain_equivalence_dijkstra(
        &mut self,
        left: &RecExpr<L>,
        right: &RecExpr<L>,
    ) -> Explanation<L> {
        self.egraph.explain_equivalence_dijkstra(left, right)
    }
}

impl<L: Language + Display, N: Analysis<L>> EGraph<L, N> {
    fn explain_equivalence_dijkstra(
        &mut self,
        left_expr: &RecExpr<L>,
        right_expr: &RecExpr<L>,
    ) -> Explanation<L> {
        let left = self.add_expr_uncanonical(left_expr);
        let right = self.add_expr_uncanonical(right_expr);

        self.explain_id_equivalence_dijkstra(left, right)
    }

    /// Get an explanation for why an expression matches a pattern.
    pub fn explain_matches_dijkstra(
        &mut self,
        left_expr: &RecExpr<L>,
        right_pattern: &PatternAst<L>,
        subst: &Subst,
    ) -> Explanation<L> {
        let left = self.add_expr_uncanonical(left_expr);
        let right = self.add_instantiation_noncanonical(right_pattern, subst);

        if self.find(left) != self.find(right) {
            panic!(
                "Tried to explain equivalence between non-equal terms {:?} and {:?}",
                left_expr, right_pattern
            );
        }
        if let Some(explain) = &mut self.explain {
            explain
                .with_nodes(&self.nodes)
                .explain_equivalence_dijkstra(left, right, (&self.unionfind).into())
        } else {
            panic!(
                "Use runner.with_explanations_enabled() or egraph.with_explanations_enabled() before running to get explanations."
            );
        }
    }

    fn explain_id_equivalence_dijkstra(&mut self, left: Id, right: Id) -> Explanation<L> {
        if self.find(left) != self.find(right) {
            panic!(
                "Tried to explain equivalence between non-equal terms {:?} and {:?}",
                self.id_to_expr(left),
                self.id_to_expr(right)
            );
        }
        if let Some(explain) = &mut self.explain {
            explain
                .with_nodes(&self.nodes)
                .explain_equivalence_dijkstra(left, right, (&self.unionfind).into())
        } else {
            panic!(
                "Use runner.with_explanations_enabled() or egraph.with_explanations_enabled() before running to get explanations."
            )
        }
    }
}

struct EClassUnionFind<'a>(&'a UnionFind);

impl<'a> EClassUnionFind<'a> {
    fn get_eclass_cannon(&self, enode: Id) -> Id {
        self.0.find(enode)
    }

    fn to_congruence_cannon<L: Language>(&self, node: L) -> L {
        node.map_children(|child| self.get_eclass_cannon(child))
    }
}

impl<'a> From<&'a UnionFind> for EClassUnionFind<'a> {
    fn from(unionfind: &'a UnionFind) -> Self {
        Self(unionfind)
    }
}

impl<'x, L: Language + Display> ExplainNodes<'x, L> {
    /// Pick a representative term for a given Id.
    ///
    /// Calling this function on an uncanonical `Id` returns a representative based on the how it
    /// was obtained (see [`add_uncanoncial`](EGraph::add_uncanonical),
    /// [`add_expr_uncanonical`](EGraph::add_expr_uncanonical))
    fn id_to_expr(&self, id: Id) -> RecExpr<L> {
        let mut res = Default::default();
        let mut cache = Default::default();
        self.id_to_expr_internal(&mut res, id, &mut cache);
        res
    }

    fn id_to_expr_internal(
        &self,
        res: &mut RecExpr<L>,
        node_id: Id,
        cache: &mut HashMap<Id, Id>,
    ) -> Id {
        if let Some(existing) = cache.get(&node_id) {
            return *existing;
        }
        let new_node = self
            .node(node_id)
            .clone()
            .map_children(|child| self.id_to_expr_internal(res, child, cache));
        let res_id = res.add(new_node);
        cache.insert(node_id, res_id);
        res_id
    }

    fn explain_enodes_dijkstra(
        &self,
        left: Id,
        right: Id,
        dijkstra_state: &DijkstraState<L>,
        cache: &mut ExplainCache<L>,
        node_explanation_cache: &mut NodeExplanationCache<L>,
    ) -> TreeExplanation<L> {
        let mut proof = vec![self.node_to_explanation_dijkstra(left, node_explanation_cache)];
        let path = dijkstra_state
            .reconstruct_path(left, right)
            .expect("Path not found");

        for edge in path {
            proof.push(self.explain_adjacent_dijkstra(
                edge,
                dijkstra_state,
                cache,
                node_explanation_cache,
            ));
        }
        proof
    }

    fn node_to_explanation_dijkstra(
        &self,
        node_id: Id,
        cache: &mut NodeExplanationCache<L>,
    ) -> Rc<TreeTerm<L>> {
        if let Some(existing) = cache.get(&node_id) {
            existing.clone()
        } else {
            let node = self.node(node_id).clone();
            let children = node.fold(vec![], |mut sofar, child| {
                sofar.push(vec![self.node_to_explanation_dijkstra(child, cache)]);
                sofar
            });
            let res = Rc::new(TreeTerm::new(node, children));
            cache.insert(node_id, res.clone());
            res
        }
    }

    fn explain_adjacent_dijkstra(
        &self,
        connection: Connection,
        dijkstra_state: &DijkstraState<L>,
        cache: &mut ExplainCache<L>,
        node_explanation_cache: &mut NodeExplanationCache<L>,
    ) -> Rc<TreeTerm<L>> {
        let fingerprint = (connection.current, connection.next);

        if let Some(answer) = cache.get(&fingerprint) {
            return answer.clone();
        }

        let term = match connection.justification {
            Rule(name) => {
                let mut rewritten = (*self
                    .node_to_explanation_dijkstra(connection.next, node_explanation_cache))
                .clone();
                if connection.is_rewrite_forward {
                    rewritten.forward_rule = Some(name);
                } else {
                    rewritten.backward_rule = Some(name);
                }

                rewritten.current = connection.next;
                rewritten.last = connection.current;

                Rc::new(rewritten)
            }
            Congruence => {
                // add the children proofs to the last explanation
                let current_node = self.node(connection.current);
                let next_node = self.node(connection.next);
                assert!(current_node.matches(next_node));
                let mut subproofs = vec![];

                for (left_child, right_child) in current_node
                    .children()
                    .iter()
                    .zip(next_node.children().iter())
                {
                    subproofs.push(self.explain_enodes_dijkstra(
                        *left_child,
                        *right_child,
                        dijkstra_state,
                        cache,
                        node_explanation_cache,
                    ));
                }
                Rc::new(TreeTerm::new(current_node.clone(), subproofs))
            }
        };

        cache.insert(fingerprint, term.clone());

        term
    }

    fn explain_equivalence_dijkstra(
        &mut self,
        left: Id,
        right: Id,
        unionfind: EClassUnionFind,
    ) -> Explanation<L> {
        let mut dijkstra_state = DijkstraState::new(unionfind, self.nodes);
        let distance = self.recursive_dijkstra(left, right, &mut dijkstra_state, 0);
        debug_assert!(
            distance.is_some(),
            "Dijkstra's algorithm failed to find a path between {} and {}",
            self.id_to_expr(left),
            self.id_to_expr(right)
        );

        let mut cache = Default::default();
        let mut enode_cache = Default::default();
        Explanation::new(self.explain_enodes_dijkstra(
            left,
            right,
            &dijkstra_state,
            &mut cache,
            &mut enode_cache,
        ))
    }

    /// PLAN:
    /// 1. Sucht man sich alle Knoten
    /// 2. Hat man eine Distance memo point-to-point (n²)
    /// 3. Macht man eins Dijkstra
    /// 4. Bei einem Funktionssymbol synthetisiert man congruence edges zu allen anderen Knoten dieser Kongruenzklasse (`cannon`:  node nehmen und children zu eclass union find root), **if** die Kante zu mir nicht eine Kongruenzkante
    ///    1. Wenn kante blackholed, skip
    ///    2. Macht man einmal sub-dijkstra zwischen deren Argumenten
    ///       1. Blackhole diese Kante in distance memo
    ///    3. Nutze das als Gewicht für die Kante => Relaxiere Kante
    ///    4. Add to priority queue
    /// 5. Für alle normalen Nachbarn
    ///   1. Relaxiere Kante
    ///   2. Add to priority queue
    fn recursive_dijkstra(
        &mut self,
        start: Id,
        end: Id,
        dijkstra_state: &mut DijkstraState<L>,
        depth: usize,
    ) -> Option<usize> {
        if start == end {
            return Some(0);
        } else if let Some(distance) = dijkstra_state.get_distance(start, end) {
            return Some(distance);
        }

        let mut prio_queue = BinaryHeap::<QueueEntry>::new();
        prio_queue.push(QueueEntry {
            node: start,
            distance: 0,
            reached_by_congruence: false,
        });

        let mut explored = HashSet::default();

        while let Some(QueueEntry {
            node,
            distance,
            reached_by_congruence,
        }) = prio_queue.pop()
        {
            // If we explore the end, we're done.
            if node == end {
                break;
            }

            // Only explore nodes we haven't explored yet.
            if !explored.insert(node) {
                continue;
            }

            let mut edges = self.explainfind[usize::from(node)]
                .neighbors
                .clone()
                .into_iter()
                .filter(|e| e.justification != Congruence) // We filter out congruence edges here. They'll be generated later.
                .collect::<HashSet<_>>();
            if !reached_by_congruence {
                // If this node was not reached by a congruence edge then generate outgoing
                // congruence edges. We can omit these if we were reached by a congruence
                // edge since congruence is transitive.
                let congruent_nodes =
                    dijkstra_state.get_congruent_neighbors(node, || self.find_all_enodes(node));
                for congruent_node in congruent_nodes {
                    let connection = Connection {
                        current: node,
                        next: congruent_node,
                        justification: Congruence,
                        is_rewrite_forward: true,
                    };
                    edges.insert(connection);
                }
            }

            'edge_loop: for edge in edges {
                let target = edge.next;
                let justification = edge.justification.clone();

                let distance = match &justification {
                    Rule(_) => distance + 1,
                    Congruence => {
                        if dijkstra_state.is_blackholed(node, target) {
                            continue; // Don't explore blackholed edges.
                        }

                        dijkstra_state.blackhole_congruent_edge(node, target);

                        let mut distance = 0;

                        let child_pairs = self
                            .node(node)
                            .children()
                            .iter()
                            .copied()
                            .zip(self.node(target).children().iter().copied())
                            .collect::<Vec<_>>();
                        for (child_start, child_target) in child_pairs {
                            let Some(child_distance) = self.recursive_dijkstra(
                                child_start,
                                child_target,
                                dijkstra_state,
                                depth + 1,
                            ) else {
                                dijkstra_state.whitehole_congruent_edge(node, target);
                                continue 'edge_loop;
                            };
                            distance += child_distance;
                        }

                        dijkstra_state.whitehole_congruent_edge(node, target);
                        distance
                    }
                };

                let distance_entry = DistanceEntry {
                    distance,
                    last_edge: edge,
                };

                if dijkstra_state.insert_distance(start, target, distance_entry) {
                    prio_queue.push(QueueEntry {
                        node: target,
                        distance,
                        reached_by_congruence: justification == Congruence,
                    });
                }
            }
        }

        dijkstra_state.get_distance(start, end)
    }
}

struct QueueEntry {
    node: Id,
    distance: usize,
    reached_by_congruence: bool,
}

impl QueueEntry {
    fn comparable(&self) -> (usize, bool, Id) {
        (self.distance, !self.reached_by_congruence, self.node)
    }
}

impl PartialEq<Self> for QueueEntry {
    fn eq(&self, other: &Self) -> bool {
        self.comparable() == other.comparable()
    }
}

impl Eq for QueueEntry {}

impl Ord for QueueEntry {
    /// Reverse order, so that the smallest distance is at the top of the queue.
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.comparable().cmp(&other.comparable()).reverse()
    }
}

impl PartialOrd for QueueEntry {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

struct DistanceEntry {
    distance: usize,
    last_edge: Connection,
}

struct DijkstraState<'a, L: Language> {
    distances: HashMap<(Id, Id), DistanceEntry>,
    unionfind: EClassUnionFind<'a>,
    nodes: &'a [L],
    congruence_map: HashMap<L, Vec<Id>>,
    black_holes: HashSet<(Id, Id)>,
}

impl<'a, L: Language + Display> DijkstraState<'a, L> {
    fn new(unionfind: EClassUnionFind<'a>, nodes: &'a [L]) -> Self {
        Self {
            distances: Default::default(),
            unionfind,
            nodes,
            congruence_map: Default::default(),
            black_holes: Default::default(),
        }
    }

    /// Query the currently best distance from `from` to `to`.
    fn get_distance(&self, from: Id, to: Id) -> Option<usize> {
        self.distances.get(&(from, to)).map(|entry| entry.distance)
    }

    /// Insert a new distance from `from` to `to` if better than the current one.
    ///
    /// Returns whether the value was updated.
    fn insert_distance(&mut self, from: Id, to: Id, distance_entry: DistanceEntry) -> bool {
        let current_distance = self.get_distance(from, to);
        if let Some(current_distance) = current_distance
            && distance_entry.distance < current_distance
        {
            return false;
        }
        self.distances.insert((from, to), distance_entry);
        true
    }

    fn reconstruct_path(&self, from: Id, to: Id) -> Option<Vec<Connection>> {
        let mut current = to;
        let mut edges = vec![];
        while current != from {
            let last_edge = self
                .distances
                .get(&(from, current))
                .as_ref()?
                .last_edge
                .clone();
            current = last_edge.current;
            edges.push(last_edge);
        }

        edges.reverse();
        Some(edges)
    }

    /// Get all different nodes in the same congruence class
    ///
    /// * `get_eclass_nodes` is called when there is no cached entry for this
    ///   enode, and should return all nodes in the same eclass as `enode`.
    fn get_congruent_neighbors<F: FnOnce() -> HashSet<Id>>(
        &mut self,
        enode: Id,
        get_eclass_nodes: F,
    ) -> impl Iterator<Item = Id> {
        let node = self.nodes[usize::from(enode)].clone();
        let cannon = self.unionfind.to_congruence_cannon(node);

        if !self.congruence_map.contains_key(&cannon) {
            let eclass_nodes = get_eclass_nodes();
            for node in eclass_nodes {
                let cannon = self
                    .unionfind
                    .to_congruence_cannon(self.nodes[usize::from(node)].clone());
                self.congruence_map.entry(cannon).or_default().push(node);
            }
        }

        self.congruence_map
            .get(&cannon)
            .unwrap()
            .iter()
            .copied()
            .filter(move |n| *n != enode)
    }

    fn blackhole_congruent_edge(&mut self, start: Id, end: Id) {
        debug_assert!(!self.black_holes.contains(&(start, end)));
        self.black_holes.insert((start, end));
    }

    fn whitehole_congruent_edge(&mut self, start: Id, end: Id) {
        debug_assert!(self.black_holes.contains(&(start, end)));
        self.black_holes.remove(&(start, end));
    }

    fn is_blackholed(&self, start: Id, end: Id) -> bool {
        self.black_holes.contains(&(start, end))
    }
}
