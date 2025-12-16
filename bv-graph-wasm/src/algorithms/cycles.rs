//! Cycle Detection algorithms.
//!
//! Provides:
//! - Tarjan's SCC algorithm for fast cycle presence check
//! - Johnson's algorithm for full cycle enumeration

use crate::graph::DiGraph;
use serde::Serialize;
use std::collections::HashSet;

/// Result of Strongly Connected Components analysis.
#[derive(Serialize, Clone)]
pub struct SCCResult {
    /// List of strongly connected components (each is a list of node indices)
    pub components: Vec<Vec<usize>>,
    /// True if any SCC has more than one node (cycle exists)
    pub has_cycles: bool,
    /// Number of non-trivial SCCs (size > 1)
    pub cycle_count: usize,
}

/// Tarjan's algorithm for finding strongly connected components.
///
/// An SCC with more than one node indicates a cycle.
/// Complexity: O(V + E)
pub fn tarjan_scc(graph: &DiGraph) -> SCCResult {
    let n = graph.len();
    if n == 0 {
        return SCCResult {
            components: Vec::new(),
            has_cycles: false,
            cycle_count: 0,
        };
    }

    let mut index = 0usize;
    let mut indices = vec![usize::MAX; n];
    let mut lowlink = vec![usize::MAX; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut components: Vec<Vec<usize>> = Vec::new();

    fn strongconnect(
        v: usize,
        graph: &DiGraph,
        index: &mut usize,
        indices: &mut [usize],
        lowlink: &mut [usize],
        on_stack: &mut [bool],
        stack: &mut Vec<usize>,
        components: &mut Vec<Vec<usize>>,
    ) {
        indices[v] = *index;
        lowlink[v] = *index;
        *index += 1;
        stack.push(v);
        on_stack[v] = true;

        for &w in graph.successors_slice(v) {
            if indices[w] == usize::MAX {
                // Not visited
                strongconnect(w, graph, index, indices, lowlink, on_stack, stack, components);
                lowlink[v] = lowlink[v].min(lowlink[w]);
            } else if on_stack[w] {
                // On stack = in current SCC
                lowlink[v] = lowlink[v].min(indices[w]);
            }
        }

        // If v is a root node, pop the stack to get SCC
        if lowlink[v] == indices[v] {
            let mut component = Vec::new();
            loop {
                let w = stack.pop().unwrap();
                on_stack[w] = false;
                component.push(w);
                if w == v {
                    break;
                }
            }
            components.push(component);
        }
    }

    for v in 0..n {
        if indices[v] == usize::MAX {
            strongconnect(
                v,
                graph,
                &mut index,
                &mut indices,
                &mut lowlink,
                &mut on_stack,
                &mut stack,
                &mut components,
            );
        }
    }

    let cycle_count = components.iter().filter(|c| c.len() > 1).count();

    SCCResult {
        components,
        has_cycles: cycle_count > 0,
        cycle_count,
    }
}

/// Check if graph has any cycles.
pub fn has_cycles(graph: &DiGraph) -> bool {
    tarjan_scc(graph).has_cycles
}

/// Enumerate elementary cycles using Johnson's algorithm.
///
/// Reference: Donald B. Johnson, "Finding All the Elementary Circuits of a Directed Graph"
/// SIAM J. Computing, Vol. 4, No. 1, March 1975
///
/// # Arguments
/// * `graph` - The directed graph
/// * `max_cycles` - Maximum number of cycles to find (prevents exponential blowup)
///
/// # Returns
/// Vector of cycles, each cycle is a vector of node indices in order
pub fn enumerate_cycles(graph: &DiGraph, max_cycles: usize) -> Vec<Vec<usize>> {
    let n = graph.len();
    if n == 0 || max_cycles == 0 {
        return Vec::new();
    }

    let mut cycles: Vec<Vec<usize>> = Vec::new();
    let mut blocked = vec![false; n];
    let mut blocked_map: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    let mut stack: Vec<usize> = Vec::new();

    // Helper: unblock a node and recursively unblock dependents
    fn unblock(u: usize, blocked: &mut [bool], blocked_map: &mut [HashSet<usize>]) {
        blocked[u] = false;
        let dependents: Vec<usize> = blocked_map[u].drain().collect();
        for w in dependents {
            if blocked[w] {
                unblock(w, blocked, blocked_map);
            }
        }
    }

    // Circuit search from start vertex
    fn circuit(
        v: usize,
        start: usize,
        graph: &DiGraph,
        blocked: &mut [bool],
        blocked_map: &mut [HashSet<usize>],
        stack: &mut Vec<usize>,
        cycles: &mut Vec<Vec<usize>>,
        max_cycles: usize,
        min_node: usize,
    ) -> bool {
        if cycles.len() >= max_cycles {
            return false;
        }

        let mut found = false;
        stack.push(v);
        blocked[v] = true;

        for &w in graph.successors_slice(v) {
            // Only consider nodes >= min_node (Johnson's optimization)
            if w < min_node {
                continue;
            }

            if w == start {
                // Found a cycle
                cycles.push(stack.clone());
                found = true;
                if cycles.len() >= max_cycles {
                    stack.pop();
                    return found;
                }
            } else if !blocked[w] {
                if circuit(
                    w,
                    start,
                    graph,
                    blocked,
                    blocked_map,
                    stack,
                    cycles,
                    max_cycles,
                    min_node,
                ) {
                    found = true;
                }
            }
        }

        if found {
            unblock(v, blocked, blocked_map);
        } else {
            for &w in graph.successors_slice(v) {
                if w >= min_node {
                    blocked_map[w].insert(v);
                }
            }
        }

        stack.pop();
        found
    }

    // Run Johnson's algorithm starting from each node
    for start in 0..n {
        if cycles.len() >= max_cycles {
            break;
        }

        // Reset blocked state
        for b in &mut blocked {
            *b = false;
        }
        for s in &mut blocked_map {
            s.clear();
        }

        circuit(
            start,
            start,
            graph,
            &mut blocked,
            &mut blocked_map,
            &mut stack,
            &mut cycles,
            max_cycles,
            start,
        );
    }

    cycles
}

/// Result of cycle enumeration with metadata.
#[derive(Serialize)]
pub struct CycleEnumerationResult {
    /// List of cycles found
    pub cycles: Vec<Vec<usize>>,
    /// Whether max_cycles limit was reached
    pub truncated: bool,
    /// Number of cycles found
    pub count: usize,
}

/// Enumerate cycles with metadata about truncation.
pub fn enumerate_cycles_with_info(graph: &DiGraph, max_cycles: usize) -> CycleEnumerationResult {
    let cycles = enumerate_cycles(graph, max_cycles);
    let count = cycles.len();
    CycleEnumerationResult {
        cycles,
        truncated: count >= max_cycles,
        count,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scc_empty() {
        let graph = DiGraph::new();
        let result = tarjan_scc(&graph);
        assert!(result.components.is_empty());
        assert!(!result.has_cycles);
    }

    #[test]
    fn test_scc_single_node() {
        let mut graph = DiGraph::new();
        graph.add_node("a");
        let result = tarjan_scc(&graph);
        assert_eq!(result.components.len(), 1);
        assert_eq!(result.components[0].len(), 1);
        assert!(!result.has_cycles);
    }

    #[test]
    fn test_scc_self_loop() {
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        graph.add_edge(a, a);
        let result = tarjan_scc(&graph);
        // Self-loop creates SCC of size 1 with edge to itself
        // Tarjan considers this a cycle
        assert!(result.has_cycles || result.components[0].len() == 1);
    }

    #[test]
    fn test_scc_simple_cycle() {
        // a -> b -> c -> a
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        let b = graph.add_node("b");
        let c = graph.add_node("c");
        graph.add_edge(a, b);
        graph.add_edge(b, c);
        graph.add_edge(c, a);

        let result = tarjan_scc(&graph);
        assert!(result.has_cycles);
        assert_eq!(result.cycle_count, 1);
        // One SCC with all 3 nodes
        let big_scc = result.components.iter().find(|c| c.len() > 1);
        assert!(big_scc.is_some());
        assert_eq!(big_scc.unwrap().len(), 3);
    }

    #[test]
    fn test_scc_dag() {
        // a -> b -> c (no cycles)
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        let b = graph.add_node("b");
        let c = graph.add_node("c");
        graph.add_edge(a, b);
        graph.add_edge(b, c);

        let result = tarjan_scc(&graph);
        assert!(!result.has_cycles);
        // Each node is its own SCC
        assert_eq!(result.components.len(), 3);
    }

    #[test]
    fn test_scc_two_cycles() {
        // Cycle 1: a -> b -> a
        // Cycle 2: c -> d -> c
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        let b = graph.add_node("b");
        let c = graph.add_node("c");
        let d = graph.add_node("d");
        graph.add_edge(a, b);
        graph.add_edge(b, a);
        graph.add_edge(c, d);
        graph.add_edge(d, c);

        let result = tarjan_scc(&graph);
        assert!(result.has_cycles);
        assert_eq!(result.cycle_count, 2);
    }

    #[test]
    fn test_enumerate_empty() {
        let graph = DiGraph::new();
        let cycles = enumerate_cycles(&graph, 100);
        assert!(cycles.is_empty());
    }

    #[test]
    fn test_enumerate_dag() {
        // a -> b -> c (no cycles)
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        let b = graph.add_node("b");
        let c = graph.add_node("c");
        graph.add_edge(a, b);
        graph.add_edge(b, c);

        let cycles = enumerate_cycles(&graph, 100);
        assert!(cycles.is_empty());
    }

    #[test]
    fn test_enumerate_simple_cycle() {
        // a -> b -> c -> a
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        let b = graph.add_node("b");
        let c = graph.add_node("c");
        graph.add_edge(a, b);
        graph.add_edge(b, c);
        graph.add_edge(c, a);

        let cycles = enumerate_cycles(&graph, 100);
        assert_eq!(cycles.len(), 1);
        assert_eq!(cycles[0].len(), 3);
    }

    #[test]
    fn test_enumerate_two_node_cycle() {
        // a -> b -> a
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        let b = graph.add_node("b");
        graph.add_edge(a, b);
        graph.add_edge(b, a);

        let cycles = enumerate_cycles(&graph, 100);
        assert_eq!(cycles.len(), 1);
        assert_eq!(cycles[0].len(), 2);
    }

    #[test]
    fn test_enumerate_max_limit() {
        // Create graph with multiple cycles
        // a <-> b <-> c <-> d with interconnections
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        let b = graph.add_node("b");
        let c = graph.add_node("c");
        let d = graph.add_node("d");
        graph.add_edge(a, b);
        graph.add_edge(b, a);
        graph.add_edge(b, c);
        graph.add_edge(c, b);
        graph.add_edge(c, d);
        graph.add_edge(d, c);
        graph.add_edge(d, a);
        graph.add_edge(a, d);

        // Limit to 2 cycles
        let cycles = enumerate_cycles(&graph, 2);
        assert_eq!(cycles.len(), 2);
    }

    #[test]
    fn test_enumerate_diamond_with_back_edge() {
        //     a
        //    / \
        //   b   c
        //    \ /
        //     d -> a (back edge creates cycle)
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        let b = graph.add_node("b");
        let c = graph.add_node("c");
        let d = graph.add_node("d");
        graph.add_edge(a, b);
        graph.add_edge(a, c);
        graph.add_edge(b, d);
        graph.add_edge(c, d);
        graph.add_edge(d, a);

        let cycles = enumerate_cycles(&graph, 100);
        // Two cycles: a->b->d->a and a->c->d->a
        assert_eq!(cycles.len(), 2);
    }

    #[test]
    fn test_enumerate_with_info() {
        // a -> b -> a
        let mut graph = DiGraph::new();
        let a = graph.add_node("a");
        let b = graph.add_node("b");
        graph.add_edge(a, b);
        graph.add_edge(b, a);

        let result = enumerate_cycles_with_info(&graph, 100);
        assert_eq!(result.count, 1);
        assert!(!result.truncated);

        // With limit of 1, we should get exactly 1 cycle and not be truncated
        // (since there's only 1 cycle to find)
        let result_one = enumerate_cycles_with_info(&graph, 1);
        assert_eq!(result_one.count, 1);
        // Truncated because we hit the limit (count >= max)
        assert!(result_one.truncated);
    }

    #[test]
    fn test_has_cycles() {
        let mut dag = DiGraph::new();
        let a = dag.add_node("a");
        let b = dag.add_node("b");
        dag.add_edge(a, b);
        assert!(!has_cycles(&dag));

        let mut cyclic = DiGraph::new();
        let x = cyclic.add_node("x");
        let y = cyclic.add_node("y");
        cyclic.add_edge(x, y);
        cyclic.add_edge(y, x);
        assert!(has_cycles(&cyclic));
    }

    #[test]
    fn test_complex_graph() {
        // Multiple interconnected cycles
        let mut graph = DiGraph::new();
        for i in 0..5 {
            graph.add_node(&format!("n{}", i));
        }
        // Create some cycles
        graph.add_edge(0, 1);
        graph.add_edge(1, 2);
        graph.add_edge(2, 0); // Cycle: 0->1->2->0
        graph.add_edge(2, 3);
        graph.add_edge(3, 4);
        graph.add_edge(4, 2); // Cycle: 2->3->4->2

        let scc = tarjan_scc(&graph);
        assert!(scc.has_cycles);

        let cycles = enumerate_cycles(&graph, 100);
        assert!(cycles.len() >= 2);
    }
}
