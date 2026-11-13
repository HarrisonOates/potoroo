//! Per-variable token flow for FDR POCL plans.
//!
//! The history of a variable in a sequential plan is a chain of *segments*:
//! the initial value, then one segment per write. Every segment except the
//! last is ended by exactly one writer, which needs the segment's value when
//! it has a precondition on the variable. So, counting a token per segment,
//! each committed step that writes `v` from `p` to `q` consumes a token at `p`
//! and produces one at `q`; the initial state produces one at `init(v)`; a goal
//! `v = g` consumes the final token at `g`. A writer with no precondition on
//! `v` consumes a token of any value, as does the final segment when `v` has
//! no goal.
//!
//! For the committed steps, the balance per value is fixed. A completion adds
//! steps, each moving a token along an edge of `v`'s domain transition graph,
//! until every value balances. The cheapest such movement is a transportation
//! problem from surplus values to deficit values, with domain-transition-graph
//! distances as costs. Summing it over variables gives a plan-space analogue
//! of the causal-graph family of state heuristics that, unlike additive costs,
//! knows a value produced once can be consumed once.
//!
//! Orderings and the other variables' preconditions are relaxed (the latter
//! priced at their additive costs from the initial state), so a variable with
//! no feasible flow proves the plan has no completion.

use std::cell::RefCell;

use crate::fdr::{Fact, Task};

struct VariableGraph {
    /// `edges[p]`: `(q, cost)` for the cheapest transition from value `p`.
    edges: Vec<Vec<(usize, f32)>>,
    /// `(q, cost)` for writes with no precondition on the variable.
    free: Vec<(usize, f32)>,
    /// Lazily computed single-source distances, one row per source value.
    dist: RefCell<Vec<Option<Box<[f32]>>>>,
}

impl VariableGraph {
    fn distance(&self, from: usize, to: usize) -> f32 {
        let mut rows = self.dist.borrow_mut();
        if rows[from].is_none() {
            rows[from] = Some(self.dijkstra(from));
        }
        rows[from].as_ref().unwrap()[to]
    }

    fn dijkstra(&self, from: usize) -> Box<[f32]> {
        let n = self.edges.len();
        let mut dist = vec![f32::INFINITY; n];
        let mut done = vec![false; n];
        dist[from] = 0.0;
        // A free writer reaches its value from anywhere.
        for &(q, cost) in &self.free {
            if cost < dist[q] {
                dist[q] = cost;
            }
        }
        // Domains are small; a quadratic scan avoids a heap.
        loop {
            let mut best = None;
            let mut best_dist = f32::INFINITY;
            for value in 0..n {
                if !done[value] && dist[value] < best_dist {
                    best_dist = dist[value];
                    best = Some(value);
                }
            }
            let Some(value) = best else { break };
            done[value] = true;
            for &(q, cost) in &self.edges[value] {
                let next = best_dist + cost;
                if next < dist[q] {
                    dist[q] = next;
                }
            }
        }
        dist.into_boxed_slice()
    }
}

/// Static per-task tables for the flow estimate.
pub struct FlowTable {
    graphs: Vec<VariableGraph>,
    derived: Vec<bool>,
    initial: Vec<usize>,
    goal: Vec<Option<usize>>,
    goal_variables: Vec<usize>,
    /// Per goal variable, its transport cost when no committed step writes
    /// it (the distance from its initial to its goal value), and their sum.
    goal_base: Vec<f32>,
    goal_base_total: f32,
    /// Per operator: `(variable, pre, post, effect index, conditional)` for
    /// every write to a non-derived variable that changes it.
    writes: Vec<Vec<Write>>,
    /// Additive costs from the initial state, for prevail and derived needs.
    add: Vec<Vec<f32>>,
    offset: Vec<usize>,
    scratch: RefCell<Scratch>,
}

#[derive(Clone, Copy)]
struct Write {
    variable: u32,
    pre: Option<u32>,
    post: u32,
    effect: u32,
    conditional: bool,
}

#[derive(Default)]
struct Scratch {
    /// Token balance per variable, sparse: `(value, balance)`.
    balance: Vec<Vec<(usize, i32)>>,
    absorb: Vec<i32>,
    skip: Vec<bool>,
    touched: Vec<usize>,
    is_touched: Vec<bool>,
    /// Facts some committed step may produce, and facts already charged as
    /// prevail needs, with the indexes to reset.
    supplied: Vec<bool>,
    charged: Vec<bool>,
    marked: Vec<usize>,
}

impl Scratch {
    fn touch(&mut self, variable: usize) {
        if !self.is_touched[variable] {
            self.is_touched[variable] = true;
            self.touched.push(variable);
        }
    }

    fn add(&mut self, variable: usize, value: usize, delta: i32) {
        self.touch(variable);
        let entries = &mut self.balance[variable];
        if let Some(entry) = entries.iter_mut().find(|(v, _)| *v == value) {
            entry.1 += delta;
        } else {
            entries.push((value, delta));
        }
    }
}

impl FlowTable {
    /// `add` holds additive costs from the initial state, `requirements` the
    /// preconditions (with effect conditions) of each operator effect, and
    /// `costs` each operator's resolved cost.
    pub fn new(
        task: &Task,
        add: &[Vec<f32>],
        requirements: &[Vec<Vec<Fact>>],
        costs: &[f32],
    ) -> Self {
        let n = task.variables.len();
        let derived = (0..n)
            .map(|v| task.is_derived_variable(v))
            .collect::<Vec<_>>();
        let mut edges: Vec<Vec<Vec<(usize, f32)>>> = task
            .variables
            .iter()
            .map(|variable| vec![Vec::new(); variable.values.len()])
            .collect();
        let mut free: Vec<Vec<(usize, f32)>> = vec![Vec::new(); n];
        let mut writes = Vec::with_capacity(task.operators.len());
        for (o, operator) in task.operators.iter().enumerate() {
            let mut list = Vec::new();
            for (e, effect) in operator.effects.iter().enumerate() {
                let v = effect.variable;
                if derived[v] {
                    continue;
                }
                let pre = effect.pre.or_else(|| {
                    operator
                        .prevail
                        .iter()
                        .find(|fact| fact.variable == v)
                        .map(|fact| fact.value)
                });
                if pre == Some(effect.post) {
                    continue;
                }
                list.push(Write {
                    variable: v as u32,
                    pre: pre.map(|p| p as u32),
                    post: effect.post as u32,
                    effect: e as u32,
                    conditional: !effect.conditions.is_empty(),
                });
                let mut cost = costs[o];
                for requirement in &requirements[o][e] {
                    if requirement.variable != v {
                        cost += add[requirement.variable][requirement.value];
                    }
                }
                if !cost.is_finite() {
                    continue;
                }
                let slot = match pre {
                    Some(p) => &mut edges[v][p],
                    None => &mut free[v],
                };
                match slot.iter_mut().find(|(q, _)| *q == effect.post) {
                    Some(entry) => entry.1 = entry.1.min(cost),
                    None => slot.push((effect.post, cost)),
                }
            }
            writes.push(list);
        }
        let graphs: Vec<VariableGraph> = edges
            .into_iter()
            .zip(free)
            .map(|(edges, free)| {
                let values = edges.len();
                VariableGraph {
                    edges,
                    free,
                    dist: RefCell::new(vec![None; values]),
                }
            })
            .collect();
        let mut goal = vec![None; n];
        let mut goal_variables = Vec::new();
        for g in &task.goals {
            if !derived[g.variable] {
                goal[g.variable] = Some(g.value);
                goal_variables.push(g.variable);
            }
        }
        let mut offset = Vec::with_capacity(n);
        let mut facts = 0;
        for variable in &task.variables {
            offset.push(facts);
            facts += variable.values.len();
        }
        let mut goal_base = vec![0.0f32; n];
        let mut goal_base_total = 0.0f32;
        for &v in &goal_variables {
            let g = goal[v].expect("goal variable has a goal value");
            let graph: &VariableGraph = &graphs[v];
            goal_base[v] = graph.distance(task.initial[v], g);
            goal_base_total += goal_base[v];
        }
        FlowTable {
            goal_base,
            goal_base_total,
            add: add.to_vec(),
            offset,
            graphs,
            derived,
            initial: task.initial.clone(),
            goal,
            goal_variables,
            writes,
            scratch: RefCell::new(Scratch {
                balance: vec![Vec::new(); n],
                absorb: vec![0; n],
                skip: vec![false; n],
                touched: Vec::new(),
                is_touched: vec![false; n],
                supplied: vec![false; facts],
                charged: vec![false; facts],
                marked: Vec::new(),
            }),
        }
    }

    /// Replaces the additive costs charged to prevail and derived needs.
    pub fn set_additive(&mut self, add: &[Vec<f32>]) {
        self.add = add.to_vec();
    }

    /// Whether the variable is derived (axiom-defined) and so outside the flow.
    pub fn is_derived(&self, variable: usize) -> bool {
        self.derived[variable]
    }

    /// The summed transport cost over variables, or infinity when some
    /// variable has no feasible flow.
    ///
    /// `operator` maps a committed step to its operator and `can_fire` tells
    /// whether that step's effect (by index) can still fire. `opens` yields
    /// each open condition with its consumer's operator (`None` for the goal).
    ///
    /// Open conditions whose consumer overwrites the variable, and goals, are
    /// the flow's demands already. A *prevail* condition only needs some
    /// segment of its value to exist: it costs its additive cost once per
    /// distinct fact when no committed step can produce it and it does not
    /// hold initially. Derived conditions cost their additive cost.
    pub fn estimate<S: Copy>(
        &self,
        steps: impl Iterator<Item = S> + Clone,
        operator: impl Fn(S) -> usize,
        can_fire: impl Fn(S, usize) -> bool,
        opens: impl Iterator<Item = (Fact, Option<usize>)>,
    ) -> f32 {
        let mut scratch = self.scratch.borrow_mut();
        let scratch = &mut *scratch;
        let mut prevail = 0.0f32;
        for step in steps.clone() {
            for write in &self.writes[operator(step)] {
                if can_fire(step, write.effect as usize) {
                    let fact = self.offset[write.variable as usize] + write.post as usize;
                    if !scratch.supplied[fact] {
                        scratch.supplied[fact] = true;
                        scratch.marked.push(fact);
                    }
                }
            }
        }
        for (fact, consumer) in opens {
            let v = fact.variable;
            if self.derived[v] {
                prevail += self.add[v][fact.value];
                continue;
            }
            let Some(op) = consumer else { continue };
            if self.writes[op].iter().any(|w| w.variable as usize == v) {
                continue;
            }
            if self.initial[v] == fact.value {
                continue;
            }
            let index = self.offset[v] + fact.value;
            if scratch.supplied[index] || scratch.charged[index] {
                continue;
            }
            scratch.charged[index] = true;
            scratch.marked.push(index);
            prevail += self.add[v][fact.value];
        }
        for &index in &scratch.marked {
            scratch.supplied[index] = false;
            scratch.charged[index] = false;
        }
        scratch.marked.clear();
        if !prevail.is_finite() {
            return prevail;
        }
        for step in steps {
            for write in &self.writes[operator(step)] {
                if !can_fire(step, write.effect as usize) {
                    continue;
                }
                let v = write.variable as usize;
                if write.conditional {
                    scratch.touch(v);
                    scratch.skip[v] = true;
                    continue;
                }
                match write.pre {
                    Some(p) => scratch.add(v, p as usize, -1),
                    None => {
                        scratch.touch(v);
                        scratch.absorb[v] += 1;
                    }
                }
                scratch.add(v, write.post as usize, 1);
            }
        }
        // Goal variables no committed step writes cost their base distance.
        let touched = std::mem::take(&mut scratch.touched);
        let mut total = if self.goal_base_total.is_finite() {
            touched
                .iter()
                .filter(|&&v| self.goal[v].is_some())
                .fold(self.goal_base_total, |sum, &v| sum - self.goal_base[v])
        } else {
            self.goal_variables
                .iter()
                .filter(|&&v| !scratch.is_touched[v])
                .map(|&v| self.goal_base[v])
                .sum()
        };
        for &v in &touched {
            if total.is_finite() && !scratch.skip[v] {
                scratch.add(v, self.initial[v], 1);
                match self.goal[v] {
                    Some(g) => scratch.add(v, g, -1),
                    None => scratch.absorb[v] += 1,
                }
                total += transport(&self.graphs[v], &scratch.balance[v], scratch.absorb[v]);
            }
            scratch.balance[v].clear();
            scratch.absorb[v] = 0;
            scratch.skip[v] = false;
            scratch.is_touched[v] = false;
        }
        scratch.touched = touched;
        scratch.touched.clear();
        total + prevail
    }
}

/// Minimum cost to move every surplus token to a deficit, where up to
/// `absorb` tokens may instead stay where they are. Successive shortest paths
/// over the bipartite surplus/deficit graph; units are few in practice.
fn transport(graph: &VariableGraph, balance: &[(usize, i32)], absorb: i32) -> f32 {
    // Allocation-free fast paths: no deficit, or one surplus and one deficit.
    let mut sinks_seen = 0;
    let mut sources_seen = 0;
    let (mut source, mut sink) = ((0, 0), (0, 0));
    for &(value, b) in balance {
        if b > 0 {
            sources_seen += 1;
            source = (value, b);
        } else if b < 0 {
            sinks_seen += 1;
            sink = (value, -b);
        }
    }
    if sinks_seen == 0 {
        return 0.0;
    }
    if sinks_seen == 1 && sources_seen == 1 {
        if source.1 < sink.1 {
            return f32::INFINITY;
        }
        return sink.1 as f32 * graph.distance(source.0, sink.0);
    }
    let mut sources: Vec<(usize, i32)> = Vec::new();
    let mut sinks: Vec<(usize, i32)> = Vec::new();
    for &(value, b) in balance {
        if b > 0 {
            sources.push((value, b));
        } else if b < 0 {
            sinks.push((value, -b));
        }
    }
    if sinks.is_empty() {
        return 0.0;
    }
    let demand: i32 = sinks.iter().map(|s| s.1).sum();
    let supply: i32 = sources.iter().map(|s| s.1).sum();
    if supply < demand {
        return f32::INFINITY;
    }
    let _ = absorb;
    // Cost matrix; the absorber is implicit (cost 0, unlimited), since any
    // surplus not routed to a deficit is absorbed by the balance identity.
    let ns = sources.len();
    let nt = sinks.len();
    let mut cost = vec![f32::INFINITY; ns * nt];
    for (i, &(s, _)) in sources.iter().enumerate() {
        for (j, &(t, _)) in sinks.iter().enumerate() {
            cost[i * nt + j] = graph.distance(s, t);
        }
    }
    // Fast path: a single deficit value takes the cheapest sources.
    if nt == 1 {
        let mut order: Vec<usize> = (0..ns).collect();
        order.sort_by(|&a, &b| cost[a].total_cmp(&cost[b]));
        let mut need = sinks[0].1;
        let mut total = 0.0;
        for i in order {
            if need == 0 {
                break;
            }
            let take = need.min(sources[i].1);
            if !cost[i].is_finite() {
                return f32::INFINITY;
            }
            total += take as f32 * cost[i];
            need -= take;
        }
        return total;
    }
    // General case: min-cost flow with Bellman-Ford on the residual graph.
    // Nodes: 0 = source, 1..=ns sources, ns+1..=ns+nt sinks, ns+nt+1 = sink.
    let n = ns + nt + 2;
    let s_node = 0;
    let t_node = n - 1;
    let mut flow = vec![0i32; ns * nt];
    let mut src_left: Vec<i32> = sources.iter().map(|s| s.1).collect();
    let mut sink_left: Vec<i32> = sinks.iter().map(|s| s.1).collect();
    let mut total = 0.0f32;
    let mut remaining = demand;
    while remaining > 0 {
        let mut dist = vec![f32::INFINITY; n];
        let mut prev = vec![usize::MAX; n];
        dist[s_node] = 0.0;
        for _ in 0..n {
            let mut changed = false;
            for i in 0..ns {
                let u = 1 + i;
                if src_left[i] > 0 && dist[s_node] < dist[u] {
                    dist[u] = dist[s_node];
                    prev[u] = s_node;
                    changed = true;
                }
                for j in 0..nt {
                    let w = 1 + ns + j;
                    let c = cost[i * nt + j];
                    if c.is_finite() && dist[u].is_finite() && dist[u] + c < dist[w] {
                        dist[w] = dist[u] + c;
                        prev[w] = u;
                        changed = true;
                    }
                    if flow[i * nt + j] > 0 && dist[w].is_finite() && dist[w] - c < dist[u] {
                        dist[u] = dist[w] - c;
                        prev[u] = w;
                        changed = true;
                    }
                }
            }
            for (j, &left) in sink_left.iter().enumerate() {
                let w = 1 + ns + j;
                if left > 0 && dist[w] < dist[t_node] {
                    dist[t_node] = dist[w];
                    prev[t_node] = w;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        if !dist[t_node].is_finite() {
            return f32::INFINITY;
        }
        // Bottleneck along the path.
        let mut bottleneck = remaining;
        let mut node = t_node;
        while node != s_node {
            let p = prev[node];
            if node == t_node {
                bottleneck = bottleneck.min(sink_left[p - 1 - ns]);
            } else if p == s_node {
                bottleneck = bottleneck.min(src_left[node - 1]);
            } else if p > ns {
                // Backward along a used edge from sink p to source node.
                bottleneck = bottleneck.min(flow[(node - 1) * nt + (p - 1 - ns)]);
            }
            node = p;
        }
        let mut node = t_node;
        while node != s_node {
            let p = prev[node];
            if node == t_node {
                sink_left[p - 1 - ns] -= bottleneck;
            } else if p == s_node {
                src_left[node - 1] -= bottleneck;
            } else if p > ns {
                flow[(node - 1) * nt + (p - 1 - ns)] -= bottleneck;
            } else {
                flow[(p - 1) * nt + (node - 1 - ns)] += bottleneck;
            }
            node = p;
        }
        total += bottleneck as f32 * dist[t_node];
        remaining -= bottleneck;
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line(n: usize) -> VariableGraph {
        let mut edges = vec![Vec::new(); n];
        for v in 0..n - 1 {
            edges[v].push((v + 1, 1.0));
            edges[v + 1].push((v, 1.0));
        }
        VariableGraph {
            edges,
            free: Vec::new(),
            dist: RefCell::new(vec![None; n]),
        }
    }

    #[test]
    fn transport_matches_tokens_to_the_nearest_deficits() {
        let graph = line(6);
        // Surpluses at 0 and 5, deficits at 1 and 4: 1 + 1.
        assert_eq!(
            transport(&graph, &[(0, 1), (5, 1), (1, -1), (4, -1)], 0),
            2.0
        );
        // Two units from 0 must cover 2 and 3.
        assert_eq!(transport(&graph, &[(0, 2), (2, -1), (3, -1)], 0), 5.0);
        // Crossing assignment must be undone by the residual graph.
        assert_eq!(
            transport(&graph, &[(1, 1), (2, 1), (0, -1), (3, -1)], 0),
            2.0
        );
    }

    #[test]
    fn unreachable_deficit_is_infinite() {
        let mut graph = line(3);
        graph.edges[1].clear();
        graph.edges[2].clear();
        // Token at 2 cannot reach 0.
        assert!(transport(&graph, &[(2, 1), (0, -1)], 0).is_infinite());
    }

    #[test]
    fn free_writers_reach_from_anywhere() {
        let mut graph = line(3);
        graph.edges = vec![Vec::new(); 3];
        graph.free.push((0, 4.0));
        assert_eq!(transport(&graph, &[(2, 1), (0, -1)], 0), 4.0);
    }
}
