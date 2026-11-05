//! Joint operator parameter domains (Younes & Simmons, AIPS 2002).
//!
//! Each shared table contains complete, relaxed-reachable argument tuples.
//! Filter these by bindings and propagate column supports through equality
//! classes to a fixpoint. Empty relations reject the plan; singleton projections
//! become ordinary bindings. An expansion-local snapshot shares unchanged row
//! domains across siblings. A worklist revisits only affected constraints.
//! Queued plans retain bindings, but no row domains or propagation worklists.
//! Exact Cartesian factors avoid scanning independent parameter combinations.
//! Binding constraints that couple factors fall back to the complete table.
//!
//! This is local consistency, not a complete CSP solver. Non-singleton domain
//! reductions are reconstructed when a queued plan is expanded; heuristic
//! matching and threat counting currently see only the forced bindings.

use std::cell::{Cell, OnceCell, RefCell};
use std::collections::VecDeque;
use std::rc::Rc;

use crate::bindings::{AtomPatternKey, Binding, Bindings, StepVariable, TypeContext};
use crate::chain::{self, Chain};
use crate::fasthash::{FastMap, FastSet};
use crate::object_set::ObjectSet;
use crate::plan::{Plan, Step};
use crate::search::SearchContext;
use crate::terms::{Object, Term};

pub(crate) struct JointDomains {
    tables: FastMap<String, Table>,
    cache_budget: CacheBudget,
    factor_work: Cell<usize>,
}

impl Default for JointDomains {
    fn default() -> Self {
        Self {
            tables: FastMap::default(),
            cache_budget: CacheBudget::default(),
            // Bound the optional decomposition analysis across all schemas.
            factor_work: Cell::new(4 * 1024 * 1024),
        }
    }
}

struct CacheBudget {
    bytes: Cell<usize>,
    entries: Cell<usize>,
}

impl Default for CacheBudget {
    fn default() -> Self {
        Self {
            bytes: Cell::new(4 * 1024 * 1024),
            entries: Cell::new(512),
        }
    }
}

struct Table {
    arity: usize,
    cells: Box<[Object]>,
    rows: usize,
    // Sorted (object, row) pairs: eight bytes per cell, with no per-object
    // hash bucket or allocation. Equal-object postings form a contiguous run.
    columns: Vec<Box<[(Object, u32)]>>,
    full: OnceCell<Rc<RowDomain>>,
    memo: RefCell<FastMap<AtomPatternKey, Rc<RowDomain>>>,
    factors: OnceCell<Factorization>,
}

#[derive(Default)]
struct Factorization {
    parts: Vec<Factor>,
    // Original column -> factor, used to detect binding constraints that
    // couple otherwise independent factors.
    groups: Vec<usize>,
}

struct Factor {
    columns: Vec<usize>,
    table: Table,
}

impl JointDomains {
    pub(crate) fn insert(&mut self, name: String, arity: usize, cells: Vec<Object>, rows: usize) {
        self.tables.insert(name, Table::new(arity, cells, rows));
    }
}

impl Table {
    fn new(arity: usize, cells: Vec<Object>, rows: usize) -> Self {
        assert_eq!(cells.len(), arity * rows);
        let columns = (0..arity)
            .map(|column| {
                let mut postings: Vec<_> = (0..rows)
                    .map(|row| {
                        (
                            cells[row * arity + column],
                            u32::try_from(row).expect("joint table exceeds bounded storage"),
                        )
                    })
                    .collect();
                postings.sort_unstable();
                postings.into_boxed_slice()
            })
            .collect();
        Self {
            arity,
            cells: cells.into(),
            rows,
            columns,
            full: OnceCell::new(),
            memo: RefCell::new(FastMap::default()),
            factors: OnceCell::new(),
        }
    }

    fn factors(&self, budget: &Cell<usize>) -> &Factorization {
        self.factors.get_or_init(|| {
            // Small tables are cheaper to filter directly. Larger arities and
            // exhausted analysis budgets retain the original complete table.
            if !(2..=8).contains(&self.arity)
                || !(64..=262_144).contains(&self.rows)
                || self.cells.len() > budget.get()
            {
                return Factorization::default();
            }
            budget.set(budget.get() - self.cells.len());
            let rows: FastSet<_> = self
                .cells
                .chunks_exact(self.arity)
                .map(|tuple| {
                    let mut row = [Object(0); 8];
                    row[..self.arity].copy_from_slice(tuple);
                    row
                })
                .collect();
            let mut parts = Vec::new();
            split_factors((0..self.arity).collect(), rows, budget, &mut parts);
            if parts.len() < 2 {
                return Factorization::default();
            }
            let parts: Vec<_> = parts
                .into_iter()
                .map(|(columns, rows)| {
                    let arity = columns.len();
                    let mut rows: Vec<_> = rows.into_iter().collect();
                    rows.sort_unstable();
                    let count = rows.len();
                    let cells = rows
                        .into_iter()
                        .flat_map(|row| row.into_iter().take(arity))
                        .collect();
                    Factor {
                        columns,
                        table: Table::new(arity, cells, count),
                    }
                })
                .collect();
            let mut groups = vec![0; self.arity];
            for (group, factor) in parts.iter().enumerate() {
                for &column in &factor.columns {
                    groups[column] = group;
                }
            }
            Factorization { parts, groups }
        })
    }

    fn full_domain(&self) -> &Rc<RowDomain> {
        self.full
            .get_or_init(|| Rc::new(RowDomain::new(self, (0..self.rows as u32).collect())))
    }

    fn tuple(&self, row: u32) -> &[Object] {
        let start = row as usize * self.arity;
        &self.cells[start..start + self.arity]
    }

    fn candidates(&self, bound: impl Iterator<Item = (usize, Object)>) -> Option<&[(Object, u32)]> {
        let mut best: Option<&[(Object, u32)]> = None;
        for (column, object) in bound {
            let postings = &self.columns[column];
            let start = postings.partition_point(|(value, _)| *value < object);
            let end = postings.partition_point(|(value, _)| *value <= object);
            let rows = &postings[start..end];
            if best.is_none_or(|previous| rows.len() < previous.len()) {
                best = Some(rows);
            }
        }
        best
    }
}

/// A relation is contained in the Cartesian product of any two disjoint
/// projections. Equal cardinalities prove equality with that product. Count
/// DISTINCT tuples, so duplicate input rows cannot falsely prove independence.
/// Every accepted split is exact; stopping early only misses an optimization.
fn split_factors(
    columns: Vec<usize>,
    rows: FastSet<[Object; 8]>,
    budget: &Cell<usize>,
    parts: &mut Vec<(Vec<usize>, FastSet<[Object; 8]>)>,
) {
    let arity = columns.len();
    // Complementary partitions are equivalent: consider only masks with bit 0.
    // Try balanced splits first: they usually remove the largest products.
    let mut masks: Vec<usize> = (1..(1 << arity) - 1).step_by(2).collect();
    masks.sort_unstable_by_key(|m| {
        let size = m.count_ones() as usize;
        (size.abs_diff(arity - size), *m)
    });
    for mask in masks {
        let work = rows.len() * arity;
        if work > budget.get() {
            break;
        }
        budget.set(budget.get() - work);
        let left: Vec<_> = (0..arity).filter(|i| mask & (1 << i) != 0).collect();
        let right: Vec<_> = (0..arity).filter(|i| mask & (1 << i) == 0).collect();
        let project = |positions: &[usize]| -> FastSet<[Object; 8]> {
            // Do not reserve the full relation's row count: successful factors
            // can have orders of magnitude fewer distinct projected tuples.
            let mut result = FastSet::default();
            for row in &rows {
                let mut projected = [Object(0); 8];
                for (i, &column) in positions.iter().enumerate() {
                    projected[i] = row[column];
                }
                result.insert(projected);
            }
            result
        };
        let a = project(&left);
        let b = project(&right);
        if a.len().checked_mul(b.len()) == Some(rows.len()) {
            split_factors(left.iter().map(|&i| columns[i]).collect(), a, budget, parts);
            split_factors(
                right.iter().map(|&i| columns[i]).collect(),
                b,
                budget,
                parts,
            );
            return;
        }
    }
    parts.push((columns, rows));
}

/// Immutable, sorted surviving row IDs and their cached column projections.
/// Only changed domains allocate replacements; siblings keep sharing these.
struct RowDomain {
    rows: Vec<u32>,
    supports: Vec<ObjectSet>,
}

impl RowDomain {
    fn new(table: &Table, rows: Vec<u32>) -> Self {
        let mut supports = vec![ObjectSet::default(); table.arity];
        for &row in &rows {
            for (support, object) in supports.iter_mut().zip(table.tuple(row)) {
                support.insert(*object);
            }
        }
        Self { rows, supports }
    }

    fn storage_bytes(&self) -> usize {
        std::mem::size_of::<Self>()
            + 2 * std::mem::size_of::<usize>()
            + self.rows.capacity() * std::mem::size_of::<u32>()
            + self.supports.capacity() * std::mem::size_of::<ObjectSet>()
            + self
                .supports
                .iter()
                .map(ObjectSet::heap_bytes)
                .sum::<usize>()
    }
}

/// Retained only while expanding one parent, never attached to queued plans.
/// The persistent histories prove ancestry before any restrictions are reused.
pub(crate) struct Snapshot {
    steps: Option<Rc<Chain<Step>>>,
    num_steps: usize,
    bindings: Rc<Bindings>,
    domains: FastMap<(usize, usize), Rc<RowDomain>>,
}

impl Snapshot {
    fn extends_steps(&self, plan: &Plan) -> bool {
        let Some(added) = plan.num_steps.checked_sub(self.num_steps) else {
            return false;
        };
        let mut tail = &plan.steps;
        for _ in 0..added {
            let Some(node) = tail else { return false };
            tail = &node.tail;
        }
        match (tail, &self.steps) {
            (Some(a), Some(b)) => Rc::ptr_eq(a, b),
            (None, None) => true,
            _ => false,
        }
    }

    fn capture(plan: &Plan, bindings: Rc<Bindings>, constraints: Vec<Constraint<'_>>) -> Self {
        Self {
            steps: plan.steps.clone(),
            num_steps: plan.num_steps,
            bindings,
            domains: constraints.into_iter().map(|c| (c.key, c.domain)).collect(),
        }
    }
}

struct Constraint<'a> {
    // (step, part): part zero denotes the complete relation.
    key: (usize, usize),
    table: &'a Table,
    domain: Rc<RowDomain>,
    variables: Vec<Option<usize>>,
}

/// Build the parent cache lazily, once its first binding-changing refinement
/// needs it. The parent is already propagated in search; this reconstructs its
/// non-singleton domains without retaining them on the frontier.
pub(crate) fn prepare(ctx: &SearchContext, parent: &Plan) -> Option<Snapshot> {
    run(ctx, parent, None, true).and_then(|(_, snapshot)| snapshot)
}

#[cfg(test)]
fn propagate(ctx: &SearchContext, plan: &Plan) -> Option<Rc<Bindings>> {
    propagate_incremental(ctx, plan, None)
}

pub(crate) fn propagate_incremental(
    ctx: &SearchContext,
    plan: &Plan,
    parent: Option<&Snapshot>,
) -> Option<Rc<Bindings>> {
    let result = run(ctx, plan, parent, false).map(|(bindings, _)| bindings);
    #[cfg(test)]
    assert_matches_reference(ctx, plan, &result);
    result
}

fn filter_bindings(
    table: &Table,
    terms: &[Term],
    step_id: usize,
    bindings: &Bindings,
    types: &TypeContext,
    inherited: Option<&Rc<RowDomain>>,
    cache_budget: &CacheBudget,
) -> Option<Rc<RowDomain>> {
    let resolved = bindings.resolve_pattern(types, terms, step_id);
    let base = inherited.unwrap_or_else(|| table.full_domain());
    if base.rows.is_empty() {
        return None;
    }
    // Only cache filtering of the complete table. An inherited domain also
    // carries restrictions from other steps that are absent from this key.
    let cache_key =
        (table.rows >= 64 && base.rows.len() == table.rows).then(|| resolved.table_cache_key());
    if let Some(hit) = cache_key
        .as_ref()
        .and_then(|key| table.memo.borrow().get(key).cloned())
    {
        return Some(hit);
    }
    let declared_types = terms.iter().map(|term| match term {
        Term::Variable(var) => types.step_vars.var_type(*var, step_id),
        // Bound positions do not need a type check.
        Term::Object(_) => crate::types::OBJECT,
    });
    let pattern = resolved.for_object_table(types, &base.supports, declared_types)?;
    if pattern.unrestricted() {
        return Some(base.clone());
    }
    let candidates = table.candidates(resolved.bound_positions());
    let mut rows = Vec::new();
    // Both indexed postings and inherited row IDs are sorted by row. A new
    // binding can probe a selective index, while enforcing inherited domains.
    if let Some(candidates) = candidates.filter(|c| c.len() < base.rows.len()) {
        let full = base.rows.len() == table.rows;
        for &(_, row) in candidates {
            if (full || base.rows.binary_search(&row).is_ok()) && pattern.matches(table.tuple(row))
            {
                rows.push(row);
            }
        }
    } else {
        for &row in &base.rows {
            if pattern.matches(table.tuple(row)) {
                rows.push(row);
            }
        }
    }
    if rows.is_empty() {
        return None;
    }
    if rows.len() == base.rows.len() {
        return Some(base.clone());
    }
    let result = Rc::new(RowDomain::new(table, rows));
    if let Some(key) = cache_key {
        let bytes = key.storage_bytes() + result.storage_bytes();
        if cache_budget.entries.get() > 0 && bytes <= cache_budget.bytes.get() {
            cache_budget.bytes.set(cache_budget.bytes.get() - bytes);
            cache_budget.entries.set(cache_budget.entries.get() - 1);
            table.memo.borrow_mut().insert(key, result.clone());
        }
    }
    Some(result)
}

type Propagation = (Rc<Bindings>, Option<Snapshot>);

fn run(
    ctx: &SearchContext,
    plan: &Plan,
    parent: Option<&Snapshot>,
    capture: bool,
) -> Option<Propagation> {
    let tables = ctx.joint_domains();
    let types = ctx.type_ctx();
    let mut bindings = plan.bindings.clone();
    let mut previous: Option<Snapshot> = None;
    loop {
        let base = previous
            .as_ref()
            .or(parent)
            .filter(|s| s.extends_steps(plan));
        let changed = base.and_then(|s| bindings.changed_classes_since(&s.bindings));
        let base = base.filter(|_| changed.is_some());
        let mut variables: Vec<StepVariable> = Vec::new();
        let mut ids = FastMap::default();
        let mut constraints = Vec::new();
        for step in chain::iter(&plan.steps) {
            let action = &step.action;
            if action.synthetic() {
                continue;
            }
            let Some(table) = tables.tables.get(&action.name) else {
                continue;
            };
            let terms: Vec<_> = if !action.arguments.is_empty() {
                action.arguments.iter().copied().map(Term::Object).collect()
            } else {
                action
                    .parameters
                    .iter()
                    .copied()
                    .map(Term::Variable)
                    .collect()
            };
            let factors = table.factors(&tables.factor_work);
            let inherited_full = base.and_then(|s| s.domains.get(&(step.id, 0)));
            let inherited_factored = !factors.parts.is_empty()
                && base.is_some_and(|s| s.domains.contains_key(&(step.id, 1)));
            let dirty = (inherited_full.is_none() && !inherited_factored)
                || terms.iter().any(|term| {
                    let base = base.unwrap();
                    match bindings.binding(*term, step.id) {
                        // A changed class can contain many variables already pinned
                        // to this object. Their patterns did not change.
                        Term::Object(object) => {
                            base.bindings.binding(*term, step.id) != Term::Object(object)
                        }
                        Term::Variable(var) => changed
                            .as_ref()
                            .unwrap()
                            .contains(&bindings.representative(var, step.id)),
                    }
                });
            // Keep canonical variable enumeration in the original parameter
            // order, independent of how columns are grouped. Singleton binding
            // batches then retain their original order as well.
            let mut positions: Vec<_> = terms
                .iter()
                .map(|term| {
                    let Term::Variable(var) = bindings.binding(*term, step.id) else {
                        return None;
                    };
                    let key = bindings.representative(var, step.id);
                    Some(*ids.entry(key).or_insert_with(|| {
                        let id = variables.len();
                        variables.push(key);
                        id
                    }))
                })
                .collect();
            // A single remaining unbound group already scans a small slice of
            // the full relation. Avoid splitting it into several constraints.
            // Retain an inherited decomposition to avoid rebuilding its domains.
            let mut active_groups = 0u8;
            for (&group, variable) in factors.groups.iter().zip(&positions) {
                if variable.is_some() {
                    active_groups |= 1 << group;
                }
            }
            let factored = !factors.parts.is_empty()
                && (inherited_factored || active_groups.count_ones() > 1)
                && if dirty {
                    !bindings
                        .resolve_pattern(&types, &terms, step.id)
                        .couples_groups(&factors.groups)
                } else {
                    inherited_factored
                };
            for part in 0..if factored { factors.parts.len() } else { 1 } {
                let projected_terms;
                let (table, terms, positions, key) = if factored {
                    let factor = &factors.parts[part];
                    projected_terms = factor.columns.iter().map(|&i| terms[i]).collect::<Vec<_>>();
                    (
                        &factor.table,
                        projected_terms.as_slice(),
                        factor.columns.iter().map(|&i| positions[i]).collect(),
                        (step.id, part + 1),
                    )
                } else {
                    (
                        table,
                        terms.as_slice(),
                        std::mem::take(&mut positions),
                        (step.id, 0),
                    )
                };
                let inherited = if factored {
                    base.and_then(|s| s.domains.get(&key))
                } else {
                    inherited_full
                };
                let domain = match inherited {
                    Some(domain) if !dirty => domain.clone(),
                    _ => filter_bindings(
                        table,
                        terms,
                        step.id,
                        &bindings,
                        &types,
                        inherited,
                        &tables.cache_budget,
                    )?,
                };
                constraints.push(Constraint {
                    key,
                    table,
                    domain,
                    variables: positions,
                });
            }
        }

        // Intersect cached projections once. Watchers then schedule only tables
        // whose rows could lose support when a shared variable domain shrinks.
        let mut domains: Vec<Option<ObjectSet>> = vec![None; variables.len()];
        let mut watchers = vec![Vec::new(); variables.len()];
        for (ci, constraint) in constraints.iter().enumerate() {
            for (column, variable) in constraint.variables.iter().enumerate() {
                let Some(v) = *variable else { continue };
                if watchers[v].last() != Some(&ci) {
                    watchers[v].push(ci);
                }
                let support = &constraint.domain.supports[column];
                if let Some(domain) = &mut domains[v] {
                    domain.intersect_with(support);
                    if domain.is_empty() {
                        return None;
                    }
                } else {
                    domains[v] = Some(support.clone());
                }
            }
        }
        let mut queue = VecDeque::new();
        let mut queued = vec![false; constraints.len()];
        for (ci, constraint) in constraints.iter().enumerate() {
            if constraint
                .variables
                .iter()
                .enumerate()
                .any(|(column, variable)| {
                    variable.is_some_and(|v| {
                        domains[v].as_ref().unwrap().len()
                            < constraint.domain.supports[column].len()
                    })
                })
            {
                queued[ci] = true;
                queue.push_back(ci);
            }
        }
        while let Some(ci) = queue.pop_front() {
            queued[ci] = false;
            let constraint = &mut constraints[ci];
            // Projections already contained in the current variable domain
            // cannot remove any row. This also discards redundant self-wakeups.
            let restrictions: Vec<_> = constraint
                .variables
                .iter()
                .enumerate()
                .filter_map(|(column, variable)| {
                    let domain = domains[(*variable)?].as_ref().unwrap();
                    (domain.len() < constraint.domain.supports[column].len())
                        .then_some((column, domain))
                })
                .collect();
            if restrictions.is_empty() {
                continue;
            }
            let matches = |row: u32| {
                let tuple = constraint.table.tuple(row);
                restrictions
                    .iter()
                    .all(|&(column, domain)| domain.contains(tuple[column]))
            };
            // A small new support set can probe existing column postings instead
            // of scanning a large relation. Require a clear reduction to cover
            // inherited-row membership checks and sorting a union of postings.
            let mut best = None;
            let mut best_len = constraint.domain.rows.len() / 4;
            for &(column, domain) in &restrictions {
                if domain.len() > 4 {
                    continue;
                }
                let mut postings = Vec::new();
                let mut count = 0;
                for object in domain.iter() {
                    let rows = constraint
                        .table
                        .candidates(std::iter::once((column, object)))
                        .unwrap();
                    count += rows.len();
                    if count >= best_len {
                        break;
                    }
                    postings.push(rows);
                }
                if count < best_len {
                    best_len = count;
                    best = Some(postings);
                }
            }
            let rows: Vec<_> = if let Some(postings) = best {
                let full = constraint.domain.rows.len() == constraint.table.rows;
                let mut rows: Vec<_> = postings
                    .iter()
                    .flat_map(|p| p.iter())
                    .map(|&(_, row)| row)
                    .filter(|&row| {
                        (full || constraint.domain.rows.binary_search(&row).is_ok()) && matches(row)
                    })
                    .collect();
                if postings.len() > 1 {
                    rows.sort_unstable();
                }
                rows
            } else {
                constraint
                    .domain
                    .rows
                    .iter()
                    .copied()
                    .filter(|&row| matches(row))
                    .collect()
            };
            if rows.is_empty() {
                return None;
            }
            if rows.len() == constraint.domain.rows.len() {
                continue;
            }
            constraint.domain = Rc::new(RowDomain::new(constraint.table, rows));
            for (column, variable) in constraint.variables.iter().enumerate() {
                let Some(v) = *variable else { continue };
                let domain = domains[v].as_mut().unwrap();
                let old_len = domain.len();
                domain.intersect_with(&constraint.domain.supports[column]);
                if domain.is_empty() {
                    return None;
                }
                if domain.len() < old_len {
                    for &other in &watchers[v] {
                        if !queued[other] {
                            queued[other] = true;
                            queue.push_back(other);
                        }
                    }
                }
            }
        }
        let forced: Vec<_> = variables
            .iter()
            .zip(&domains)
            .filter_map(|(&(var, step), domain)| {
                let domain = domain.as_ref()?;
                (domain.len() == 1).then(|| {
                    Binding::new(
                        var,
                        step,
                        Term::Object(domain.iter().next().unwrap()),
                        0,
                        true,
                    )
                })
            })
            .collect();
        if forced.is_empty() {
            let snapshot = capture.then(|| Snapshot::capture(plan, bindings.clone(), constraints));
            return Some((bindings, snapshot));
        }
        let strengthened = bindings.add(&types, &forced, false)?;
        // Reuse these narrowed tables when newly forced objects propagate
        // exclusions to other steps. They cannot grow under stronger bindings.
        previous = Some(Snapshot::capture(plan, bindings, constraints));
        bindings = strengthened;
    }
}

#[cfg(test)]
fn assert_matches_reference(ctx: &SearchContext, plan: &Plan, actual: &Option<Rc<Bindings>>) {
    let expected = reference::propagate_reference(ctx, plan);
    assert_eq!(
        actual.is_some(),
        expected.is_some(),
        "incremental propagation changed pruning"
    );
    if let (Some(actual), Some(expected)) = (actual, expected) {
        let mut variables = plan.bindings.constrained_variables();
        for step in chain::iter(&plan.steps) {
            variables.extend(step.action.parameters.iter().map(|&v| (v, step.id)));
        }
        for (var, step) in variables {
            assert_eq!(
                actual.binding(Term::Variable(var), step),
                expected.binding(Term::Variable(var), step),
                "incremental propagation changed a forced binding"
            );
        }
    }
}

#[cfg(test)]
mod reference {
    use super::*;
    struct ReferenceConstraint<'a> {
        table: &'a Table,
        rows: Vec<u32>,
        // Bound positions have no variable domain to update.
        variables: Vec<Option<usize>>,
    }

    /// Returns the strengthened bindings, or None if no allowed tuple remains.
    /// Register this plan's step types before calling, just as for ranking it.
    pub(super) fn propagate_reference(ctx: &SearchContext, plan: &Plan) -> Option<Rc<Bindings>> {
        let tables = ctx.joint_domains();
        let types = ctx.type_ctx();
        let mut bindings = plan.bindings.clone();
        loop {
            let mut variables: Vec<StepVariable> = Vec::new();
            let mut ids = FastMap::default();
            let mut constraints = Vec::new();
            for step in chain::iter(&plan.steps) {
                let action = &step.action;
                if action.synthetic() {
                    continue;
                }
                let Some(table) = tables.tables.get(&action.name) else {
                    continue;
                };
                let terms: Vec<Term> = if !action.arguments.is_empty() {
                    action.arguments.iter().copied().map(Term::Object).collect()
                } else {
                    action
                        .parameters
                        .iter()
                        .copied()
                        .map(Term::Variable)
                        .collect()
                };
                let mut pattern = bindings.resolve_pattern(&types, &terms, step.id);
                let mut rows = Vec::new();
                let mut consider = |row| {
                    if pattern.matches_objects(&types, table.tuple(row)) {
                        rows.push(row);
                    }
                };
                // Extract first so the iterator doesn't borrow the mutable pattern.
                let bound: Vec<_> = terms
                    .iter()
                    .enumerate()
                    .filter_map(|(i, term)| match bindings.binding(*term, step.id) {
                        Term::Object(object) => Some((i, object)),
                        _ => None,
                    })
                    .collect();
                if let Some(candidates) = table.candidates(bound.into_iter()) {
                    for &(_, row) in candidates {
                        consider(row);
                    }
                } else {
                    for row in 0..table.rows as u32 {
                        consider(row);
                    }
                }
                if rows.is_empty() {
                    return None;
                }
                let positions = terms
                    .iter()
                    .map(|term| {
                        let Term::Variable(var) = bindings.binding(*term, step.id) else {
                            return None;
                        };
                        let key = bindings.representative(var, step.id);
                        Some(*ids.entry(key).or_insert_with(|| {
                            let id = variables.len();
                            variables.push(key);
                            id
                        }))
                    })
                    .collect();
                constraints.push(ReferenceConstraint {
                    table,
                    rows,
                    variables: positions,
                });
            }

            let mut domains: Vec<Option<FastSet<Object>>> = vec![None; variables.len()];
            loop {
                let mut changed = false;
                for constraint in &mut constraints {
                    constraint.rows.retain(|row| {
                        constraint
                            .table
                            .tuple(*row)
                            .iter()
                            .zip(&constraint.variables)
                            .all(|(object, var)| {
                                var.is_none_or(|v| {
                                    domains[v].as_ref().is_none_or(|d| d.contains(object))
                                })
                            })
                    });
                    if constraint.rows.is_empty() {
                        return None;
                    }
                    for (column, variable) in constraint.variables.iter().enumerate() {
                        let Some(variable) = *variable else { continue };
                        let support: FastSet<Object> = constraint
                            .rows
                            .iter()
                            .map(|row| constraint.table.tuple(*row)[column])
                            .collect();
                        if let Some(domain) = &mut domains[variable] {
                            let old_len = domain.len();
                            domain.retain(|object| support.contains(object));
                            if domain.is_empty() {
                                return None;
                            }
                            changed |= old_len != domain.len();
                        } else {
                            domains[variable] = Some(support);
                            changed = true;
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            let forced: Vec<_> = variables
                .iter()
                .zip(&domains)
                .filter_map(|(&(var, step), domain)| {
                    let domain = domain.as_ref()?;
                    (domain.len() == 1).then(|| {
                        Binding::new(
                            var,
                            step,
                            Term::Object(*domain.iter().next().unwrap()),
                            0,
                            true,
                        )
                    })
                })
                .collect();
            if forced.is_empty() {
                return Some(bindings);
            }
            bindings = bindings.add(&types, &forced, false)?;
            // Re-resolve patterns: a newly pinned variable can exclude an object
            // from a different step through a non-codesignation constraint.
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::Domain;
    use crate::params::Parameters;
    use crate::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
    use crate::plan::{Step, StepAction};
    use crate::problem::Problem;
    use crate::terms::Variable;

    fn task(initial: &str) -> (Domain, Problem) {
        let ParsedUnit::Domain(parsed) = read_pddl(
            "(define (domain joint)
            (:requirements :strips :equality)
            (:predicates (pair ?x ?y) (choice ?x) (done))
            (:action pair-step :parameters (?x ?y) :precondition (pair ?x ?y) :effect (done))
            (:action choice-step :parameters (?x) :precondition (choice ?x) :effect (done)))",
        )
        .unwrap() else {
            panic!()
        };
        let domain = lower_domain(&parsed).unwrap();
        let ParsedUnit::Problem(parsed) = read_pddl(&format!(
            "(define (problem test)
            (:domain joint) (:objects a b c) (:init {initial}) (:goal (done)))"
        ))
        .unwrap() else {
            panic!()
        };
        let problem = lower_problem(&parsed, &domain).unwrap();
        (domain, problem)
    }

    fn steps(ctx: &SearchContext, schemas: &[usize]) -> Rc<Plan> {
        let mut plan = Plan::make_initial_plan(ctx).unwrap();
        for (offset, &schema) in schemas.iter().enumerate() {
            append_step(ctx, &mut plan, schema, offset + 1);
        }
        ctx.register_plan(&plan);
        plan
    }

    fn append_step(ctx: &SearchContext, plan: &mut Rc<Plan>, schema: usize, id: usize) {
        let schema = &ctx.domain.actions[schema];
        let action = Rc::new(StepAction {
            name: schema.name.clone(),
            parameters: schema.parameters.clone(),
            arguments: vec![],
            precondition: schema.precondition.clone(),
            effects: schema.effects.clone(),
            cost: schema.cost,
            var_types: schema.var_types.clone(),
        });
        let unique = Rc::get_mut(plan).unwrap();
        unique.steps = chain::cons(Step { id, action }, unique.steps.take());
        unique.num_steps += 1;
        ctx.register_plan(plan);
    }

    fn object(ctx: &SearchContext, name: &str) -> Object {
        ctx.problem
            .objects
            .find_object(Some(&ctx.domain.constants), name)
            .unwrap()
    }

    fn bind(ctx: &SearchContext, plan: Rc<Plan>, bindings: &[Binding]) -> Rc<Plan> {
        let updated = plan.bindings.add(&ctx.type_ctx(), bindings, false).unwrap();
        plan.with_bindings(updated)
    }

    fn eq(var: u32, step: usize, term: Term, other_step: usize) -> Binding {
        Binding::new(Variable(var), step, term, other_step, true)
    }

    #[test]
    fn factorization_proves_products_and_handles_duplicate_rows() {
        // Interleaved correlated pairs, with no independent single column.
        let mut cells = Vec::new();
        for a in 0..10 {
            for b in 0..10 {
                cells.extend([Object(a), Object(b), Object(a), Object(b)]);
            }
        }
        let table = Table::new(4, cells.clone(), 100);
        let factors = table.factors(&Cell::new(100_000));
        assert_eq!(factors.parts.len(), 2);
        assert_eq!(factors.groups, vec![0, 1, 0, 1]);
        assert!(factors.parts.iter().all(|part| part.table.rows == 10));
        let mut rebuilt = FastSet::default();
        for a in 0..10 {
            for b in 0..10 {
                let mut row = [Object(0); 4];
                for (part, id) in factors.parts.iter().zip([a, b]) {
                    for (&column, &value) in part.columns.iter().zip(part.table.tuple(id)) {
                        row[column] = value;
                    }
                }
                rebuilt.insert(row);
            }
        }
        assert!(cells
            .as_chunks::<4>()
            .0
            .iter()
            .all(|row| rebuilt.contains(row)));

        // Remove one combination, replace it with a duplicate. Raw row counts
        // still multiply, but the relation is no longer a Cartesian product.
        cells.truncate(cells.len() - 4);
        cells.extend([Object(0); 4]);
        let correlated = Table::new(4, cells, 100);
        assert!(correlated.factors(&Cell::new(100_000)).parts.is_empty());
        assert!(Table::new(0, vec![], 1)
            .factors(&Cell::new(100))
            .parts
            .is_empty());
        assert!(table.factors(&Cell::new(0)).parts.len() == 2); // already cached
        let bounded = Table::new(2, (0..200).map(Object).collect(), 100);
        assert!(bounded.factors(&Cell::new(0)).parts.is_empty());
    }

    #[test]
    fn grouped_propagation_matches_full_tables_through_binding_changes() {
        let ParsedUnit::Domain(parsed) = read_pddl(
            "(define (domain groups) (:requirements :strips :equality)
            (:predicates (pair ?a ?b) (choice ?a) (done))
            (:action product :parameters (?a ?b ?c ?d)
             :precondition (and (pair ?a ?c) (pair ?b ?d)) :effect (done))
            (:action choice :parameters (?a) :precondition (choice ?a) :effect (done)))",
        )
        .unwrap() else {
            panic!()
        };
        let domain = lower_domain(&parsed).unwrap();
        let names: Vec<_> = (0..10).map(|i| format!("o{i}")).collect();
        let facts = names
            .iter()
            .map(|s| format!("(pair {s} {s})"))
            .collect::<String>();
        let ParsedUnit::Problem(parsed) = read_pddl(&format!(
            "(define (problem test) (:domain groups) (:objects {})
             (:init {facts} (choice o0) (choice o1)) (:goal (done)))",
            names.join(" ")
        ))
        .unwrap() else {
            panic!()
        };
        let problem = lower_problem(&parsed, &domain).unwrap();
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let parent = steps(&ctx, &[0, 0, 1]);
        let cache = prepare(&ctx, &parent).unwrap();
        assert!(cache.domains.contains_key(&(1, 1)));
        assert!(!cache.domains.contains_key(&(1, 0)));
        // Cross-factor equality and inequality must both use the full relation.
        for equal in [true, false] {
            let binding = Binding::new(Variable(0), 1, Term::Variable(Variable(1)), 1, equal);
            let child = bind(&ctx, parent.clone(), &[binding]);
            assert!(propagate_incremental(&ctx, &child, Some(&cache)).is_some());
            let (_, snapshot) = run(&ctx, &child, Some(&cache), true).unwrap();
            let snapshot = snapshot.unwrap();
            assert!(snapshot.domains.contains_key(&(1, 0)));
            // Fixing one side makes the cross-group constraint unary. This
            // refinement must agree with full propagation as well.
            let child = bind(
                &ctx,
                child,
                &[eq(0, 1, Term::Object(object(&ctx, "o0")), 0)],
            );
            assert!(propagate_incremental(&ctx, &child, Some(&snapshot)).is_some());
            let (_, result) = run(&ctx, &child, Some(&snapshot), true).unwrap();
            assert!(result.unwrap().domains.contains_key(&(1, 1)));
        }
        let vars = [(0, 1), (1, 1), (2, 1), (3, 1), (0, 2), (1, 2), (0, 3)];
        let mut refinements = Vec::new();
        for &(a, sa) in &vars {
            for equal in [false, true] {
                for &(b, sb) in &vars {
                    refinements.push(Binding::new(
                        Variable(a),
                        sa,
                        Term::Variable(Variable(b)),
                        sb,
                        equal,
                    ));
                }
                for name in ["o0", "o1"] {
                    refinements.push(Binding::new(
                        Variable(a),
                        sa,
                        Term::Object(object(&ctx, name)),
                        0,
                        equal,
                    ));
                }
            }
        }
        // Compare every pair of refinements with the independent, unfactored
        // oracle, including equality cycles, external restrictions and siblings.
        for first in &refinements {
            let Some(bindings) = parent.bindings.add(&ctx.type_ctx(), &[*first], false) else {
                continue;
            };
            let child = parent.clone().with_bindings(bindings);
            let Some(bindings) = propagate_incremental(&ctx, &child, Some(&cache)) else {
                continue;
            };
            let child = child.with_bindings(bindings);
            let snapshot = prepare(&ctx, &child).unwrap();
            for next in &refinements {
                let Some(bindings) = child.bindings.add(&ctx.type_ctx(), &[*next], false) else {
                    continue;
                };
                propagate_incremental(
                    &ctx,
                    &child.clone().with_bindings(bindings),
                    Some(&snapshot),
                );
            }
        }
    }

    #[test]
    fn binding_one_parameter_forces_its_correlated_partner() {
        let (domain, problem) = task("(pair a b) (pair b c)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let a = object(&ctx, "a");
        let b = object(&ctx, "b");
        let plan = bind(&ctx, steps(&ctx, &[0]), &[eq(0, 1, Term::Object(a), 0)]);
        let result = propagate(&ctx, &plan).unwrap();
        assert_eq!(
            result.binding(Term::Variable(Variable(1)), 1),
            Term::Object(b)
        );
        assert_eq!(
            plan.bindings.binding(Term::Variable(Variable(1)), 1),
            Term::Variable(Variable(1))
        );
    }

    #[test]
    fn impossible_tuple_and_repeated_variable_are_rejected() {
        let (domain, problem) = task("(pair a b) (pair b a)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let a = Term::Object(object(&ctx, "a"));
        for bindings in [
            vec![eq(0, 1, a, 0), eq(1, 1, a, 0)],
            vec![eq(0, 1, Term::Variable(Variable(1)), 1)],
        ] {
            let plan = bind(&ctx, steps(&ctx, &[0]), &bindings);
            assert!(propagate(&ctx, &plan).is_none());
        }
    }

    #[test]
    fn non_singleton_supports_intersect_across_steps() {
        let (domain, problem) = task("(pair a a) (pair b b) (choice b) (choice c)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let plan = bind(
            &ctx,
            steps(&ctx, &[0, 1]),
            &[eq(0, 1, Term::Variable(Variable(0)), 2)],
        );
        let result = propagate(&ctx, &plan).unwrap();
        let b = Term::Object(object(&ctx, "b"));
        assert_eq!(result.binding(Term::Variable(Variable(0)), 1), b);
        assert_eq!(result.binding(Term::Variable(Variable(1)), 1), b);
        assert_eq!(result.binding(Term::Variable(Variable(0)), 2), b);
    }

    #[test]
    fn inequalities_filter_tuples_and_propagate_between_steps() {
        let (domain, problem) = task("(pair a a) (choice a) (choice b)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let inequality = Binding::new(Variable(0), 1, Term::Variable(Variable(0)), 2, false);
        let plan = bind(&ctx, steps(&ctx, &[0, 1]), &[inequality]);
        let result = propagate(&ctx, &plan).unwrap();
        assert_eq!(
            result.binding(Term::Variable(Variable(0)), 2),
            Term::Object(object(&ctx, "b"))
        );
        let within_step = Binding::new(Variable(0), 1, Term::Variable(Variable(1)), 1, false);
        let plan = bind(&ctx, steps(&ctx, &[0]), &[within_step]);
        assert!(propagate(&ctx, &plan).is_none());
    }

    #[test]
    fn oversized_relations_are_omitted_in_full() {
        let (domain, problem) = task("(pair a b) (pair b a) (choice c)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let tables = ctx.planning_graph().joint_parameter_domains_with_limit(
            &domain.actions,
            &domain.predicates,
            |ty| ctx.compatible_objects(ty),
            2,
        );
        assert!(!tables.tables.contains_key("pair-step"));
        assert_eq!(tables.tables["choice-step"].rows, 1);
        let tables = ctx.planning_graph().joint_parameter_domains_with_limit(
            &domain.actions,
            &domain.predicates,
            |ty| ctx.compatible_objects(ty),
            4,
        );
        assert_eq!(tables.tables["pair-step"].rows, 2);
        assert!(!tables.tables.contains_key("choice-step"));
    }

    #[test]
    fn propagation_preserves_every_solution_of_small_relations() {
        let names = ["a", "b"];
        for pairs in 0..16 {
            for choices in 0..4 {
                for unequal in [false, true] {
                    let mut facts = String::new();
                    let mut solutions = Vec::new();
                    for x in 0..2 {
                        if choices & (1 << x) != 0 {
                            facts.push_str(&format!("(choice {})", names[x]));
                        }
                        for y in 0..2 {
                            if pairs & (1 << (2 * x + y)) != 0 {
                                facts.push_str(&format!("(pair {} {})", names[x], names[y]));
                                if choices & (1 << x) != 0 && (!unequal || x != y) {
                                    solutions.push((x, y));
                                }
                            }
                        }
                    }
                    let (domain, problem) = task(&facts);
                    let params = Parameters::default();
                    let ctx = SearchContext::new(&domain, &problem, &params);
                    let mut constraints = vec![eq(0, 1, Term::Variable(Variable(0)), 2)];
                    if unequal {
                        constraints.push(Binding::new(
                            Variable(0),
                            1,
                            Term::Variable(Variable(1)),
                            1,
                            false,
                        ));
                    }
                    let plan = bind(&ctx, steps(&ctx, &[0, 1]), &constraints);
                    let result = propagate(&ctx, &plan);
                    if let Some(result) = result {
                        for (x, y) in solutions {
                            let objects = [
                                eq(0, 1, Term::Object(object(&ctx, names[x])), 0),
                                eq(1, 1, Term::Object(object(&ctx, names[y])), 0),
                            ];
                            assert!(result.add(&ctx.type_ctx(), &objects, true).is_some());
                        }
                    } else {
                        assert!(
                            solutions.is_empty(),
                            "lost solution for {facts}, unequal={unequal}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn unconstrained_parameters_remain_unbound() {
        let (domain, problem) = task("(pair a b) (pair b a)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let plan = steps(&ctx, &[0]);
        assert!(Rc::ptr_eq(&propagate(&ctx, &plan).unwrap(), &plan.bindings));
    }

    #[test]
    fn incremental_domains_share_unaffected_steps_and_isolate_siblings() {
        let (domain, problem) = task("(pair a a) (pair b b) (pair c c) (choice a) (choice b)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let parent = steps(&ctx, &[0, 1]);
        let cache = prepare(&ctx, &parent).unwrap();
        let mut sibling_cache = None;
        for name in ["a", "b"] {
            let child = bind(
                &ctx,
                parent.clone(),
                &[eq(0, 1, Term::Object(object(&ctx, name)), 0)],
            );
            let actual = propagate_incremental(&ctx, &child, Some(&cache));
            // Restrictions from another sibling must never leak into this one.
            let from_sibling = propagate_incremental(&ctx, &child, sibling_cache.as_ref());
            assert!(actual.is_some() && from_sibling.is_some());
            let (_, snapshot) = run(&ctx, &child, Some(&cache), true).unwrap();
            let snapshot = snapshot.unwrap();
            assert!(Rc::ptr_eq(
                &snapshot.domains[&(2, 0)],
                &cache.domains[&(2, 0)]
            ));
            assert!(!Rc::ptr_eq(
                &snapshot.domains[&(1, 0)],
                &cache.domains[&(1, 0)]
            ));
            assert_eq!(snapshot.domains[&(1, 0)].rows.len(), 1);
            sibling_cache = Some(snapshot);
        }
        assert_eq!(cache.domains[&(1, 0)].rows.len(), 3);
    }

    #[test]
    fn incremental_inequality_invalidates_every_alias() {
        let (domain, problem) = task("(choice a) (choice b)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let parent = bind(
            &ctx,
            steps(&ctx, &[1, 1, 1]),
            &[
                eq(0, 1, Term::Variable(Variable(0)), 2),
                eq(0, 3, Term::Object(object(&ctx, "a")), 0),
            ],
        );
        let cache = prepare(&ctx, &parent).unwrap();
        let child = bind(
            &ctx,
            parent,
            &[Binding::new(
                Variable(0),
                1,
                Term::Variable(Variable(0)),
                3,
                false,
            )],
        );
        let result = propagate_incremental(&ctx, &child, Some(&cache)).unwrap();
        for step in [1, 2] {
            assert_eq!(
                result.binding(Term::Variable(Variable(0)), step),
                Term::Object(object(&ctx, "b"))
            );
        }
    }

    #[test]
    fn new_step_propagates_supports_back_through_cached_constraints() {
        let (domain, problem) = task("(pair a a) (pair b b) (pair c c) (choice b) (choice c)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let equalities: Vec<_> = (1..4)
            .map(|step| eq(1, step, Term::Variable(Variable(0)), step + 1))
            .collect();
        let mut parent = bind(&ctx, steps(&ctx, &[0, 0, 0, 0]), &equalities);
        let cache = prepare(&ctx, &parent).unwrap();
        append_step(&ctx, &mut parent, 1, 5);
        let child = bind(&ctx, parent, &[eq(1, 4, Term::Variable(Variable(0)), 5)]);
        assert!(propagate_incremental(&ctx, &child, Some(&cache)).is_some());
        let (_, result) = run(&ctx, &child, Some(&cache), true).unwrap();
        let result = result.unwrap();
        for step in 1..=4 {
            assert_eq!(cache.domains[&(step, 0)].rows.len(), 3);
            assert_eq!(result.domains[&(step, 0)].rows.len(), 2);
        }
    }

    #[test]
    fn unrelated_step_histories_do_not_reuse_domains() {
        let (domain, problem) = task("(pair a b) (pair b a) (choice c)");
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let parent = steps(&ctx, &[0]);
        let cache = prepare(&ctx, &parent).unwrap();
        let other = steps(&ctx, &[1]);
        assert!(!cache.extends_steps(&other));
        let result = propagate_incremental(&ctx, &other, Some(&cache)).unwrap();
        assert_eq!(
            result.binding(Term::Variable(Variable(0)), 1),
            Term::Object(object(&ctx, "c"))
        );
    }

    #[test]
    fn cached_domains_respect_narrower_types_and_large_object_ids() {
        let ParsedUnit::Domain(parsed) = read_pddl("(define (domain typed-joint)
            (:requirements :strips :typing)
            (:types item - object special - item)
            (:predicates (pair ?x ?y - item) (choice ?x - special) (done))
            (:action pair-step :parameters (?x ?y - item) :precondition (pair ?x ?y) :effect (done))
            (:action choice-step :parameters (?x - special) :precondition (choice ?x) :effect (done)))").unwrap() else { panic!() };
        let domain = lower_domain(&parsed).unwrap();
        let fillers = (0..150)
            .map(|i| format!("f{i:03}"))
            .collect::<Vec<_>>()
            .join(" ");
        let ParsedUnit::Problem(parsed) = read_pddl(&format!(
            "(define (problem typed-test)
            (:domain typed-joint) (:objects {fillers} zordinary - item zspecial - special)
            (:init (pair zordinary zordinary) (pair zspecial zspecial) (choice zspecial))
            (:goal (done)))"
        ))
        .unwrap() else {
            panic!()
        };
        let problem = lower_problem(&parsed, &domain).unwrap();
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        let special = object(&ctx, "zspecial");
        assert!(special.0 >= 128);
        let mut parent = steps(&ctx, &[0]);
        let cache = prepare(&ctx, &parent).unwrap();
        append_step(&ctx, &mut parent, 1, 2);
        let child = bind(&ctx, parent, &[eq(0, 1, Term::Variable(Variable(0)), 2)]);
        let result = propagate_incremental(&ctx, &child, Some(&cache)).unwrap();
        for variable in [0, 1] {
            assert_eq!(
                result.binding(Term::Variable(Variable(variable)), 1),
                Term::Object(special)
            );
        }
    }

    #[test]
    fn table_memo_shares_patterns_without_mixing_constraints_and_obeys_budget() {
        let (domain, _) = task("");
        let names: Vec<_> = (0..10).map(|i| format!("o{i}")).collect();
        let mut facts = String::new();
        for x in &names {
            for y in &names {
                facts.push_str(&format!("(pair {x} {y})"));
            }
        }
        facts.push_str("(choice o0) (choice o1)");
        let ParsedUnit::Problem(parsed) = read_pddl(&format!(
            "(define (problem memo-test)
            (:domain joint) (:objects {}) (:init {facts}) (:goal (done)))",
            names.join(" ")
        ))
        .unwrap() else {
            panic!()
        };
        let problem = lower_problem(&parsed, &domain).unwrap();
        let params = Parameters::default();
        let ctx = SearchContext::new(&domain, &problem, &params);
        assert!(ctx.joint_domains().tables["pair-step"]
            .factors
            .set(Factorization::default())
            .is_ok());
        let snapshot = |value: &str| {
            let child = bind(
                &ctx,
                steps(&ctx, &[0]),
                &[eq(0, 1, Term::Object(object(&ctx, value)), 0)],
            );
            assert!(propagate(&ctx, &child).is_some());
            prepare(&ctx, &child).unwrap()
        };
        let a = snapshot("o0");
        let again = snapshot("o0");
        assert!(Rc::ptr_eq(&a.domains[&(1, 0)], &again.domains[&(1, 0)]));
        assert_eq!(a.domains[&(1, 0)].rows.len(), 10);
        let b = snapshot("o1");
        assert!(!Rc::ptr_eq(&a.domains[&(1, 0)], &b.domains[&(1, 0)]));
        let equal = bind(
            &ctx,
            steps(&ctx, &[0]),
            &[eq(0, 1, Term::Variable(Variable(1)), 1)],
        );
        let equal = prepare(&ctx, &equal).unwrap();
        assert_eq!(equal.domains[&(1, 0)].rows.len(), 10);
        let unequal = bind(
            &ctx,
            steps(&ctx, &[0]),
            &[Binding::new(
                Variable(0),
                1,
                Term::Variable(Variable(1)),
                1,
                false,
            )],
        );
        let result = propagate(&ctx, &unequal);
        assert!(result.is_some());
        let unequal = prepare(&ctx, &unequal).unwrap();
        assert_eq!(unequal.domains[&(1, 0)].rows.len(), 90);
        let tables = ctx.joint_domains();
        tables.cache_budget.bytes.set(0);
        let entries = tables.tables["pair-step"].memo.borrow().len();
        let c = snapshot("o2");
        let c_again = snapshot("o2");
        assert!(!Rc::ptr_eq(&c.domains[&(1, 0)], &c_again.domains[&(1, 0)]));
        assert_eq!(tables.tables["pair-step"].memo.borrow().len(), entries);
        assert!(Rc::ptr_eq(
            &a.domains[&(1, 0)],
            &snapshot("o0").domains[&(1, 0)]
        ));
        // A two-value support set selects a union of indexed postings. Sort
        // its row IDs before a descendant inherits them for binary searches.
        let mut parent = steps(&ctx, &[0]);
        let cache = prepare(&ctx, &parent).unwrap();
        append_step(&ctx, &mut parent, 1, 2);
        let child = bind(&ctx, parent, &[eq(0, 1, Term::Variable(Variable(0)), 2)]);
        assert!(propagate_incremental(&ctx, &child, Some(&cache)).is_some());
        let (_, propagated) = run(&ctx, &child, Some(&cache), true).unwrap();
        let propagated = propagated.unwrap();
        let rows = &propagated.domains[&(1, 0)].rows;
        assert_eq!(rows.len(), 20);
        assert!(rows.windows(2).all(|pair| pair[0] < pair[1]));
        let table = &tables.tables["pair-step"];
        for &row in rows {
            assert!([object(&ctx, "o0"), object(&ctx, "o1")].contains(&table.tuple(row)[0]));
        }
    }

    #[test]
    fn incremental_refinements_match_full_recomputation() {
        // Exercise equality, inequality, constant binding, forced singleton
        // rounds and sibling isolation over every binary two-object relation.
        for mask in 1..16 {
            let mut facts = String::from("(choice a) (choice b)");
            for (i, (x, y)) in [("a", "a"), ("a", "b"), ("b", "a"), ("b", "b")]
                .iter()
                .enumerate()
            {
                if mask & (1 << i) != 0 {
                    facts.push_str(&format!("(pair {x} {y})"));
                }
            }
            let (domain, problem) = task(&facts);
            let params = Parameters::default();
            let ctx = SearchContext::new(&domain, &problem, &params);
            let parent = steps(&ctx, &[0, 0, 1]);
            let parent = parent
                .clone()
                .with_bindings(propagate(&ctx, &parent).unwrap());
            let cache = prepare(&ctx, &parent).unwrap();
            let variables = [(0, 1), (1, 1), (0, 2), (1, 2), (0, 3)];
            let mut refinements = Vec::new();
            for &(var, step) in &variables {
                for equal in [false, true] {
                    for &(other, other_step) in &variables {
                        refinements.push(Binding::new(
                            Variable(var),
                            step,
                            Term::Variable(Variable(other)),
                            other_step,
                            equal,
                        ));
                    }
                    for name in ["a", "b"] {
                        refinements.push(Binding::new(
                            Variable(var),
                            step,
                            Term::Object(object(&ctx, name)),
                            0,
                            equal,
                        ));
                    }
                }
            }
            for refinement in &refinements {
                let Some(bindings) = parent.bindings.add(&ctx.type_ctx(), &[*refinement], false)
                else {
                    continue;
                };
                let child = parent.clone().with_bindings(bindings);
                let Some(bindings) = propagate_incremental(&ctx, &child, Some(&cache)) else {
                    continue;
                };
                let child = child.with_bindings(bindings);
                let child_cache = prepare(&ctx, &child).unwrap();
                for next in &refinements {
                    let Some(bindings) = child.bindings.add(&ctx.type_ctx(), &[*next], false)
                    else {
                        continue;
                    };
                    let grandchild = child.clone().with_bindings(bindings);
                    propagate_incremental(&ctx, &grandchild, Some(&child_cache));
                }
            }
        }
    }

    #[test]
    fn zlifo_search_matches_reference_propagation() {
        // Unit-test builds compare every propagated child with the original
        // algorithm, including cache invalidation along actual search paths.
        for (domain_name, problem_name) in [
            ("blocks-world-domain", "sussman-anomaly"),
            ("gripper-domain", "gripper-2"),
            ("briefcase-world-domain", "get-paid"),
        ] {
            let source = std::fs::read_to_string(format!("examples/{domain_name}.pddl")).unwrap();
            let ParsedUnit::Domain(parsed) = read_pddl(&source).unwrap() else {
                panic!()
            };
            let domain = lower_domain(&parsed).unwrap();
            let source = std::fs::read_to_string(format!("examples/{problem_name}.pddl")).unwrap();
            let ParsedUnit::Problem(parsed) = read_pddl(&source).unwrap() else {
                panic!()
            };
            let problem = lower_problem(&parsed, &domain).unwrap();
            let params = Parameters {
                flaw_orders: vec![crate::heuristics::FlawSelectionOrder::parse("ZLIFO").unwrap()],
                heuristic: crate::heuristics::Heuristic::parse("ADD/LIFO").unwrap(),
                prune: crate::pruning::PruneOptions {
                    joint: true,
                    ..Default::default()
                },
                search_limits: vec![10_000],
                ..Parameters::default()
            };
            let ctx = SearchContext::new(&domain, &problem, &params);
            let crate::search::Outcome::Solved(solution) = crate::search::plan(&ctx) else {
                panic!("joint propagation failed on {problem_name}")
            };
            crate::validate::is_valid_solution(&solution, &ctx).unwrap();
            crate::validate::is_executable_solution(&solution, &ctx).unwrap();
        }
    }
}
