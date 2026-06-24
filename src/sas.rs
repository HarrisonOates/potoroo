//! A minimal finite-domain (FDR / SAS⁺) task representation and encoder, plus a
//! direct path to Fast Downward's `downward` C++ binary.
//!
//! This is the fast heuristic-evaluation path for the causal-link compilation
//! (Phase 1-opt): instead of emitting PDDL and paying Fast Downward's Python
//! translator on every search node (~95% of the per-node cost — measured 202 ms
//! translate vs 9 ms search), we ground the compiled task ourselves and write
//! FD's *input* representation (SAS⁺) directly, invoking only `downward`.
//!
//! Encoding choice: **all-binary**. Every ground fact becomes its own two-valued
//! SAS⁺ variable (`Atom <name>` = value 0 = true, `NegatedAtom <name>` = value 1
//! = false). This skips the translator's mutex-group / invariant synthesis; the
//! resulting task is valid (FD heuristics work on it, just without mutex
//! information). Grounding the compiled task — including folding the polynomial
//! causal-link guards into ground preconditions — lives in `crate::compile`.

use std::fmt::Write;

use crate::external::{run_downward_sas, run_h_server_eval, FdError, FdHeuristic, HResult};

/// A ground finite-domain task over boolean facts.
#[derive(Debug, Clone, Default)]
pub struct GroundTask {
    /// Fact names, indexed by fact id (rendered as the SAS⁺ `Atom` label).
    facts: Vec<String>,
    /// Initial truth value of each fact (parallel to `facts`).
    init: Vec<bool>,
    /// Goal: each `(fact, required-truth)`.
    goal: Vec<(usize, bool)>,
    /// Operators.
    ops: Vec<GroundOp>,
}

/// A ground operator: a conjunctive precondition and a set of (optionally
/// conditional) effects over boolean facts.
#[derive(Debug, Clone)]
pub struct GroundOp {
    pub name: String,
    /// Precondition: each `(fact, required-truth)`.
    pub pre: Vec<(usize, bool)>,
    /// Effects.
    pub effects: Vec<GroundEffect>,
}

/// A ground effect: set `fact` to `value` when all `cond` facts hold as given.
/// An empty `cond` is an unconditional effect.
#[derive(Debug, Clone)]
pub struct GroundEffect {
    pub cond: Vec<(usize, bool)>,
    pub fact: usize,
    pub value: bool,
}

impl GroundTask {
    pub fn new() -> Self {
        GroundTask::default()
    }

    /// Interns a fact name, returning its id. `init` is its initial truth.
    pub fn add_fact(&mut self, name: impl Into<String>, init: bool) -> usize {
        let id = self.facts.len();
        self.facts.push(name.into());
        self.init.push(init);
        id
    }

    pub fn set_init(&mut self, fact: usize, value: bool) {
        self.init[fact] = value;
    }

    pub fn add_goal(&mut self, fact: usize, value: bool) {
        self.goal.push((fact, value));
    }

    pub fn add_op(&mut self, op: GroundOp) {
        self.ops.push(op);
    }

    /// Mutable access to the operators (used to fold per-node causal-link guards
    /// into the cached, constant original-action operators).
    pub fn ops_mut(&mut self) -> &mut [GroundOp] {
        &mut self.ops
    }

    pub fn num_facts(&self) -> usize {
        self.facts.len()
    }

    /// Initial truth of every fact (parallel to fact ids). Used by the Lplan LP.
    pub fn init(&self) -> &[bool] {
        &self.init
    }

    /// Goal as `(fact, required-truth)` pairs. Used by the Lplan LP.
    pub fn goal(&self) -> &[(usize, bool)] {
        &self.goal
    }

    /// The operators. Used by the Lplan LP.
    pub fn ops(&self) -> &[GroundOp] {
        &self.ops
    }

    pub fn num_ops(&self) -> usize {
        self.ops.len()
    }

    /// Encodes the task as an all-binary SAS⁺ string (FD format version 3).
    pub fn to_sas(&self) -> String {
        // Boolean encoding: value 0 = Atom (true), value 1 = NegatedAtom (false).
        let v = |truth: bool| if truth { 0 } else { 1 };

        let mut s = String::new();
        s.push_str("begin_version\n3\nend_version\n");
        s.push_str("begin_metric\n0\nend_metric\n");

        // Variables (one binary variable per fact; var index = fact id).
        let _ = writeln!(s, "{}", self.facts.len());
        for (i, name) in self.facts.iter().enumerate() {
            s.push_str("begin_variable\n");
            let _ = writeln!(s, "var{i}");
            s.push_str("-1\n2\n");
            let _ = writeln!(s, "Atom {name}");
            let _ = writeln!(s, "NegatedAtom {name}");
            s.push_str("end_variable\n");
        }

        // No mutex groups.
        s.push_str("0\n");

        // Initial state.
        s.push_str("begin_state\n");
        for &t in &self.init {
            let _ = writeln!(s, "{}", v(t));
        }
        s.push_str("end_state\n");

        // Goal.
        s.push_str("begin_goal\n");
        let _ = writeln!(s, "{}", self.goal.len());
        for &(f, t) in &self.goal {
            let _ = writeln!(s, "{} {}", f, v(t));
        }
        s.push_str("end_goal\n");

        // Operators.
        let _ = writeln!(s, "{}", self.ops.len());
        for op in &self.ops {
            s.push_str(&op.to_sas(v));
        }

        // No axioms.
        s.push_str("0\n");
        s
    }

    /// Evaluates a heuristic on the initial state. Prefers the persistent
    /// `downward --h-server` process (no per-task spawn or search); falls back to
    /// the one-shot `downward` binary if the server cannot be started.
    pub fn heuristic(&self, heur: FdHeuristic) -> Result<HResult, FdError> {
        let sas = self.to_sas();
        match run_h_server_eval(&sas, heur) {
            Ok(v) => Ok(v),
            Err(_) => run_downward_sas(&sas, heur),
        }
    }
}

impl GroundOp {
    fn to_sas(&self, v: impl Fn(bool) -> u8) -> String {
        // Facts that appear in some effect are encoded *in* that effect (with
        // their `pre` value); the rest of the precondition is "prevail".
        use std::collections::HashMap;
        let effect_facts: std::collections::HashSet<usize> =
            self.effects.iter().map(|e| e.fact).collect();
        let pre_val: HashMap<usize, bool> = self.pre.iter().map(|&(f, t)| (f, t)).collect();

        let mut s = String::new();
        s.push_str("begin_operator\n");
        let _ = writeln!(s, "{}", self.name);

        // Prevail conditions: preconditions on facts not modified by the op.
        let prevail: Vec<&(usize, bool)> =
            self.pre.iter().filter(|(f, _)| !effect_facts.contains(f)).collect();
        let _ = writeln!(s, "{}", prevail.len());
        for &&(f, t) in &prevail {
            let _ = writeln!(s, "{} {}", f, v(t));
        }

        // Effects.
        let _ = writeln!(s, "{}", self.effects.len());
        for e in &self.effects {
            let pre = pre_val.get(&e.fact).map(|&t| v(t) as i32).unwrap_or(-1);
            let mut line = format!("{}", e.cond.len());
            for &(cf, ct) in &e.cond {
                let _ = write!(line, " {} {}", cf, v(ct));
            }
            let _ = writeln!(s, "{line} {} {} {}", e.fact, pre, v(e.value));
        }

        // Unit cost (metric 0).
        s.push_str("1\n");
        s.push_str("end_operator\n");
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::external::downward_available;

    /// A trivial task: one fact, false in init, true in goal, one op that sets
    /// it. FF/hmax of the initial state must be 1. Verifies the FDR encoding and
    /// the `downward` invocation against the frozen binary.
    #[test]
    fn one_step_task_h_is_one() {
        if !downward_available() {
            eprintln!("skipping: downward binary not available");
            return;
        }
        let mut t = GroundTask::new();
        let p = t.add_fact("p", false);
        t.add_goal(p, true);
        t.add_op(GroundOp {
            name: "make-p".to_string(),
            pre: vec![],
            effects: vec![GroundEffect { cond: vec![], fact: p, value: true }],
        });
        assert_eq!(t.heuristic(FdHeuristic::Ff).unwrap(), HResult::Finite(1.0));
        assert_eq!(t.heuristic(FdHeuristic::HMax).unwrap(), HResult::Finite(1.0));
    }

    /// A two-step chain: goal needs `q`, `q` needs `p`. h^max = 2.
    #[test]
    fn two_step_chain() {
        if !downward_available() {
            eprintln!("skipping: downward binary not available");
            return;
        }
        let mut t = GroundTask::new();
        let p = t.add_fact("p", false);
        let q = t.add_fact("q", false);
        t.add_goal(q, true);
        t.add_op(GroundOp {
            name: "a1".to_string(),
            pre: vec![],
            effects: vec![GroundEffect { cond: vec![], fact: p, value: true }],
        });
        t.add_op(GroundOp {
            name: "a2".to_string(),
            pre: vec![(p, true)],
            effects: vec![GroundEffect { cond: vec![], fact: q, value: true }],
        });
        assert_eq!(t.heuristic(FdHeuristic::HMax).unwrap(), HResult::Finite(2.0));
    }

    /// Goal already satisfied in the initial state ⇒ h = 0.
    #[test]
    fn goal_satisfied_h_zero() {
        if !downward_available() {
            eprintln!("skipping: downward binary not available");
            return;
        }
        let mut t = GroundTask::new();
        let p = t.add_fact("p", true);
        t.add_goal(p, true);
        assert_eq!(t.heuristic(FdHeuristic::Ff).unwrap(), HResult::Finite(0.0));
    }
}
