//! Compiler tests: the lifted FDR rewrite agrees with STRIPS semantics on
//! random walks from the initial state.
use std::collections::{HashMap, HashSet};

use super::task::{objects_of, LValue, LiftedTask};
use crate::domain::Domain;
use crate::formula::{Atom, Formula, Literal};
use crate::parser::{lower_domain, lower_problem, read_pddl, ParsedUnit};
use crate::problem::Problem;
use crate::terms::{Object, Term, Variable};

pub(crate) fn load(domain_src: &str, problem_src: &str) -> (Domain, Problem) {
    let domain = match read_pddl(domain_src).expect("parse domain") {
        ParsedUnit::Domain(d) => lower_domain(&d).expect("lower domain"),
        _ => panic!("expected a domain"),
    };
    let problem = match read_pddl(problem_src).expect("parse problem") {
        ParsedUnit::Problem(p) => lower_problem(&p, &domain).expect("lower problem"),
        _ => panic!("expected a problem"),
    };
    (domain, problem)
}

fn subst(term: Term, s: &[Option<Object>]) -> Option<Object> {
    match term {
        Term::Object(o) => Some(o),
        Term::Variable(v) => s.get(v.0 as usize).copied().flatten(),
    }
}

fn ground(atom: &Atom, s: &[Option<Object>]) -> Atom {
    Atom {
        predicate: atom.predicate,
        terms: atom
            .terms
            .iter()
            .map(|t| Term::Object(subst(*t, s).expect("bound")))
            .collect(),
    }
}

/// Every full substitution of `parameters` that makes all `positive` atoms
/// members of `atoms`: a naive join, then a type product for the rest.
fn substitutions(
    domain: &Domain,
    problem: &Problem,
    parameters: &[Variable],
    var_types: &[crate::types::Type],
    positive: &[Atom],
    atoms: &HashSet<Atom>,
) -> Vec<Vec<Option<Object>>> {
    let mut by_predicate: HashMap<_, Vec<&Atom>> = HashMap::new();
    for a in atoms {
        by_predicate.entry(a.predicate).or_default().push(a);
    }
    let mut out = Vec::new();
    let mut s = vec![None; var_types.len()];
    fn join(
        k: usize,
        positive: &[Atom],
        by_predicate: &HashMap<crate::predicates::Predicate, Vec<&Atom>>,
        s: &mut Vec<Option<Object>>,
        rest: &mut dyn FnMut(&mut Vec<Option<Object>>),
    ) {
        if k == positive.len() {
            rest(s);
            return;
        }
        let atom = &positive[k];
        for candidate in by_predicate.get(&atom.predicate).into_iter().flatten() {
            let saved = s.clone();
            let mut ok = true;
            for (t, c) in atom.terms.iter().zip(&candidate.terms) {
                let c = c.as_object();
                match *t {
                    Term::Object(o) => ok &= o == c,
                    Term::Variable(v) => match s[v.0 as usize] {
                        Some(o) => ok &= o == c,
                        None => s[v.0 as usize] = Some(c),
                    },
                }
                if !ok {
                    break;
                }
            }
            if ok {
                join(k + 1, positive, by_predicate, s, rest);
            }
            *s = saved;
        }
    }
    let domains: Vec<Vec<Object>> = parameters
        .iter()
        .map(|v| objects_of(domain, problem, var_types[v.0 as usize]))
        .collect();
    let mut rest = |s: &mut Vec<Option<Object>>| {
        fn product(
            i: usize,
            parameters: &[Variable],
            domains: &[Vec<Object>],
            s: &mut Vec<Option<Object>>,
            out: &mut Vec<Vec<Option<Object>>>,
        ) {
            if i == parameters.len() {
                out.push(s.clone());
                return;
            }
            let v = parameters[i].0 as usize;
            if let Some(o) = s[v] {
                if domains[i].contains(&o) {
                    product(i + 1, parameters, domains, s, out);
                }
                return;
            }
            for &o in &domains[i] {
                s[v] = Some(o);
                product(i + 1, parameters, domains, s, out);
            }
            s[v] = None;
        }
        product(0, parameters, &domains, s, &mut out);
    };
    join(0, positive, &by_predicate, &mut s, &mut rest);
    out.sort();
    out.dedup();
    out
}

fn literals(f: &Formula, out: &mut Vec<Formula>) {
    match f {
        Formula::Conjunction(fs) => fs.iter().for_each(|f| literals(f, out)),
        Formula::True => {}
        other => out.push(other.clone()),
    }
}

fn holds_strips(f: &Formula, s: &[Option<Object>], atoms: &HashSet<Atom>) -> bool {
    match f {
        Formula::True => true,
        Formula::False => false,
        Formula::Atom(a) => atoms.contains(&ground(a, s)),
        Formula::Negation(a) => !atoms.contains(&ground(a, s)),
        Formula::Equality { left, right, .. } => subst(*left, s) == subst(*right, s),
        Formula::Inequality { left, right, .. } => subst(*left, s) != subst(*right, s),
        Formula::Conjunction(fs) => fs.iter().all(|f| holds_strips(f, s, atoms)),
        Formula::Disjunction(fs) => fs.iter().any(|f| holds_strips(f, s, atoms)),
        _ => panic!("unsupported formula in oracle"),
    }
}

type FdrState = HashMap<(u32, Vec<Object>), LValue>;

fn ground_value(value: &LValue, s: &[Option<Object>]) -> LValue {
    match value {
        LValue::None => LValue::None,
        LValue::Part { part, args } => LValue::Part {
            part: *part,
            args: args
                .iter()
                .map(|t| Term::Object(subst(*t, s).unwrap()))
                .collect(),
        },
    }
}

fn instance(inv: &[Term], s: &[Option<Object>]) -> Vec<Object> {
    inv.iter().map(|t| subst(*t, s).unwrap()).collect()
}

fn fdr_applicable(
    task: &LiftedTask,
    schema: usize,
    s: &[Option<Object>],
    state: &FdrState,
) -> bool {
    let sc = &task.schemas[schema];
    sc.conditions.iter().all(|c| {
        let current = state
            .get(&(c.var, instance(&c.inv, s)))
            .cloned()
            .unwrap_or(LValue::None);
        current == ground_value(&c.value, s)
    }) && sc
        .statics
        .iter()
        .all(|a| task.static_atoms.contains(&ground(a, s)))
        && sc
            .negated_statics
            .iter()
            .all(|a| !task.static_atoms.contains(&ground(a, s)))
        && sc
            .equalities
            .iter()
            .all(|(l, r)| subst(*l, s) == subst(*r, s))
        && sc
            .inequalities
            .iter()
            .all(|(l, r)| subst(*l, s) != subst(*r, s))
}

fn fdr_apply(task: &LiftedTask, schema: usize, s: &[Option<Object>], state: &FdrState) -> FdrState {
    let mut next = state.clone();
    for a in &task.schemas[schema].assigns {
        let key = (a.fact.var, instance(&a.fact.inv, s));
        match ground_value(&a.fact.value, s) {
            LValue::None => {
                next.remove(&key);
            }
            v => {
                next.insert(key, v);
            }
        }
    }
    next
}

fn fdr_atoms(task: &LiftedTask, state: &FdrState) -> HashSet<Atom> {
    state
        .iter()
        .map(|((var, inv), value)| {
            task.atom_of(&super::task::LFact {
                var: *var,
                inv: inv.iter().map(|o| Term::Object(*o)).collect(),
                value: value.clone(),
            })
            .unwrap()
        })
        .collect()
}

/// Random walks: at each state, STRIPS-applicable and FDR-applicable ground
/// actions coincide and their successors agree. Returns states visited.
pub(crate) fn check_random_walks(
    domain: &Domain,
    problem: &Problem,
    walks: usize,
    depth: usize,
) -> usize {
    let task = LiftedTask::compile(domain, problem).expect("compile");
    let fluent: HashSet<_> = task.covered.keys().copied().collect();
    let mut seed = 0x2545F4914F6CDD1Du64;
    let mut rand = move |n: usize| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        (seed % n as u64) as usize
    };
    let mut visited = 0;
    for _ in 0..walks {
        let mut strips: HashSet<Atom> = problem.init_atoms.clone();
        let mut fdr: FdrState = task.init.clone().into_iter().collect();
        for _ in 0..depth {
            visited += 1;
            let fluent_atoms: HashSet<Atom> = strips
                .iter()
                .filter(|a| fluent.contains(&a.predicate))
                .cloned()
                .collect();
            assert_eq!(fluent_atoms, fdr_atoms(&task, &fdr), "states diverged");
            let mut successors = Vec::new();
            for (index, action) in domain.actions.iter().enumerate() {
                let mut lits = Vec::new();
                literals(&action.precondition, &mut lits);
                let positive: Vec<Atom> = lits
                    .iter()
                    .filter_map(|l| match l {
                        Formula::Atom(a) => Some(a.clone()),
                        _ => None,
                    })
                    .collect();
                let strips_ok: Vec<_> = substitutions(
                    domain,
                    problem,
                    &action.parameters,
                    &action.var_types,
                    &positive,
                    &strips,
                )
                .into_iter()
                .filter(|s| holds_strips(&action.precondition, s, &strips))
                .collect();
                // Every DNF schema of this action, with its applicable
                // substitutions.
                let mut all = fdr_atoms(&task, &fdr);
                all.extend(task.static_atoms.iter().cloned());
                let mut fdr_ok: Vec<(usize, Vec<Option<Object>>)> = Vec::new();
                for (schema_index, schema) in task
                    .schemas
                    .iter()
                    .enumerate()
                    .filter(|(_, s)| s.action == index)
                {
                    let mut fdr_positive: Vec<Atom> = schema
                        .conditions
                        .iter()
                        .filter_map(|c| task.atom_of(c))
                        .collect();
                    fdr_positive.extend(schema.statics.iter().cloned());
                    for sub in substitutions(
                        domain,
                        problem,
                        &schema.parameters,
                        &task.var_types,
                        &fdr_positive,
                        &all,
                    ) {
                        if fdr_applicable(&task, schema_index, &sub, &fdr) {
                            fdr_ok.push((schema_index, sub));
                        }
                    }
                }
                let schema_index = task.schemas.iter().position(|s| s.action == index).unwrap();
                let schema = &task.schemas[schema_index];
                let tuple = |params: &[Variable], s: &Vec<Option<Object>>| -> Vec<Object> {
                    params.iter().map(|v| s[v.0 as usize].unwrap()).collect()
                };
                let strips_tuples: Vec<Vec<Object>> = strips_ok
                    .iter()
                    .map(|s| tuple(&action.parameters, s))
                    .collect();
                let mut fdr_tuples: Vec<Vec<Object>> = fdr_ok
                    .iter()
                    .map(|(i, s)| tuple(&task.schemas[*i].parameters, s))
                    .collect();
                let mut sorted = strips_tuples.clone();
                sorted.sort();
                fdr_tuples.sort();
                fdr_tuples.dedup();
                assert_eq!(
                    sorted, fdr_tuples,
                    "applicability differs for {}",
                    action.name
                );
                for (s, args) in strips_ok.into_iter().zip(strips_tuples) {
                    let mut global = vec![None; task.var_types.len()];
                    for (v, o) in schema.parameters.iter().zip(&args) {
                        global[v.0 as usize] = Some(*o);
                    }
                    let mut next = strips.clone();
                    for e in &action.effects {
                        if let Literal::Negation(a) = &e.literal {
                            next.remove(&ground(a, &s));
                        }
                    }
                    for e in &action.effects {
                        if let Literal::Atom(a) = &e.literal {
                            next.insert(ground(a, &s));
                        }
                    }
                    successors.push((next, fdr_apply(&task, schema_index, &global, &fdr)));
                }
            }
            if successors.is_empty() {
                break;
            }
            let (s, f) = successors.swap_remove(rand(successors.len()));
            strips = s;
            fdr = f;
        }
    }
    visited
}

const GRIPPER_DOMAIN: &str = "(define (domain gripper-strips)
 (:predicates (room ?r) (ball ?b) (gripper ?g) (at-robby ?r) (at ?b ?r) (free ?g) (carry ?o ?g))
 (:action move :parameters (?from ?to)
   :precondition (and (room ?from) (room ?to) (at-robby ?from))
   :effect (and (at-robby ?to) (not (at-robby ?from))))
 (:action pick :parameters (?obj ?room ?gripper)
   :precondition (and (ball ?obj) (room ?room) (gripper ?gripper) (at ?obj ?room) (at-robby ?room) (free ?gripper))
   :effect (and (carry ?obj ?gripper) (not (at ?obj ?room)) (not (free ?gripper))))
 (:action drop :parameters (?obj ?room ?gripper)
   :precondition (and (ball ?obj) (room ?room) (gripper ?gripper) (carry ?obj ?gripper) (at-robby ?room))
   :effect (and (at ?obj ?room) (free ?gripper) (not (carry ?obj ?gripper)))))";

const GRIPPER_PROBLEM: &str = "(define (problem g2) (:domain gripper-strips)
 (:objects rooma roomb ball1 ball2 left right)
 (:init (room rooma) (room roomb) (ball ball1) (ball ball2) (gripper left) (gripper right)
   (at-robby rooma) (free left) (free right) (at ball1 rooma) (at ball2 rooma))
 (:goal (and (at ball1 roomb) (at ball2 roomb))))";

#[test]
fn gripper_compiles_to_multi_valued_variables() {
    let (domain, problem) = load(GRIPPER_DOMAIN, GRIPPER_PROBLEM);
    let task = LiftedTask::compile(&domain, &problem).unwrap();
    let pred = |n: &str| domain.predicates.find_predicate(n).unwrap();
    let (robby, _) = task.covered[&pred("at-robby")];
    let (at, _) = task.covered[&pred("at")];
    let (carry, _) = task.covered[&pred("carry")];
    // A ball is in a room or in a gripper: one variable per ball.
    assert_eq!(at, carry, "at and carry share the ball variable");
    assert_eq!(task.vars[robby as usize].arity, 0);
    assert!(!task.vars[robby as usize].binary);
    // move rewrites to one assignment whose pre is the at-robby condition.
    let mv = task.schemas.iter().find(|s| s.name == "move").unwrap();
    assert_eq!(mv.assigns.len(), 1);
    assert!(mv.assigns[0].pre.is_some());
    assert_eq!(mv.statics.len(), 2);
}

#[test]
fn gripper_random_walks_agree_with_strips() {
    let (domain, problem) = load(GRIPPER_DOMAIN, GRIPPER_PROBLEM);
    assert!(check_random_walks(&domain, &problem, 20, 30) > 20);
}

/// Compile every agile-suite domain's p01 and check random walks on those that
/// compile. Run with `--ignored --nocapture`; SUITE overrides the location.
#[test]
#[ignore]
fn suite_compiles_and_agrees() {
    let suite = std::env::var("SUITE").unwrap_or_else(|_| "../autoscale-unitcost/agile".into());
    let mut domains: Vec<_> = std::fs::read_dir(&suite)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    domains.sort();
    let (mut ok, mut total) = (0, 0);
    for dir in domains {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let problem_path = dir.join("p01.pddl");
        let domain_path = if dir.join("domain-p01.pddl").exists() {
            dir.join("domain-p01.pddl")
        } else {
            dir.join("domain.pddl")
        };
        let (Ok(d), Ok(p)) = (
            std::fs::read_to_string(&domain_path),
            std::fs::read_to_string(&problem_path),
        ) else {
            continue;
        };
        total += 1;
        let (domain, problem) = load(&d, &p);
        match LiftedTask::compile(&domain, &problem) {
            Err(e) => println!("{name:28} REJECT {}", e.0),
            Ok(task) => {
                ok += 1;
                let multi = task.vars.iter().filter(|v| !v.binary).count();
                let states = check_random_walks(&domain, &problem, 3, 15);
                println!(
                    "{name:28} ok: {} vars ({} multi-valued), {} schemas, walks {} states agree",
                    task.vars.len(),
                    multi,
                    task.schemas.len(),
                    states
                );
            }
        }
    }
    println!("compiled {ok}/{total}");
}

/// Print the synthesised groups and the chosen cover for DIAG_DOMAIN.
#[test]
#[ignore]
fn print_groups() {
    let Ok(dir) = std::env::var("DIAG_DOMAIN") else {
        return;
    };
    let dir = std::path::Path::new(&dir);
    let domain_path = if dir.join("domain-p01.pddl").exists() {
        dir.join("domain-p01.pddl")
    } else {
        dir.join("domain.pddl")
    };
    let (domain, problem) = load(
        &std::fs::read_to_string(domain_path).unwrap(),
        &std::fs::read_to_string(dir.join("p01.pddl")).unwrap(),
    );
    let task = LiftedTask::compile(&domain, &problem).unwrap();
    for v in &task.vars {
        println!(
            "var {} arity {} binary {} none {}",
            v.name, v.arity, v.binary, v.has_none
        );
    }
}

fn solve_config(
    domain: &Domain,
    problem: &Problem,
    kind: super::heuristic::Kind,
) -> (super::Outcome, super::Stats) {
    let config = super::Config {
        lanes: vec![super::Lane {
            name: "test".into(),
            flaw_order: crate::heuristics::FlawSelectionOrder::parse("ZLIFO").unwrap(),
            heuristic: kind,
            degree_binding: false,
        }],
        node_limit: 200_000,
        ..super::Config::default()
    };
    super::solve(domain, problem, &config).expect("supported")
}

#[test]
fn gripper_solves_with_open_condition_count() {
    let (domain, problem) = load(GRIPPER_DOMAIN, GRIPPER_PROBLEM);
    let (outcome, stats) = solve_config(&domain, &problem, super::heuristic::Kind::Oc);
    match outcome {
        super::Outcome::Solved(solution) => {
            super::search::validate(&domain, &problem, &solution).unwrap();
            assert!(
                solution.actions.len() >= 5,
                "{}",
                solution.format(&domain, &problem)
            );
        }
        _ => panic!("not solved: {stats:?}"),
    }
}

/// Solve DIAG_DOMAIN's DIAG_PROBLEM (default p01) and print the plan.
#[test]
#[ignore]
fn solve_diag() {
    let Ok(dir) = std::env::var("DIAG_DOMAIN") else {
        return;
    };
    let dir = std::path::Path::new(&dir);
    let instance = std::env::var("DIAG_PROBLEM").unwrap_or_else(|_| "p01".into());
    let domain_path = if dir.join(format!("domain-{instance}.pddl")).exists() {
        dir.join(format!("domain-{instance}.pddl"))
    } else {
        dir.join("domain.pddl")
    };
    let (domain, problem) = load(
        &std::fs::read_to_string(domain_path).unwrap(),
        &std::fs::read_to_string(dir.join(format!("{instance}.pddl"))).unwrap(),
    );
    let start = std::time::Instant::now();
    let config = super::Config {
        node_limit: std::env::var("DIAG_NODES")
            .ok()
            .and_then(|n| n.parse().ok())
            .unwrap_or(1_000_000),
        ..super::Config::default()
    };
    let (outcome, stats) = super::solve(&domain, &problem, &config).expect("supported");
    match outcome {
        super::Outcome::Solved(s) => println!(
            "solved cost {} in {:?}\n{}",
            s.cost,
            start.elapsed(),
            s.format(&domain, &problem)
        ),
        super::Outcome::NoSolution => println!("no solution"),
        super::Outcome::LimitReached => println!("limit"),
    }
    println!("{stats:?} {:?}", start.elapsed());
}
