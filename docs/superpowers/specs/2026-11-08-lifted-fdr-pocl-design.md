# Lifted FDR POCL planner — design

Status: draft, 2026-11-08. Branch `investigate/relax-vs-add`.

## Goal

A refinement-based POCL planner whose steps are lifted (schema plus binding
constraints) and whose conditions and effects are over **lifted state
variables** derived from lifted mutex groups. Target: FDR-mode coverage
(cluster FDR ZLIFO ADD/LIFO 193 of 1,260; lifted STRIPS 70; ground 98) while
keeping lifted least commitment.

### Why

With the same heuristic and flaw order, FDR needs 30× fewer nodes than ground
STRIPS on gripper p04 (8,943 vs 267,765 generated). On childsnack p04, FDR
solves in 59,703 nodes, while ground has generated over 15M nodes without
solving. FDR also prunes about a third of children as dead. The cause is the representation: when
`pick(b2,left)` writes the gripper variable, it immediately threatens a link on
`carry(b1,left)`. In STRIPS it only deletes `free(left)`, so the conflict is
found much later. The cluster per-domain gap (gripper 30/12/0,
childsnack 30/2/2, airport 12/0/0, FDR/ground/lifted) is concentrated where
this applies.

The operator-class idea was measured negative first
(`investigation/op-classes/findings.md`).

### Literature

* Helmert, *Concise finite-domain representations for PDDL planning tasks*, AIJ 2009:
  schematic variables `G(fixed params)`, values are the group's atoms over the
  counted parameters plus `<none>`, and the operator rewrite.
* Fišer, *Lifted fact-alternating mutex groups and pruned grounding*, AAAI 2020:
  defines lifted fam-groups. These are the groups already synthesised by
  `src/lifted_mutex.rs`.
* Bit-Monnot et al., *FAPE*, 2020: lifted state-variable causal links, where any
  possibly co-designating writer threatens, and the binding-constraint network.
* Younes & Simmons, AIPS 2002: joint parameter domains (`src/joint_domains.rs`).
* Joslin & Pollack 1996 and Vidal & Geffner 2006: forced supporter and forced
  threat propagation.
* Corrêa et al., ICAPS 2021 and AAAI 2022: lifted h_add and FF. These are a later
  option for heuristics that avoid grounding.

No published lifted SAS+ POCL planner or lifted DTG/flow heuristic exists.

## Non-goals (v1)

* PDDL beyond conjunctive preconditions over positive atoms, negated atoms of
  binary variables, (in)equality, and unconditional effects. Domains with
  conditional or quantified effects, disjunction, `exists`, or negated group
  atoms are rejected with a clear error (`use --fdr-pocl`). The supported share
  of the suite is measured and reported in phase 1.
* Action costs other than unit and constant per schema.
* Changes to the existing FDR, ground, or lifted planners. Defaults and
  published configurations stay unchanged. The new planner is opt-in
  (`--lifted-fdr`).

## Architecture

New module tree `src/lifted_fdr/`, independent of `fdr_pocl.rs`. It reuses
`chain`, `orderings`, `rank`, `memory`, `bindings`, the flaw-order DSL in
`heuristics.rs`, `lifted_mutex`, and `validate`. The FDR search skeleton is
copied and adapted rather than made generic. Making `fdr_pocl.rs` generic over
step and fact types would put its exact behaviour at risk. Shared extraction can
follow once both planners are stable.

| File | Purpose |
|---|---|
| `task.rs` | Lifted task compiler: variables, schema rewrite, statics, init |
| `plan.rs` | Partial plan: steps, bindings, links, open conditions, threats, orderings |
| `refine.rs` | Open-condition and threat refinements |
| `ground.rs` | Ground view for heuristics: reachable ground actions and facts, ADD table |
| `heuristic.rs` | Plan ranking: OC, ADD (binding-aware, with reuse), later TADD/FLOW |
| `search.rs` | A*, GBFS, PEA, per-queue flaw orders, limits, completion |
| `mod.rs` | Public entry `solve(domain, problem, params)` |

### 1. Lifted task (`task.rs`)

**Variables.** Start from `LiftedMutexes::synthesise`. Choose a cover so that
each predicate argument pattern belongs to one variable:

* Greedy, largest group first, as in FD's translator.
* Uncovered fluent predicates become *binary variables*: a one-part group whose
  arguments are all invariant, with values `{true, none}`.
* Predicates that no effect mentions are **static**. They are not variables.

`LVar { params: Vec<Type>, parts: Vec<Part>, has_none: bool }`. `has_none` is
false only when the group is proved exactly-one:

* every instance has exactly one member initially, and
* every schema that deletes a member adds a member of the same instance.

Values: `LValue::None | LValue::Part { part: u16, args: Vec<Term> }`. The args
are over the counted slots.

**Facts.** `LFact { var, inv: Vec<Term>, value: LValue }`, written
`var(inv) = value`. A ground fact has only objects as terms.

**Schema rewrite** (Helmert §5), per `ActionSchema`:

| Source | Becomes |
|---|---|
| Positive atom over a variable part | condition `var(inv)=Part(p, counted)` |
| Positive atom over a static predicate | static constraint on the step |
| Negated atom of a binary variable | condition `var(inv)=none` |
| `=` / `≠` | step binding constraint |
| Add effect | assignment `var(inv) := Part(p, counted)` |
| Delete with no add to the syntactically same instance | assignment `:= none` (requires `has_none`) |
| Delete paired with an add on the same instance | dropped; the add's assignment carries a `pre` |

`pre` is the deleted value when it is also a precondition. A condition on a
variable the schema does not assign is a *prevail*.

If two effects assign the same variable with non-identical instance terms, the
schema is rejected in v1.

`LSchema { name, params, conditions: Vec<LFact>, statics: Vec<Atom>,
assignments: Vec<Assign{fact: LFact, pre: Option<usize>}>, eqs, neqs, cost }`.

**Init and goal.**
* Init is a set of ground facts. For each variable instance it is either the one
  true member, or `none`.
* Instances are enumerated over the variable's parameter types. That is
  finite, but a large variable would make it expensive. Instances whose value is
  `none` are stored implicitly: absent from the map means `none`.
* The goal is a conjunction of `LFact`s. Negative goals are allowed for binary
  variables only.

**Correctness oracle (test).** Ground the compiled task over the reachable
ground actions. Then take random walks from init and check two things at
each step:
* the STRIPS successor (adds over deletes) equals the FDR successor;
* the STRIPS and FDR applicability verdicts agree.

### 2. Partial plan (`plan.rs`)

* Steps: `LStep { id, schema }`. Step variables are `(Variable, step_id)` in a
  shared `Rc<Bindings>`. Step 0 is init, step 1 is goal, as in the other
  planners.
* Causal link: `{ producer, consumer, cond: (step, condition index), assign:
  Option<usize> }`. Link compatibility is enforced by bindings: `inv` terms are
  pairwise equal and value args are pairwise equal, with the same part. A `none`
  link is compatible only with a `none` producer.
* Init links bind the consumer's terms to the objects of one ground init fact.
  A `none` condition is supported by init only through an instance absent from
  the init map. In v1 that means one child per such instance consistent with
  the bindings.
* Open conditions: `(consumer, condition index)`.
* Orderings: `Rc<BinaryOrderings>` (reused).
* Persistent `Chain`s, as in `fdr_pocl.rs`, so node size stays small.

### 3. Refinements (`refine.rs`)

**Open condition** `var(t̄)=y` at consumer `c` produces three kinds of children:

1. A new step for each `(schema, assignment)` whose assignment is on `var` with a
   compatible value: the same part, or `none` to `none`. The step's variables are
   fresh, and its terms are unified with `t̄` and `y`.
2. Reuse of any existing step that may precede `c`, with a compatible
   assignment.
3. Init: for each ground init fact of `var` consistent with the bindings, or the
   `none` instances.

Children whose bindings become inconsistent, or whose all-bound static
constraints fail, are discarded. A partially bound static atom must match at
least one tuple in an index of static atoms.

**Threat.**
* *Definition.* Step `w` with assignment `var(ū):=x` threatens link
  `p →var(t̄)=y→ c` when three conditions hold:
  * `w` can be ordered between `p` and `c`;
  * `ū` can co-designate with `t̄`;
  * `x` can differ from `y`.
* *Differ.* `none` vs `Part` always differs. Different parts always differ. The
  same part differs unless all counted args are already co-designated.
* *Refinements:*
  * promote;
  * demote;
  * **disjoint separation**: for position `i`, bind `u_j=t_j` for `j<i` and
    `u_i≠t_i`;
  * **agreement**: when `x` and `y` are the same part, bind the counted args
    equal. The writer then rewrites the protected value, which is not a threat
    in SAS+ semantics.
* *Lazy evaluation.* Threats are detected conservatively when steps or links are
  added and re-checked on selection. A threat that is no longer possible is
  dropped, as `plan.rs:393` does for lifted STRIPS.

**Dead-plan check** (the analogue of `has_unresolvable_threat`): a threat that
is certain has no possible resolution when all three of these hold:
* promote and demote are both inconsistent with the orderings;
* every separation child is inconsistent;
* agreement is impossible.

A plan with such a threat is pruned. This is the pruning that FDR gets and
STRIPS does not.

### 4. Ground view and heuristics (`ground.rs`, `heuristic.rs`)

Lifted mode already grounds for its heuristics (see the memory note
*lifted mode already grounds*). The ground view does the same:

* reachable ground actions come from the existing planning graph's per-schema
  tuples;
* each is instantiated through the compiled schema into ground `LFact` ids;
* a relaxed exploration over those facts gives `add[fact]`.

**Cost of a lifted condition** `var(t̄)=y` under bindings: the minimum of
`add[f]` over the ground facts `f` that match the resolved pattern. The pattern
comes from the bindings and the step's static constraints. A positional index
per `(var, part)` makes the lookup cheap, like `AtomIndex` in
`planning_graph.rs`.

**Reuse**, as in FDR ADD: a condition that an existing step or the initial state
can supply, consistently with the orderings and bindings, costs 0.

**Ranking terms:** `OC`, `ADD`, `ADDR`. TADD and FLOW come in phase 5, over the
ground view, with a lifted step's assignments counted only when bound.

### 5. Search (`search.rs`)

* An adapted copy of the FDR loop: A*, GBFS, PEA, round-robin per-order queues
  with `-f ORDER@H`, node, time and RSS limits.
* Flaw DSL subset: ZLIFO, LIFO, `{n}/{s}/{o}N` buckets, NEW, REUSE, LC_add.
* `{s}` means threats with a separation or agreement option, and `{n}` the rest.

**Completion.** A plan with no flaws is grounded by DFS over the step variables,
using the joint-domain or static checks. The result is then validated as a STRIPS
plan with `validate`, so an unsound planner cannot report a plan as solved.

### 6. CLI

`--lifted-fdr` selects the planner and is mutually exclusive with `--fdr-pocl`
and `-g`. FDR-only flags (`--pea`, `-f ORDER@H`) are accepted with it. A task
the compiler does not support exits with the message *unsupported: <reason>; use
--fdr-pocl*.

## Phases

1. **Task compiler**, with the random-walk oracle. Report which suite domains
   compile.
2. **Plan model, refinements, threats, completion** with the OC heuristic. Small
   gripper, childsnack, blocksworld and logistics tasks solve with validated
   plans. Optimal costs under A* with h=0 match FDR with LM-cut on tiny
   instances.
3. **Ground view plus ADD/ADDR**, PEA, flaw DSL, CLI. Panel screen at 10 s / 1 GiB
   against FDR, ground and lifted.
4. **Propagation**: forced supporters and threats, joint-domain integration,
   dead-threat pruning tuned.
5. **TADD and FLOW over the ground view**, and the per-queue portfolio
   (`port3c` analogue).
6. **PDDL coverage**: negated group atoms (`var ≠ value` conditions), and
   conditional effects (lifted effect conditions plus confrontation).

Each phase ends with tests passing and a short findings note in
`investigation/lifted-fdr/`.

## Testing

* Unit tests per module: variable cover, schema rewrite on gripper, childsnack,
  blocksworld and logistics, and threat and separation cases.
* The random-walk compiler oracle on every compiled suite domain's p01.
* Solve tests: every returned plan is validated, and optimal costs are
  cross-checked against FDR LM-cut A*.
* `cargo test` stays green. Existing planners' outputs do not change: no shared
  code is modified except to make private helpers `pub(crate)`.
