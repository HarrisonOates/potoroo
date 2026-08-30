//! Parsed finite-domain (SAS+) planning tasks.
//!
//! Unlike [`crate::sas`], which deliberately emits one binary SAS+ variable per
//! ground proposition for heuristic evaluation, this module retains the
//! translator's invariant groups. A [`Fact`] is therefore an equality
//! `variable = value`, and an [`Effect`] is an assignment to one variable.

use std::collections::{BTreeMap, HashMap, HashSet};

use thiserror::Error;

/// A finite-domain fact `variable = value`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Fact {
    pub variable: usize,
    pub value: usize,
}

impl Fact {
    pub fn new(variable: usize, value: usize) -> Self {
        Fact { variable, value }
    }
}

/// One SAS+ state variable and its printable values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variable {
    pub name: String,
    pub values: Vec<String>,
}

/// A conditional finite-domain assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Effect {
    /// Conditions local to this effect. Operator applicability conditions are
    /// stored separately in [`Operator::prevail`] and `pre`.
    pub conditions: Vec<Fact>,
    pub variable: usize,
    /// Required old value of the affected variable, when present. In the SAS+
    /// format this is an operator applicability condition even for a
    /// conditional effect.
    pub pre: Option<usize>,
    pub post: usize,
}

impl Effect {
    pub fn assignment(&self) -> Fact {
        Fact::new(self.variable, self.post)
    }
}

/// A ground SAS+ operator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operator {
    pub name: String,
    pub prevail: Vec<Fact>,
    pub effects: Vec<Effect>,
    pub cost: usize,
}

/// One grounded SAS+ axiom rule. Derived variables are reset to their default
/// (last) value before the rule closure is evaluated in each state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Axiom {
    pub conditions: Vec<Fact>,
    pub variable: usize,
    pub pre: usize,
    pub post: usize,
}

impl Operator {
    /// Returns the complete applicability condition: prevail facts plus the
    /// pre-values embedded in effects, with at most one value per variable.
    pub fn preconditions(&self) -> Vec<Fact> {
        let mut by_variable = BTreeMap::new();
        for &fact in &self.prevail {
            by_variable.insert(fact.variable, fact.value);
        }
        for effect in &self.effects {
            if let Some(value) = effect.pre {
                by_variable.insert(effect.variable, value);
            }
        }
        by_variable
            .into_iter()
            .map(|(variable, value)| Fact::new(variable, value))
            .collect()
    }
}

/// A fully grounded finite-domain planning task.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Task {
    pub variables: Vec<Variable>,
    /// One value per variable.
    pub initial: Vec<usize>,
    pub goals: Vec<Fact>,
    pub operators: Vec<Operator>,
    pub axioms: Vec<Axiom>,
}

impl Task {
    /// Parses Fast Downward's SAS+ format version 3.
    ///
    pub fn parse(input: &str) -> Result<Self, ParseError> {
        let mut lines = Lines::new(input);
        lines.marker("begin_version")?;
        let version = lines.usize("SAS+ version")?;
        if version != 3 {
            return Err(lines.error(format!("unsupported SAS+ version {version}; expected 3")));
        }
        lines.marker("end_version")?;
        lines.marker("begin_metric")?;
        let _metric = lines.usize("metric flag")?;
        lines.marker("end_metric")?;

        let num_variables = lines.usize("variable count")?;
        let mut variables = Vec::with_capacity(num_variables);
        for _ in 0..num_variables {
            lines.marker("begin_variable")?;
            let name = lines.next("variable name")?.to_string();
            let axiom_layer = lines.isize("axiom layer")?;
            if axiom_layer < -1 {
                return Err(lines.error(format!(
                    "variable `{name}` has invalid axiom layer {axiom_layer}"
                )));
            }
            let domain_size = lines.usize("variable domain size")?;
            if domain_size == 0 {
                return Err(lines.error(format!("variable `{name}` has an empty domain")));
            }
            let mut values = Vec::with_capacity(domain_size);
            for _ in 0..domain_size {
                values.push(lines.next("variable value")?.to_string());
            }
            lines.marker("end_variable")?;
            variables.push(Variable { name, values });
        }

        // Mutex groups are useful diagnostics, but variable=value already carries
        // the invariants needed by this representation. Parse and validate them,
        // then discard them.
        let num_mutex_groups = lines.usize("mutex group count")?;
        for _ in 0..num_mutex_groups {
            lines.marker("begin_mutex_group")?;
            let size = lines.usize("mutex group size")?;
            for _ in 0..size {
                let fact = lines.fact("mutex fact")?;
                validate_fact(&variables, fact, &lines)?;
            }
            lines.marker("end_mutex_group")?;
        }

        lines.marker("begin_state")?;
        let mut initial = Vec::with_capacity(num_variables);
        for variable in 0..num_variables {
            let value = lines.usize("initial value")?;
            validate_fact(&variables, Fact::new(variable, value), &lines)?;
            initial.push(value);
        }
        lines.marker("end_state")?;

        lines.marker("begin_goal")?;
        let num_goals = lines.usize("goal count")?;
        let mut goals = Vec::with_capacity(num_goals);
        for _ in 0..num_goals {
            let fact = lines.fact("goal fact")?;
            validate_fact(&variables, fact, &lines)?;
            goals.push(fact);
        }
        lines.marker("end_goal")?;

        let num_operators = lines.usize("operator count")?;
        let mut operators = Vec::with_capacity(num_operators);
        for _ in 0..num_operators {
            lines.marker("begin_operator")?;
            let name = lines.next("operator name")?.to_string();
            let num_prevail = lines.usize("prevail count")?;
            let mut prevail = Vec::with_capacity(num_prevail);
            for _ in 0..num_prevail {
                let fact = lines.fact("prevail fact")?;
                validate_fact(&variables, fact, &lines)?;
                prevail.push(fact);
            }

            let num_effects = lines.usize("effect count")?;
            let mut effects = Vec::with_capacity(num_effects);
            for _ in 0..num_effects {
                let line = lines.next("effect")?;
                effects.push(parse_effect(line, &variables, lines.line_number())?);
            }
            let cost = lines.usize("operator cost")?;
            lines.marker("end_operator")?;
            operators.push(Operator {
                name,
                prevail,
                effects,
                cost,
            });
        }

        let num_axioms = lines.usize("axiom count")?;
        let mut axioms = Vec::with_capacity(num_axioms);
        for _ in 0..num_axioms {
            lines.marker("begin_rule")?;
            let num_conditions = lines.usize("axiom condition count")?;
            let mut conditions = Vec::with_capacity(num_conditions);
            for _ in 0..num_conditions {
                let fact = lines.fact("axiom condition")?;
                validate_fact(&variables, fact, &lines)?;
                conditions.push(fact);
            }
            let effect_line = lines.next("axiom effect")?;
            let fields = effect_line.split_whitespace().collect::<Vec<_>>();
            if fields.len() != 3 {
                return Err(lines.error(format!(
                    "axiom effect has {} field(s), expected 3",
                    fields.len()
                )));
            }
            let parse_field = |field: &str, what: &str| {
                field.parse::<usize>().map_err(|_| ParseError {
                    line: lines.line_number(),
                    message: format!("invalid {what} `{field}`"),
                })
            };
            let variable = parse_field(fields[0], "axiom variable")?;
            let pre = parse_field(fields[1], "axiom old value")?;
            let post = parse_field(fields[2], "axiom new value")?;
            validate_fact(&variables, Fact::new(variable, pre), &lines)?;
            validate_fact(&variables, Fact::new(variable, post), &lines)?;
            lines.marker("end_rule")?;
            axioms.push(Axiom {
                conditions,
                variable,
                pre,
                post,
            });
        }
        if let Some(extra) = lines.remaining_nonempty() {
            return Err(lines.error(format!("unexpected trailing input `{extra}`")));
        }

        Ok(Task {
            variables,
            initial,
            goals,
            operators,
            axioms,
        })
    }

    pub fn fact_name(&self, fact: Fact) -> &str {
        &self.variables[fact.variable].values[fact.value]
    }

    pub fn multi_valued_variables(&self) -> usize {
        self.variables.iter().filter(|v| v.values.len() > 2).count()
    }

    pub fn num_facts(&self) -> usize {
        self.variables.iter().map(|v| v.values.len()).sum()
    }

    pub fn is_derived_variable(&self, variable: usize) -> bool {
        self.axioms.iter().any(|axiom| axiom.variable == variable)
    }

    pub fn default_value(&self, variable: usize) -> usize {
        self.variables[variable].values.len() - 1
    }

    /// Resets derived variables and computes the grounded axiom closure.
    pub fn close_axioms(&self, state: &mut [usize]) {
        for (variable, value) in state.iter_mut().enumerate().take(self.variables.len()) {
            if self.is_derived_variable(variable) {
                *value = self.default_value(variable);
            }
        }
        loop {
            let mut changed = false;
            for axiom in &self.axioms {
                if state[axiom.variable] == axiom.pre
                    && axiom
                        .conditions
                        .iter()
                        .all(|fact| state[fact.variable] == fact.value)
                    && state[axiom.variable] != axiom.post
                {
                    state[axiom.variable] = axiom.post;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// Returns a DNF of conjunctions over non-derived facts that establish a
    /// derived equality. `None` means `fact` is not derived. Default values are
    /// supported by making every rule for a non-default value false.
    pub fn derived_supports(&self, fact: Fact) -> Option<Vec<Vec<Fact>>> {
        if !self.is_derived_variable(fact.variable) {
            return None;
        }
        let mut memo = HashMap::new();
        let mut active = HashSet::new();
        Some(self.support_fact(fact, &mut memo, &mut active))
    }

    fn support_fact(
        &self,
        fact: Fact,
        memo: &mut HashMap<Fact, Vec<Vec<Fact>>>,
        active: &mut HashSet<Fact>,
    ) -> Vec<Vec<Fact>> {
        if let Some(cached) = memo.get(&fact) {
            return cached.clone();
        }
        if !self.is_derived_variable(fact.variable) {
            return vec![vec![fact]];
        }
        if !active.insert(fact) {
            return Vec::new();
        }

        let default = self.default_value(fact.variable);
        let mut result = if fact.value == default {
            let mut supports = vec![Vec::new()];
            for axiom in self
                .axioms
                .iter()
                .filter(|axiom| axiom.variable == fact.variable && axiom.post != default)
            {
                let mut rule_false = Vec::new();
                for condition in &axiom.conditions {
                    for value in 0..self.variables[condition.variable].values.len() {
                        if value == condition.value {
                            continue;
                        }
                        rule_false.extend(self.support_fact(
                            Fact::new(condition.variable, value),
                            memo,
                            active,
                        ));
                    }
                }
                supports = and_dnf(supports, rule_false);
            }
            supports
        } else {
            let mut supports = Vec::new();
            for axiom in self
                .axioms
                .iter()
                .filter(|axiom| axiom.variable == fact.variable && axiom.post == fact.value)
            {
                let mut body = vec![Vec::new()];
                for condition in &axiom.conditions {
                    body = and_dnf(body, self.support_fact(*condition, memo, active));
                }
                supports.extend(body);
            }
            deduplicate_dnf(supports)
        };
        result = deduplicate_dnf(result);
        active.remove(&fact);
        memo.insert(fact, result.clone());
        result
    }
}

fn and_dnf(left: Vec<Vec<Fact>>, right: Vec<Vec<Fact>>) -> Vec<Vec<Fact>> {
    let mut result = Vec::new();
    for lhs in &left {
        for rhs in &right {
            let mut values = BTreeMap::new();
            let mut consistent = true;
            for fact in lhs.iter().chain(rhs) {
                if values
                    .insert(fact.variable, fact.value)
                    .is_some_and(|old| old != fact.value)
                {
                    consistent = false;
                    break;
                }
            }
            if consistent {
                result.push(
                    values
                        .into_iter()
                        .map(|(variable, value)| Fact::new(variable, value))
                        .collect(),
                );
            }
        }
    }
    deduplicate_dnf(result)
}

fn deduplicate_dnf(mut clauses: Vec<Vec<Fact>>) -> Vec<Vec<Fact>> {
    for clause in &mut clauses {
        clause.sort_unstable_by_key(|fact| (fact.variable, fact.value));
        clause.dedup();
    }
    clauses.sort();
    clauses.dedup();
    clauses
}

fn parse_effect(
    line: &str,
    variables: &[Variable],
    line_number: usize,
) -> Result<Effect, ParseError> {
    let fields: Vec<&str> = line.split_whitespace().collect();
    let parse = |field: &str, what: &str| -> Result<isize, ParseError> {
        field.parse::<isize>().map_err(|_| ParseError {
            line: line_number,
            message: format!("invalid {what} `{field}`"),
        })
    };
    let Some(first) = fields.first() else {
        return Err(ParseError {
            line: line_number,
            message: "empty effect line".to_string(),
        });
    };
    let num_conditions = parse(first, "effect-condition count")?;
    if num_conditions < 0 {
        return Err(ParseError {
            line: line_number,
            message: "negative effect-condition count".to_string(),
        });
    }
    let num_conditions = num_conditions as usize;
    let expected = 1 + 2 * num_conditions + 3;
    if fields.len() != expected {
        return Err(ParseError {
            line: line_number,
            message: format!(
                "effect has {} field(s), expected {expected} for {num_conditions} condition(s)",
                fields.len()
            ),
        });
    }

    let mut conditions = Vec::with_capacity(num_conditions);
    let mut offset = 1;
    for _ in 0..num_conditions {
        let variable = parse(fields[offset], "effect-condition variable")?;
        let value = parse(fields[offset + 1], "effect-condition value")?;
        if variable < 0 || value < 0 {
            return Err(ParseError {
                line: line_number,
                message: "negative variable/value in effect condition".to_string(),
            });
        }
        let fact = Fact::new(variable as usize, value as usize);
        validate_fact_at(variables, fact, line_number)?;
        conditions.push(fact);
        offset += 2;
    }

    let variable = parse(fields[offset], "effect variable")?;
    let pre = parse(fields[offset + 1], "effect pre-value")?;
    let post = parse(fields[offset + 2], "effect post-value")?;
    if variable < 0 || pre < -1 || post < 0 {
        return Err(ParseError {
            line: line_number,
            message: "invalid negative value in effect transition".to_string(),
        });
    }
    let variable = variable as usize;
    let post = post as usize;
    validate_fact_at(variables, Fact::new(variable, post), line_number)?;
    let pre = if pre == -1 {
        None
    } else {
        let pre = pre as usize;
        validate_fact_at(variables, Fact::new(variable, pre), line_number)?;
        Some(pre)
    };

    Ok(Effect {
        conditions,
        variable,
        pre,
        post,
    })
}

fn validate_fact(variables: &[Variable], fact: Fact, lines: &Lines<'_>) -> Result<(), ParseError> {
    validate_fact_at(variables, fact, lines.line_number())
}

fn validate_fact_at(variables: &[Variable], fact: Fact, line: usize) -> Result<(), ParseError> {
    let Some(variable) = variables.get(fact.variable) else {
        return Err(ParseError {
            line,
            message: format!("variable {} is out of range", fact.variable),
        });
    };
    if fact.value >= variable.values.len() {
        return Err(ParseError {
            line,
            message: format!(
                "value {} is out of range for variable {} (domain size {})",
                fact.value,
                fact.variable,
                variable.values.len()
            ),
        });
    }
    Ok(())
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error("SAS+ parse error at line {line}: {message}")]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

struct Lines<'a> {
    lines: Vec<&'a str>,
    position: usize,
}

impl<'a> Lines<'a> {
    fn new(input: &'a str) -> Self {
        Lines {
            lines: input.lines().collect(),
            position: 0,
        }
    }

    fn line_number(&self) -> usize {
        self.position.max(1)
    }

    fn next(&mut self, what: &str) -> Result<&'a str, ParseError> {
        let Some(line) = self.lines.get(self.position) else {
            return Err(self.error(format!("expected {what}, found end of input")));
        };
        self.position += 1;
        Ok(line.trim())
    }

    fn marker(&mut self, expected: &str) -> Result<(), ParseError> {
        let actual = self.next(expected)?;
        if actual == expected {
            Ok(())
        } else {
            Err(self.error(format!("expected `{expected}`, found `{actual}`")))
        }
    }

    fn usize(&mut self, what: &str) -> Result<usize, ParseError> {
        let value = self.next(what)?;
        value
            .parse()
            .map_err(|_| self.error(format!("invalid {what} `{value}`")))
    }

    fn isize(&mut self, what: &str) -> Result<isize, ParseError> {
        let value = self.next(what)?;
        value
            .parse()
            .map_err(|_| self.error(format!("invalid {what} `{value}`")))
    }

    fn fact(&mut self, what: &str) -> Result<Fact, ParseError> {
        let line = self.next(what)?;
        let fields: Vec<&str> = line.split_whitespace().collect();
        if fields.len() != 2 {
            return Err(self.error(format!("invalid {what} `{line}`")));
        }
        let variable = fields[0]
            .parse()
            .map_err(|_| self.error(format!("invalid variable in {what} `{line}`")))?;
        let value = fields[1]
            .parse()
            .map_err(|_| self.error(format!("invalid value in {what} `{line}`")))?;
        Ok(Fact::new(variable, value))
    }

    fn remaining_nonempty(&self) -> Option<&'a str> {
        self.lines[self.position..]
            .iter()
            .map(|line| line.trim())
            .find(|line| !line.is_empty())
    }

    fn error(&self, message: String) -> ParseError {
        ParseError {
            line: self.line_number(),
            message,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const THREE_LOCATION_TASK: &str = "begin_version
3
end_version
begin_metric
0
end_metric
1
begin_variable
location
-1
3
Atom at(truck,paris)
Atom at(truck,lyon)
Atom at(truck,nice)
end_variable
0
begin_state
0
end_state
begin_goal
1
0 1
end_goal
1
begin_operator
drive truck paris lyon
0
1
0 0 0 1
1
end_operator
0
";

    #[test]
    fn parses_multi_valued_sas_task() {
        let task = Task::parse(THREE_LOCATION_TASK).unwrap();
        assert_eq!(task.variables.len(), 1);
        assert_eq!(task.variables[0].values.len(), 3);
        assert_eq!(task.multi_valued_variables(), 1);
        assert_eq!(task.initial, vec![0]);
        assert_eq!(task.goals, vec![Fact::new(0, 1)]);
        assert_eq!(task.operators[0].preconditions(), vec![Fact::new(0, 0)]);
        assert_eq!(task.operators[0].effects[0].assignment(), Fact::new(0, 1));
    }

    #[test]
    fn accepts_an_unused_axiom_layer() {
        let sas = THREE_LOCATION_TASK.replacen("location\n-1", "location\n0", 1);
        assert!(Task::parse(&sas).is_ok());
    }

    #[test]
    fn parses_and_expands_binary_axiom_supports() {
        let sas = "begin_version
3
end_version
begin_metric
0
end_metric
2
begin_variable
p
-1
2
p-true
p-false
end_variable
begin_variable
d
0
2
d-true
d-false
end_variable
0
begin_state
1
1
end_state
begin_goal
1
1 0
end_goal
0
1
begin_rule
1
0 0
1 1 0
end_rule
";
        let task = Task::parse(sas).unwrap();
        assert_eq!(task.axioms.len(), 1);
        assert_eq!(
            task.derived_supports(Fact::new(1, 0)).unwrap(),
            vec![vec![Fact::new(0, 0)]]
        );
        assert_eq!(
            task.derived_supports(Fact::new(1, 1)).unwrap(),
            vec![vec![Fact::new(0, 1)]]
        );
        let mut state = vec![0, 1];
        task.close_axioms(&mut state);
        assert_eq!(state, vec![0, 0]);
    }
}
