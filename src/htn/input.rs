//! Reader for the grounded PANDA format (not Fast Downward SAS+).
//! Parsing is positional, ignoring blank lines and whole-line comments.
use super::model::{Action, Method, Problem, Task};

struct Lines<'a> {
    remaining: std::iter::Peekable<std::vec::IntoIter<(usize, &'a str)>>,
    line: usize,
}

impl<'a> Lines<'a> {
    fn next(&mut self, what: &str) -> Result<&'a str, String> {
        let (line, text) = self
            .remaining
            .next()
            .ok_or_else(|| format!("after line {}: missing {what}", self.line))?;
        self.line = line;
        Ok(text)
    }

    fn number(&mut self, what: &str) -> Result<usize, String> {
        let text = self.next(what)?;
        text.parse()
            .map_err(|_| format!("line {}: invalid {what}: {text:?}", self.line))
    }

    fn count(&mut self, what: &str) -> Result<usize, String> {
        let n = self.number(what)?;
        if n > self.remaining.len() {
            return Err(format!(
                "line {}: {what} exceeds remaining input",
                self.line
            ));
        }
        Ok(n)
    }

    fn list(&mut self, what: &str) -> Result<Vec<usize>, String> {
        let text = self.next(what)?;
        let mut tokens: Vec<_> = text.split_whitespace().collect();
        if tokens.pop() != Some("-1") {
            return Err(format!("line {}: {what} must end with -1", self.line));
        }
        tokens
            .into_iter()
            .map(|s| {
                s.parse::<usize>()
                    .map_err(|_| format!("line {}: invalid ID in {what}: {s:?}", self.line))
            })
            .collect()
    }

    fn effects(&mut self, what: &str) -> Result<Vec<usize>, String> {
        let values = self.list(what)?;
        let mut facts = Vec::new();
        let mut tokens = values.into_iter();
        while let Some(conditions) = tokens.next() {
            if conditions != 0 {
                return Err(format!("line {}: native conditional effects are not supported by the HTN kernel; compile them in the frontend", self.line));
            }
            facts.push(
                tokens
                    .next()
                    .ok_or_else(|| format!("line {}: malformed {what}", self.line))?,
            );
        }
        Ok(facts)
    }
}

pub fn read(source: &str) -> Result<Problem, String> {
    let lines: Vec<_> = source
        .lines()
        .enumerate()
        .map(|(i, s)| (i + 1, s.trim()))
        .filter(|(_, s)| !s.is_empty() && !s.starts_with(';'))
        .collect();
    let mut input = Lines {
        remaining: lines.into_iter().peekable(),
        line: 0,
    };
    let mut facts = Vec::new();
    for _ in 0..input.count("fact count")? {
        facts.push(input.next("fact name")?.to_owned());
    }
    // These are inferred invariants, not extra task-network requirements.
    for _ in 0..input.count("mutex range count")? {
        let row = input.next("mutex range")?;
        let mut parts = row.split_whitespace();
        let lo = parts.next().and_then(|s| s.parse::<usize>().ok());
        let hi = parts.next().and_then(|s| s.parse::<usize>().ok());
        if !matches!((lo, hi), (Some(a), Some(b)) if a <= b && b < facts.len())
            || parts.next().is_none()
        {
            return Err(format!("line {}: invalid mutex range", input.line));
        }
    }
    for kind in [
        "strict mutex groups",
        "non-strict mutex groups",
        "invariants",
    ] {
        // Additional inferred metadata is not yet supported by this baseline.
        if input.count(kind)? != 0 {
            return Err(format!(
                "line {}: nonempty {kind} are not supported by the grounded PANDA input adapter",
                input.line
            ));
        }
    }
    let mut actions = Vec::new();
    for _ in 0..input.count("action count")? {
        let cost = input.next("action cost")?.parse::<u64>().map_err(|_| {
            format!(
                "line {}: action cost must be a nonnegative integer",
                input.line
            )
        })?;
        actions.push(Action {
            cost,
            preconditions: input.list("preconditions")?,
            add: input.effects("add effects")?,
            delete: input.effects("delete effects")?,
        });
    }
    let initial = input.list("initial state")?;
    let goal = input.list("goal")?;
    let mut tasks = Vec::new();
    for _ in 0..input.count("task count")? {
        let row = input.next("task")?;
        let (flag, name) = row
            .split_once(char::is_whitespace)
            .ok_or_else(|| format!("line {}: invalid task", input.line))?;
        let primitive = match flag {
            "0" => true,
            "1" => false,
            _ => return Err(format!("line {}: task flag must be 0 or 1", input.line)),
        };
        tasks.push(Task {
            name: name.trim().to_owned(),
            primitive,
        });
    }
    let root = input.number("root task")?;
    let mut methods = Vec::new();
    for _ in 0..input.count("method count")? {
        let name = input.next("method name")?.to_owned();
        let task = input.number("method head")?;
        let subtasks = input.list("subtasks")?;
        let edges = input.list("subtask orderings")?;
        if edges.len() % 2 != 0 {
            return Err(format!(
                "line {}: ordering endpoints must come in pairs",
                input.line
            ));
        }
        let orderings = edges
            .as_chunks::<2>()
            .0
            .iter()
            .map(|p| (p[0], p[1]))
            .collect();
        methods.push(Method {
            name,
            task,
            subtasks,
            orderings,
        });
    }
    if let Some((line, _)) = input.remaining.next() {
        return Err(format!("line {line}: unexpected data after methods"));
    }
    Problem::new(facts, actions, tasks, methods, initial, goal, root)
}
