//! Immutable ground task schemas and method templates. IDs index these tables;
//! occurrences in a partial plan have separate IDs, even for identical tasks.

pub type FactId = usize;
pub type TaskId = usize;
pub type MethodId = usize;

#[derive(Clone, Debug)]
pub struct Action {
    pub cost: u64,
    pub preconditions: Vec<FactId>,
    pub add: Vec<FactId>,
    pub delete: Vec<FactId>,
}

#[derive(Clone, Debug)]
pub struct Task {
    pub name: String,
    pub primitive: bool,
}

#[derive(Clone, Debug)]
pub struct Method {
    pub name: String,
    pub task: TaskId,
    /// Occurrences, not a set: repeated task IDs must be preserved.
    pub subtasks: Vec<TaskId>,
    /// Edges between positions in `subtasks`, not task IDs.
    pub orderings: Vec<(usize, usize)>,
}

#[derive(Debug)]
pub struct Problem {
    pub(crate) facts: Vec<String>,
    pub(crate) actions: Vec<Action>,
    pub(crate) tasks: Vec<Task>,
    pub(crate) methods: Vec<Method>,
    pub(crate) initial: Vec<FactId>,
    pub(crate) goal: Vec<FactId>,
    pub(crate) root: TaskId,
    pub(crate) methods_by_task: Vec<Vec<MethodId>>,
}

impl Problem {
    /// PANDA numbers primitive tasks first, in the same order as actions.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        facts: Vec<String>,
        mut actions: Vec<Action>,
        tasks: Vec<Task>,
        mut methods: Vec<Method>,
        mut initial: Vec<FactId>,
        mut goal: Vec<FactId>,
        root: TaskId,
    ) -> Result<Self, String> {
        if root >= tasks.len() || actions.len() > tasks.len() {
            return Err("invalid root task or primitive task count".into());
        }
        let normalize = |ids: &mut Vec<usize>| -> Result<(), String> {
            if ids.iter().any(|&id| id >= facts.len()) {
                return Err("fact ID outside the fact table".into());
            }
            ids.sort_unstable();
            ids.dedup();
            Ok(())
        };
        normalize(&mut initial)?;
        normalize(&mut goal)?;
        for action in &mut actions {
            normalize(&mut action.preconditions)?;
            normalize(&mut action.add)?;
            normalize(&mut action.delete)?;
            // Simultaneous adds win over deletes, as in the flat executor.
            action
                .delete
                .retain(|f| action.add.binary_search(f).is_err());
        }
        for (id, task) in tasks.iter().enumerate() {
            if task.primitive != (id < actions.len()) {
                return Err(
                    "primitive tasks must precede compounds and match the action table".into(),
                );
            }
            if task.name.trim().is_empty() || task.name.contains(['\n', '\r']) {
                return Err("task names must be nonempty single lines".into());
            }
        }
        let mut methods_by_task = vec![Vec::new(); tasks.len()];
        for (id, method) in methods.iter_mut().enumerate() {
            if method.task < actions.len() || method.task >= tasks.len() {
                return Err(format!("method {} has no compound head", method.name));
            }
            if method.name.trim().is_empty() || method.name.contains(['\n', '\r']) {
                return Err("method names must be nonempty single lines".into());
            }
            if method.subtasks.iter().any(|&t| t >= tasks.len()) {
                return Err(format!("method {} references an unknown task", method.name));
            }
            method.orderings.sort_unstable();
            method.orderings.dedup();
            check_orderings(method.subtasks.len(), &method.orderings)
                .map_err(|e| format!("method {}: {e}", method.name))?;
            methods_by_task[method.task].push(id);
        }
        Ok(Self {
            facts,
            actions,
            tasks,
            methods,
            initial,
            goal,
            root,
            methods_by_task,
        })
    }

    pub fn facts(&self) -> &[String] {
        &self.facts
    }
    pub fn actions(&self) -> &[Action] {
        &self.actions
    }
    pub fn tasks(&self) -> &[Task] {
        &self.tasks
    }
    pub fn methods(&self) -> &[Method] {
        &self.methods
    }
    pub fn initial(&self) -> &[FactId] {
        &self.initial
    }
    pub fn goal(&self) -> &[FactId] {
        &self.goal
    }
    pub fn root(&self) -> TaskId {
        self.root
    }
}

fn check_orderings(n: usize, edges: &[(usize, usize)]) -> Result<(), String> {
    let mut outgoing = vec![Vec::new(); n];
    let mut incoming = vec![0usize; n];
    for &(a, b) in edges {
        if a >= n || b >= n || a == b {
            return Err("invalid subtask ordering endpoint".into());
        }
        outgoing[a].push(b);
        incoming[b] += 1;
    }
    let mut ready: Vec<_> = (0..n).filter(|&i| incoming[i] == 0).collect();
    let mut visited = 0;
    while let Some(a) = ready.pop() {
        visited += 1;
        for &b in &outgoing[a] {
            incoming[b] -= 1;
            if incoming[b] == 0 {
                ready.push(b);
            }
        }
    }
    if visited == n {
        Ok(())
    } else {
        Err("cyclic subtask ordering".into())
    }
}
