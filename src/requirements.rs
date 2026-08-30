//! PDDL requirements flags.

use crate::parser::lower::LowerError;

/// The set of enabled PDDL requirements.
#[derive(Debug, Clone, Copy, Default)]
pub struct Requirements {
    pub typing: bool,
    pub negative_preconditions: bool,
    pub disjunctive_preconditions: bool,
    pub equality: bool,
    pub existential_preconditions: bool,
    pub universal_preconditions: bool,
    pub conditional_effects: bool,
    /// The restricted PDDL action-cost fragment (`total-cost` only).
    pub action_costs: bool,
    pub fluents: bool,
    pub durative_actions: bool,
    pub duration_inequalities: bool,
    pub continuous_effects: bool,
    pub timed_initial_literals: bool,
}

impl Requirements {
    pub fn new() -> Self {
        Requirements::default()
    }

    /// Enables the ADL bundle: typing, negative/disjunctive preconditions,
    /// equality, quantified preconditions, and conditional effects.
    pub fn enable_adl(&mut self) {
        self.typing = true;
        self.negative_preconditions = true;
        self.disjunctive_preconditions = true;
        self.equality = true;
        self.existential_preconditions = true;
        self.universal_preconditions = true;
        self.conditional_effects = true;
    }

    /// Enables both existential and universal preconditions.
    pub fn enable_quantified_preconditions(&mut self) {
        self.existential_preconditions = true;
        self.universal_preconditions = true;
    }

    /// Rejects requirements outside the classical subset. Durative/temporal and
    /// general numeric-fluent features are deferred; restricted action costs
    /// have their own flag and remain supported.
    pub fn reject_deferred(&self) -> Result<(), LowerError> {
        let unsupported = [
            (self.fluents, "fluents"),
            (self.durative_actions, "durative-actions"),
            (self.duration_inequalities, "duration-inequalities"),
            (self.continuous_effects, "continuous-effects"),
            (self.timed_initial_literals, "timed-initial-literals"),
        ];
        for (set, name) in unsupported {
            if set {
                return Err(LowerError::UnsupportedRequirement(name.to_string()));
            }
        }
        Ok(())
    }
}
