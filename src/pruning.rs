//! Optional plan-space pruning rules, disabled by default.
//!
//! Select rules with `-p`; their implementations document the applicable
//! representations and correctness constraints.

/// Which pruning rules are enabled. All off by default.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PruneOptions {
    /// Cutset mutex pruning: a partial plan whose pre- or post-cutset contains
    /// a mutex pair has no executable completion. Finite-domain search takes
    /// its mutexes from the translator; the literal representations synthesise
    /// lifted mutex groups instead. See [`crate::cutset`] and
    /// [`crate::lifted_mutex`].
    pub cutset: bool,
    /// Prove lifted cutset mutexes while some terms remain variables. Includes
    /// the ground cutset check; opt-in separately because symbolic checks cost
    /// more and can change the search order.
    pub symbolic: bool,
    /// FDR supporter feasibility checks and bounded propagation of forced
    /// support choices, before allocating queue entries.
    pub supporters: bool,
    /// FDR: compress forced threat resolutions after a threat is selected,
    /// without queueing every intermediate ordering refinement.
    pub threats: bool,
    /// Bounded h² preprocessing for FDR. Includes cutsets and supporter
    /// feasibility filtering; forced propagation still requires `supporters`.
    pub h2: bool,
    /// e-deletion: extend threats from "deletes the protected fact" to "cannot
    /// hold beside it", using the same mutexes as `cutset`. See
    /// [`crate::fdr_pocl`] for the finite-domain reading and
    /// [`crate::plan::effect_e_deletes`] for the literal one.
    pub edelete: bool,
    /// Resolve threats by posting a disjunctive ordering constraint and
    /// propagating, instead of splitting the plan into a promotion child and a
    /// demotion child. See [`crate::fdr_pocl`].
    pub disjunctive: bool,
    /// Operator parameter domains: reject action instances whose arguments lie
    /// outside the constants that can reach that parameter. See
    /// [`crate::param_domains`].
    pub params: bool,
    /// Reachable joint parameter tuples, with propagation through shared
    /// variables and forced bindings. See [`crate::joint_domains`].
    pub joint: bool,
    /// Recursion suspension and its two pruning theorems. See
    /// [`crate::opgraph`].
    pub recursion: bool,
    /// Non-minimality (cutset-dominance) pruning. See [`crate::minimality`].
    pub minimality: bool,
    /// Skip achievers that introduce an interchangeable object other than the
    /// first unused one of its class. See [`crate::symmetry`].
    pub symmetry: bool,
}

impl PruneOptions {
    /// Every rule on.
    pub fn all() -> Self {
        PruneOptions {
            cutset: true,
            symbolic: true,
            supporters: true,
            threats: true,
            h2: true,
            edelete: true,
            disjunctive: true,
            params: true,
            joint: true,
            recursion: true,
            minimality: true,
            symmetry: true,
        }
    }

    /// Whether any rule is enabled — lets callers skip per-node setup entirely.
    pub fn any(self) -> bool {
        self.cutset
            || self.symbolic
            || self.supporters
            || self.threats
            || self.h2
            || self.edelete
            || self.disjunctive
            || self.params
            || self.joint
            || self.recursion
            || self.minimality
            || self.symmetry
    }

    /// Parses a comma-separated rule list: `cutset`, `edelete`, `disjunctive`,
    /// `params`, `recursion`, `minimality`, `all`, or `none`. Names are
    /// case-insensitive and a leading `no-` turns a rule off, so
    /// `all,no-recursion,no-minimality` keeps only the cheap rules.
    pub fn parse(spec: &str) -> Result<Self, String> {
        let mut options = PruneOptions::default();
        for raw in spec.split(',') {
            let token = raw.trim().to_ascii_lowercase();
            if token.is_empty() {
                continue;
            }
            let (name, on) = match token.strip_prefix("no-") {
                Some(rest) => (rest.to_string(), false),
                None => (token, true),
            };
            match name.as_str() {
                "all" => {
                    options = if on {
                        PruneOptions::all()
                    } else {
                        PruneOptions::default()
                    }
                }
                "none" => options = PruneOptions::default(),
                "cutset" => options.cutset = on,
                "symbolic" => options.symbolic = on,
                "supporters" => options.supporters = on,
                "threats" => options.threats = on,
                "h2" => options.h2 = on,
                "edelete" | "e-deletion" | "edeletion" => options.edelete = on,
                "disjunctive" | "disjunctions" => options.disjunctive = on,
                "params" | "parameters" | "param-domains" => options.params = on,
                "joint" | "joint-domains" => options.joint = on,
                "recursion" | "recursive" => options.recursion = on,
                "minimality" | "minimal" => options.minimality = on,
                "symmetry" | "symmetries" | "objects" => options.symmetry = on,
                other => {
                    return Err(format!(
                        "unknown pruning rule `{other}` (expected cutset, edelete, \
                         symbolic, supporters, threats, h2, disjunctive, params, joint, recursion, minimality, symmetry, all or none)"
                    ))
                }
            }
        }
        Ok(options)
    }

    /// Enabled rules that cannot fire on the finite-domain representation.
    /// A SAS⁺ task is already ground and reachability-filtered by the
    /// translator, so schema parameter domains have nothing to say about it.
    pub fn lifted_only(self) -> Vec<&'static str> {
        let mut names = Vec::new();
        if self.params {
            names.push("params");
        }
        if self.joint {
            names.push("joint");
        }
        if self.symbolic {
            names.push("symbolic");
        }
        names
    }

    /// Rules that need ground steps: they cannot fire on the lifted
    /// representation, where a step's arguments are still variables.
    pub fn ground_only(self) -> Vec<&'static str> {
        let mut names = Vec::new();
        if self.symmetry {
            names.push("symmetry");
        }
        names
    }

    /// Rules implemented only for the finite-domain representation.
    pub fn finite_domain_only(self) -> Vec<&'static str> {
        let mut names = Vec::new();
        if self.disjunctive {
            names.push("disjunctive");
        }
        if self.supporters {
            names.push("supporters");
        }
        if self.threats {
            names.push("threats");
        }
        if self.h2 {
            names.push("h2");
        }
        names
    }

    /// The enabled rules, in declaration order, for `-v` reporting.
    pub fn names(self) -> Vec<&'static str> {
        let mut names = Vec::new();
        if self.cutset {
            names.push("cutset");
        }
        if self.symbolic {
            names.push("symbolic");
        }
        if self.supporters {
            names.push("supporters");
        }
        if self.threats {
            names.push("threats");
        }
        if self.h2 {
            names.push("h2");
        }
        if self.edelete {
            names.push("edelete");
        }
        if self.disjunctive {
            names.push("disjunctive");
        }
        if self.params {
            names.push("params");
        }
        if self.joint {
            names.push("joint");
        }
        if self.recursion {
            names.push("recursion");
        }
        if self.minimality {
            names.push("minimality");
        }
        if self.symmetry {
            names.push("symmetry");
        }
        names
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defaults_to_nothing_enabled() {
        let options = PruneOptions::default();
        assert!(!options.any());
        assert!(options.names().is_empty());
    }

    #[test]
    fn parses_a_rule_list() {
        let options = PruneOptions::parse("cutset,recursion").unwrap();
        assert!(options.cutset && options.recursion);
        assert!(!options.params && !options.minimality);
    }

    #[test]
    fn all_then_subtract() {
        let options = PruneOptions::parse("all,no-minimality").unwrap();
        assert_eq!(
            options.names(),
            vec![
                "cutset",
                "symbolic",
                "supporters",
                "threats",
                "h2",
                "edelete",
                "disjunctive",
                "params",
                "joint",
                "recursion",
                "symmetry"
            ]
        );
    }

    #[test]
    fn rejects_an_unknown_rule() {
        let err = PruneOptions::parse("cutset,wibble").unwrap_err();
        assert!(err.contains("wibble"), "{err}");
    }

    #[test]
    fn ignores_whitespace_and_case() {
        assert_eq!(
            PruneOptions::parse(" Cutset , PARAMS ").unwrap(),
            PruneOptions {
                cutset: true,
                params: true,
                ..PruneOptions::default()
            }
        );
    }
}
