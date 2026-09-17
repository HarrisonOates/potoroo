//! Optional plan-space pruning rules, disabled by default.
//!
//! Select rules with `-p`; their implementations document the applicable
//! representations and correctness constraints.

/// Which pruning rules are enabled. All off by default.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PruneOptions {
    /// Cutset mutex pruning: a partial plan whose pre- or post-cutset contains
    /// a mutex pair has no executable completion. See [`crate::cutset`].
    pub cutset: bool,
    /// Operator parameter domains: reject action instances whose arguments lie
    /// outside the constants that can reach that parameter. See
    /// [`crate::param_domains`].
    pub params: bool,
    /// Recursion suspension and its two pruning theorems. See
    /// [`crate::opgraph`].
    pub recursion: bool,
    /// Non-minimality (cutset-dominance) pruning. See [`crate::minimality`].
    pub minimality: bool,
}

impl PruneOptions {
    /// Every rule on.
    pub fn all() -> Self {
        PruneOptions {
            cutset: true,
            params: true,
            recursion: true,
            minimality: true,
        }
    }

    /// Whether any rule is enabled — lets callers skip per-node setup entirely.
    pub fn any(self) -> bool {
        self.cutset || self.params || self.recursion || self.minimality
    }

    /// Parses a comma-separated rule list: `cutset`, `params`, `recursion`,
    /// `minimality`, `all`, or `none`. Names are case-insensitive and a leading
    /// `no-` turns a rule off, so `all,no-minimality` is the three cheap rules.
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
                "params" | "parameters" | "param-domains" => options.params = on,
                "recursion" | "recursive" => options.recursion = on,
                "minimality" | "minimal" => options.minimality = on,
                other => {
                    return Err(format!(
                        "unknown pruning rule `{other}` \
                         (expected cutset, params, recursion, minimality, all or none)"
                    ))
                }
            }
        }
        Ok(options)
    }

    /// The enabled rules, in declaration order, for `-v` reporting.
    pub fn names(self) -> Vec<&'static str> {
        let mut names = Vec::new();
        if self.cutset {
            names.push("cutset");
        }
        if self.params {
            names.push("params");
        }
        if self.recursion {
            names.push("recursion");
        }
        if self.minimality {
            names.push("minimality");
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
        assert_eq!(options.names(), vec!["cutset", "params", "recursion"]);
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
