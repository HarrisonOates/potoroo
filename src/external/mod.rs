//! Shelling out to an external classical planner (Fast Downward) to evaluate a
//! state-based heuristic on the initial state of a compiled classical problem.
//!
//! This is the "external solver" plumbing (Phase 0c). It is consumed by the
//! causal-link compilation heuristic (Phase 1): a partial POCL plan is compiled
//! to a classical STRIPS problem (`crate::compile`), and that problem's initial
//! heuristic value — computed by Fast Downward — is the partial plan's rank.
//!
//! Design notes:
//! - We *shell out* (write PDDL, spawn `fast-downward.py`, parse stdout). There
//!   is therefore no compile-time dependency on any planner, so this module is
//!   always compiled (`std` + `thiserror` only). The roadmap's optional `external`
//!   Cargo feature is deferred to phases that link a real library (OR-tools /
//!   tch/ONNX); shelling out does not need it.
//! - The Fast Downward executable is found via the `POTOROO_FD` environment
//!   variable, falling back to `fast-downward.py` on `PATH`.
//! - `run_fd_heuristic` is *memoized* by a hash of (domain, problem, heuristic).
//!   The paper notes that the per-node external-call overhead dominated the
//!   Bercher–Geier–Biundo (2013) compilation approach, so caching identical
//!   compiled problems is essential.
//! - The output parser (`parse_initial_h`) is a pure function, unit-tested
//!   against captured Fast Downward output so it is verifiable without FD
//!   installed.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use thiserror::Error;

/// A state-based heuristic Fast Downward can evaluate. The variant maps to the
/// FD evaluator syntax (`evaluator`) and to the name FD prints in its
/// "Initial heuristic value for <name>:" line (`fd_name`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FdHeuristic {
    /// FF heuristic (`ff()`).
    Ff,
    /// Landmark-cut (`lmcut()`).
    LmCut,
    /// h^max (`hmax()`).
    HMax,
    /// Additive heuristic (`add()`).
    HAdd,
    /// Goal-count / blind sanity heuristic (`blind()`).
    Blind,
}

impl FdHeuristic {
    /// The Fast Downward evaluator expression (e.g. `ff()`).
    pub fn evaluator(self) -> &'static str {
        match self {
            FdHeuristic::Ff => "ff()",
            FdHeuristic::LmCut => "lmcut()",
            FdHeuristic::HMax => "hmax()",
            FdHeuristic::HAdd => "add()",
            FdHeuristic::Blind => "blind()",
        }
    }

    /// The name Fast Downward prints in "Initial heuristic value for <name>:".
    pub fn fd_name(self) -> &'static str {
        match self {
            FdHeuristic::Ff => "ff",
            FdHeuristic::LmCut => "lmcut",
            FdHeuristic::HMax => "hmax",
            FdHeuristic::HAdd => "add",
            FdHeuristic::Blind => "blind",
        }
    }

    /// A short discriminant for cache keying.
    fn tag(self) -> u8 {
        match self {
            FdHeuristic::Ff => 0,
            FdHeuristic::LmCut => 1,
            FdHeuristic::HMax => 2,
            FdHeuristic::HAdd => 3,
            FdHeuristic::Blind => 4,
        }
    }
}

/// Errors from invoking Fast Downward.
#[derive(Debug, Error)]
pub enum FdError {
    /// The Fast Downward executable could not be spawned (not installed / not on
    /// `PATH` / bad `POTOROO_FD`).
    #[error("could not run Fast Downward ({path}): {source}; set POTOROO_FD to its path")]
    Spawn {
        path: String,
        #[source]
        source: std::io::Error,
    },
    /// A temp-file I/O error while preparing the PDDL inputs.
    #[error("I/O error preparing Fast Downward inputs: {0}")]
    Io(#[from] std::io::Error),
    /// Fast Downward ran but we could not find the initial heuristic value in its
    /// output. The captured output is included for diagnosis.
    #[error("could not parse initial heuristic value from Fast Downward output")]
    ParseFailure { output: String },
}

/// The result of evaluating the heuristic on the compiled problem's initial
/// state. `Finite(h)` is a reachable estimate; `Infinite` means Fast Downward
/// proved the (delete-relaxed) goal unreachable from the initial state — i.e.
/// the partial plan is a dead end under this heuristic.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum HResult {
    Finite(f32),
    Infinite,
}

/// Global memoization cache, keyed by a hash of (domain, problem, heuristic).
/// Only successful results are cached (errors are transient — e.g. FD missing).
fn cache() -> &'static Mutex<HashMap<u64, HResult>> {
    static CACHE: OnceLock<Mutex<HashMap<u64, HResult>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

fn cache_key(domain_pddl: &str, problem_pddl: &str, heur: FdHeuristic) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = crate::fasthash::FxHasher::default();
    domain_pddl.hash(&mut h);
    0xFFu8.hash(&mut h); // separator
    problem_pddl.hash(&mut h);
    heur.tag().hash(&mut h);
    h.finish()
}

/// The configured Fast Downward driver. Resolution order:
/// 1. `POTOROO_FD` environment variable (an explicit path to `fast-downward.py`).
/// 2. `fast-downward.py` on `PATH`.
///
/// The same argument syntax drives the source build, a GitHub-release build, and
/// the apptainer `.sif` image, so callers need not care which is configured.
pub fn fd_path() -> String {
    if let Ok(p) = std::env::var("POTOROO_FD") {
        return p;
    }
    "fast-downward.py".to_string()
}

/// Whether a Fast Downward executable appears to be invocable. Used by tests and
/// callers to degrade gracefully when FD is not installed.
pub fn fd_available() -> bool {
    std::process::Command::new(fd_path())
        .arg("--help")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Computes the initial-state value of `heur` on the classical problem given by
/// `domain_pddl` + `problem_pddl`, by running Fast Downward. Memoized.
pub fn run_fd_heuristic(
    domain_pddl: &str,
    problem_pddl: &str,
    heur: FdHeuristic,
) -> Result<HResult, FdError> {
    let key = cache_key(domain_pddl, problem_pddl, heur);
    if let Some(v) = cache().lock().unwrap().get(&key).copied() {
        return Ok(v);
    }

    let output = invoke_fd(domain_pddl, problem_pddl, heur)?;
    let result = parse_initial_h(&output, heur).ok_or_else(|| FdError::ParseFailure {
        output: truncate(&output, 4000),
    })?;

    cache().lock().unwrap().insert(key, result);
    Ok(result)
}

/// The frozen `downward` C++ search binary (built from the submodule). Resolution
/// order: `VHPOP_DOWNWARD` env → the submodule build → `downward` on `PATH`.
pub fn downward_path() -> String {
    if let Ok(p) = std::env::var("POTOROO_DOWNWARD") {
        return p;
    }
    "downward".to_string()
}

/// Whether the `downward` binary appears invocable.
pub fn downward_available() -> bool {
    std::path::Path::new(&downward_path()).exists()
        || std::process::Command::new(downward_path())
            .arg("--help")
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
}

/// A persistent `downward --h-server` process: constructs a heuristic and
/// evaluates `h(init)` on each task in-process, so there is no per-task process
/// spawn or search setup. One process is kept alive per heuristic backend.
struct HServer {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: std::io::BufReader<std::process::ChildStdout>,
}

fn h_servers() -> &'static Mutex<HashMap<u8, HServer>> {
    static S: OnceLock<Mutex<HashMap<u8, HServer>>> = OnceLock::new();
    S.get_or_init(|| Mutex::new(HashMap::new()))
}

fn spawn_h_server(heur: FdHeuristic) -> Result<HServer, FdError> {
    let path = downward_path();
    let mut child = std::process::Command::new(&path)
        .arg("--h-server")
        .arg(heur.fd_name())
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .map_err(|source| FdError::Spawn { path, source })?;
    let stdin = child.stdin.take().expect("piped stdin");
    let stdout = std::io::BufReader::new(child.stdout.take().expect("piped stdout"));
    Ok(HServer { child, stdin, stdout })
}

/// One request/response against a (possibly freshly spawned) server process.
fn h_server_request(server: &mut HServer, sas: &str) -> std::io::Result<HResult> {
    use std::io::{BufRead, Write};
    write!(server.stdin, "{}\n", sas.len())?;
    server.stdin.write_all(sas.as_bytes())?;
    server.stdin.flush()?;
    let mut line = String::new();
    loop {
        line.clear();
        if server.stdout.read_line(&mut line)? == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::UnexpectedEof,
                "h-server closed",
            ));
        }
        if let Some(rest) = line.trim().strip_prefix("HRESULT ") {
            return Ok(if rest.eq_ignore_ascii_case("inf") {
                HResult::Infinite
            } else {
                HResult::Finite(rest.trim().parse::<f32>().unwrap_or(f32::INFINITY))
            });
        }
        // Otherwise an incidental FD log line: skip it.
    }
}

/// Evaluates `heur` on a SAS⁺ task's initial state via the persistent
/// `downward --h-server` process (no per-task spawn, no search). Memoized. On a
/// dead server, respawns once. Falls back to `run_downward_sas` is the caller's
/// responsibility if the server cannot be started.
pub fn run_h_server_eval(sas: &str, heur: FdHeuristic) -> Result<HResult, FdError> {
    let key = {
        use std::hash::{Hash, Hasher};
        let mut h = crate::fasthash::FxHasher::default();
        sas.hash(&mut h);
        heur.tag().hash(&mut h);
        h.finish()
    };
    if let Some(v) = cache().lock().unwrap().get(&key).copied() {
        return Ok(v);
    }

    let mut map = h_servers().lock().unwrap();
    // Up to two attempts: the first may hit a stale/dead server.
    for attempt in 0..2 {
        if !map.contains_key(&heur.tag()) {
            let s = spawn_h_server(heur)?;
            map.insert(heur.tag(), s);
        }
        let server = map.get_mut(&heur.tag()).unwrap();
        match h_server_request(server, sas) {
            Ok(v) => {
                cache().lock().unwrap().insert(key, v);
                return Ok(v);
            }
            Err(_) if attempt == 0 => {
                // Drop the dead process and retry with a fresh one.
                if let Some(mut dead) = map.remove(&heur.tag()) {
                    let _ = dead.child.kill();
                    let _ = dead.child.wait();
                }
            }
            Err(source) => {
                return Err(FdError::Spawn {
                    path: downward_path(),
                    source,
                })
            }
        }
    }
    unreachable!("h-server retry loop returns on both attempts")
}

/// Evaluates `heur` on the initial state of an FDR/SAS+ task given as text, by
/// invoking only the `downward` C++ binary (no Python translator). This is the
/// fast path: feeding FD's *input* directly skips the ~95% of per-node cost the
/// translator otherwise incurs (measured: 202 ms translate vs 9 ms search).
pub fn run_downward_sas(sas: &str, heur: FdHeuristic) -> Result<HResult, FdError> {
    use std::io::Write;
    // Memoize by a hash of (SAS⁺ text, heuristic): different search nodes can
    // re-derive structurally identical compiled tasks.
    let key = {
        use std::hash::{Hash, Hasher};
        let mut h = crate::fasthash::FxHasher::default();
        sas.hash(&mut h);
        heur.tag().hash(&mut h);
        h.finish()
    };
    if let Some(v) = cache().lock().unwrap().get(&key).copied() {
        return Ok(v);
    }

    let dir = unique_tmp_dir();
    std::fs::create_dir_all(&dir)?;
    let plan_path = dir.join("sas_plan");
    let path = downward_path();
    let search = format!("astar({})", heur.evaluator());

    let spawn = std::process::Command::new(&path)
        .arg("--internal-plan-file")
        .arg(&plan_path)
        .arg("--search")
        .arg(&search)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .current_dir(&dir)
        .spawn();

    let result = (|| {
        let mut child = spawn.map_err(|source| FdError::Spawn {
            path: path.clone(),
            source,
        })?;
        child
            .stdin
            .take()
            .expect("piped stdin")
            .write_all(sas.as_bytes())?;
        let out = child.wait_with_output()?;
        let mut captured = String::from_utf8_lossy(&out.stdout).into_owned();
        captured.push_str(&String::from_utf8_lossy(&out.stderr));
        parse_initial_h(&captured, heur).ok_or(FdError::ParseFailure {
            output: truncate(&captured, 4000),
        })
    })();
    let _ = std::fs::remove_dir_all(&dir);
    if let Ok(v) = result {
        cache().lock().unwrap().insert(key, v);
    }
    result
}

/// Runs only Fast Downward's translator (PDDL → SAS+) on the given problem and
/// returns the SAS+ output as a string. This exposes FD's grounder so later
/// phases (the reachability grounder / Lplan, Phase 0d/4) can consume FD's
/// grounded operators instead of the naive Rust instantiation, riding FD's
/// grounding improvements. Parsing SAS+ into our action model is a separate
/// (later) step; this is the plumbing.
pub fn run_fd_translate(domain_pddl: &str, problem_pddl: &str) -> Result<String, FdError> {
    use std::io::Write;
    let dir = unique_tmp_dir();
    std::fs::create_dir_all(&dir)?;
    let domain_path = dir.join("domain.pddl");
    let problem_path = dir.join("problem.pddl");
    let sas_path = dir.join("output.sas");
    {
        std::fs::File::create(&domain_path)?.write_all(domain_pddl.as_bytes())?;
        std::fs::File::create(&problem_path)?.write_all(problem_pddl.as_bytes())?;
    }
    let path = fd_path();
    let spawn = std::process::Command::new(&path)
        .arg("--sas-file")
        .arg(&sas_path)
        .arg("--translate")
        .arg(&domain_path)
        .arg(&problem_path)
        .current_dir(&dir)
        .output();
    let result = (|| {
        let out = spawn.map_err(|source| FdError::Spawn {
            path: path.clone(),
            source,
        })?;
        if !sas_path.exists() {
            let mut captured = String::from_utf8_lossy(&out.stdout).into_owned();
            captured.push_str(&String::from_utf8_lossy(&out.stderr));
            return Err(FdError::ParseFailure {
                output: truncate(&captured, 4000),
            });
        }
        Ok(std::fs::read_to_string(&sas_path)?)
    })();
    let _ = std::fs::remove_dir_all(&dir);
    result
}

/// Writes the PDDL to a unique temp directory, runs Fast Downward there, returns
/// captured stdout+stderr. The temp directory is removed afterwards.
fn invoke_fd(
    domain_pddl: &str,
    problem_pddl: &str,
    heur: FdHeuristic,
) -> Result<String, FdError> {
    use std::io::Write;

    // Unique scratch directory (pid + a monotonically increasing counter).
    let dir = unique_tmp_dir();
    std::fs::create_dir_all(&dir)?;
    let domain_path = dir.join("domain.pddl");
    let problem_path = dir.join("problem.pddl");
    let sas_path = dir.join("output.sas");
    let plan_path = dir.join("sas_plan");
    {
        let mut f = std::fs::File::create(&domain_path)?;
        f.write_all(domain_pddl.as_bytes())?;
        let mut f = std::fs::File::create(&problem_path)?;
        f.write_all(problem_pddl.as_bytes())?;
    }

    let path = fd_path();
    // We only want h(init): A* prints "Initial heuristic value for <h>: N" before
    // expanding. A tiny bound keeps FD from running a full search on the (rare)
    // compiled instance it can solve outright; the initial-value line is emitted
    // regardless. `--sas-file`/`--plan-file` keep all artifacts inside `dir`.
    let search = format!("astar({})", heur.evaluator());
    let spawn = std::process::Command::new(&path)
        .arg("--sas-file")
        .arg(&sas_path)
        .arg("--plan-file")
        .arg(&plan_path)
        .arg(&domain_path)
        .arg(&problem_path)
        .arg("--search")
        .arg(&search)
        .current_dir(&dir)
        .output();

    let out = match spawn {
        Ok(o) => o,
        Err(source) => {
            let _ = std::fs::remove_dir_all(&dir);
            return Err(FdError::Spawn { path, source });
        }
    };

    let mut captured = String::from_utf8_lossy(&out.stdout).into_owned();
    captured.push_str(&String::from_utf8_lossy(&out.stderr));
    let _ = std::fs::remove_dir_all(&dir);
    Ok(captured)
}

/// Parses the initial heuristic value from Fast Downward output. Pure function so
/// it can be unit-tested without FD installed.
///
/// Recognises:
/// - `Initial heuristic value for <name>: <int>` → `Finite(int)`.
/// - `Initial heuristic value for <name>: infinity` → `Infinite`.
/// - A "no solution"/"unsolvable" report with no finite initial value →
///   `Infinite` (the relaxed goal is unreachable, a dead end).
///
/// The `<name>` is not strictly required to match `heur.fd_name()` (FD's printed
/// name has varied across versions), but a matching line is preferred.
pub fn parse_initial_h(output: &str, heur: FdHeuristic) -> Option<HResult> {
    const MARK: &str = "Initial heuristic value for ";
    let want = heur.fd_name();

    let mut fallback: Option<HResult> = None;
    for line in output.lines() {
        let line = line.trim();
        let Some(rest) = line.find(MARK).map(|i| &line[i + MARK.len()..]) else {
            continue;
        };
        // rest looks like "<name>: <value>"
        let Some(colon) = rest.find(':') else { continue };
        let name = rest[..colon].trim();
        let value = rest[colon + 1..].trim();
        let parsed = parse_h_value(value)?;
        if name == want {
            return Some(parsed);
        }
        // Keep the first line as a fallback if the name didn't match exactly.
        fallback.get_or_insert(parsed);
    }
    if fallback.is_some() {
        return fallback;
    }

    // No initial-value line. If FD reported the task unsolvable, treat as a dead
    // end (infinite). Otherwise we genuinely failed to parse.
    let lower = output.to_ascii_lowercase();
    if lower.contains("search stopped without finding a solution")
        || lower.contains("completely explored state space -- no solution")
        || lower.contains("task is provably unsolvable")
        || lower.contains("unsolvable")
    {
        return Some(HResult::Infinite);
    }
    None
}

fn parse_h_value(s: &str) -> Option<HResult> {
    let s = s.trim();
    if s.eq_ignore_ascii_case("infinity") || s.eq_ignore_ascii_case("inf") {
        return Some(HResult::Infinite);
    }
    // Values are non-negative integers in FD; accept a leading integer token.
    let tok: String = s.chars().take_while(|c| c.is_ascii_digit()).collect();
    if tok.is_empty() {
        return None;
    }
    tok.parse::<f32>().ok().map(HResult::Finite)
}

fn unique_tmp_dir() -> std::path::PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    std::env::temp_dir().join(format!("vhpop-fd-{pid}-{n}"))
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max {
        s.to_string()
    } else {
        format!("{}…(truncated)", &s[..max])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_matching_initial_value() {
        let out = "\
Parsing...
Initial heuristic value for ff: 12
f = 12 [1 evaluated, 0 expanded, t=0.0s]
Solution found!
";
        assert_eq!(
            parse_initial_h(out, FdHeuristic::Ff),
            Some(HResult::Finite(12.0))
        );
    }

    #[test]
    fn parses_lmcut_among_other_lines() {
        let out = "\
Initial heuristic value for lmcut: 7
New best heuristic value for lmcut: 5
";
        assert_eq!(
            parse_initial_h(out, FdHeuristic::LmCut),
            Some(HResult::Finite(7.0))
        );
    }

    #[test]
    fn parses_infinity() {
        let out = "Initial heuristic value for ff: infinity\n";
        assert_eq!(parse_initial_h(out, FdHeuristic::Ff), Some(HResult::Infinite));
    }

    #[test]
    fn zero_is_finite_goal_reached() {
        let out = "Initial heuristic value for hmax: 0\n";
        assert_eq!(
            parse_initial_h(out, FdHeuristic::HMax),
            Some(HResult::Finite(0.0))
        );
    }

    #[test]
    fn unsolvable_without_value_is_infinite() {
        let out = "Building causal graph...\nCompletely explored state space -- no solution!\n";
        assert_eq!(parse_initial_h(out, FdHeuristic::Ff), Some(HResult::Infinite));
    }

    #[test]
    fn unrelated_output_fails_to_parse() {
        let out = "Parsing...\nDone.\n";
        assert_eq!(parse_initial_h(out, FdHeuristic::Ff), None);
    }

    #[test]
    fn name_mismatch_falls_back() {
        // Older FD might print a different name; we still recover the value.
        let out = "Initial heuristic value for h^add: 4\n";
        assert_eq!(
            parse_initial_h(out, FdHeuristic::HAdd),
            Some(HResult::Finite(4.0))
        );
    }

    /// End-to-end against the frozen Fast Downward submodule. Skips (passes) if
    /// FD is not available so the suite stays green without it.
    #[test]
    fn run_fd_on_gripper_if_available() {
        if !fd_available() {
            eprintln!("skipping: Fast Downward not available (set POTOROO_FD)");
            return;
        }
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/examples");
        let domain = std::fs::read_to_string(format!("{dir}/gripper-domain.pddl")).unwrap();
        let problem = std::fs::read_to_string(format!("{dir}/gripper-2.pddl")).unwrap();
        // FF on the unmodified gripper-2 init state is 3 (verified via the driver).
        let h = run_fd_heuristic(&domain, &problem, FdHeuristic::Ff).expect("FD run");
        assert_eq!(h, HResult::Finite(3.0));
        // Second call must hit the memoization cache and return the same value.
        let h2 = run_fd_heuristic(&domain, &problem, FdHeuristic::Ff).expect("FD run cached");
        assert_eq!(h2, HResult::Finite(3.0));
    }
}
