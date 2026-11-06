//! External HDDL parsing and Malleefowl grounding through their file interfaces.
//! Executables are explicit arguments, documented environment variables, or PATH
//! entries. No dependency on a particular sibling checkout is introduced.
use std::fs::{self, File};
use std::io::{Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use super::{input, Problem};

#[derive(Clone, Debug)]
pub struct Tools {
    pub parser: PathBuf,
    pub grounder: PathBuf,
}

impl Default for Tools {
    fn default() -> Self {
        Self {
            parser: std::env::var_os("POTOROO_HTN_PARSER")
                .map(PathBuf::from)
                .unwrap_or_else(|| "pandaPIparser".into()),
            grounder: std::env::var_os("POTOROO_MALLEEFOWL")
                .map(PathBuf::from)
                .unwrap_or_else(|| "malleefowl".into()),
        }
    }
}

pub enum Input<'a> {
    Hddl { domain: &'a Path, problem: &'a Path },
    Lifted(&'a Path),
    Grounded(&'a Path),
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("HTN pipeline deadline reached")]
    Deadline,
    #[error("{0}")]
    Failed(String),
}

struct Workspace(PathBuf);

impl Workspace {
    fn new() -> Result<Self, Error> {
        static SERIAL: AtomicU64 = AtomicU64::new(0);
        for _ in 0..100 {
            let serial = SERIAL.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("potoroo-htn-{}-{serial}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(Self(path)),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(Error::Failed(format!("create HTN workspace: {e}"))),
            }
        }
        Err(Error::Failed(
            "could not allocate a fresh HTN workspace".into(),
        ))
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn check_deadline(deadline: Option<Instant>) -> Result<(), Error> {
    if deadline.is_some_and(|d| Instant::now() >= d) {
        Err(Error::Deadline)
    } else {
        Ok(())
    }
}

/// Load an existing grounded model, or run parser/grounder first. Grounding
/// disables abstract expansion so experiments observe the supplied hierarchy.
pub fn load(input: Input<'_>, tools: &Tools, deadline: Option<Instant>) -> Result<Problem, Error> {
    check_deadline(deadline)?;
    if let Input::Grounded(path) = input {
        return read(path, deadline);
    }
    let workspace = Workspace::new()?;
    let parsed = workspace.0.join("input.htn");
    let grounded = workspace.0.join("output.sas");
    let lifted = match input {
        Input::Hddl { domain, problem } => {
            let mut command = Command::new(&tools.parser);
            command.arg(domain).arg(problem).arg(&parsed);
            run(&mut command, "HDDL parser", &workspace, deadline)?;
            parsed.as_path()
        }
        Input::Lifted(path) => path,
        Input::Grounded(_) => unreachable!(),
    };
    let mut command = Command::new(&tools.grounder);
    command
        .arg("--target=bowerbird")
        .arg("--no-abstract-expansion")
        .arg(lifted)
        .arg(&grounded);
    run(&mut command, "Malleefowl", &workspace, deadline)?;
    read(&grounded, deadline)
}

fn read(path: &Path, deadline: Option<Instant>) -> Result<Problem, Error> {
    let source =
        fs::read_to_string(path).map_err(|e| Error::Failed(format!("{}: {e}", path.display())))?;
    check_deadline(deadline)?;
    let model =
        input::read(&source).map_err(|e| Error::Failed(format!("{}: {e}", path.display())))?;
    check_deadline(deadline)?;
    Ok(model)
}

fn run(
    command: &mut Command,
    label: &str,
    workspace: &Workspace,
    deadline: Option<Instant>,
) -> Result<(), Error> {
    check_deadline(deadline)?;
    let stdout_path = workspace.0.join("stdout.log");
    let stderr_path = workspace.0.join("stderr.log");
    let stdout = File::create(&stdout_path).map_err(|e| Error::Failed(e.to_string()))?;
    let stderr = File::create(&stderr_path).map_err(|e| Error::Failed(e.to_string()))?;
    let mut child = command.stdin(Stdio::null()).stdout(stdout).stderr(stderr).spawn()
        .map_err(|e| Error::Failed(format!("could not run {label} ({:?}): {e}; configure --parser/--grounder or POTOROO_HTN_PARSER/POTOROO_MALLEEFOWL", command.get_program())))?;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {}
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(Error::Failed(format!("waiting for {label}: {e}")));
            }
        }
        if check_deadline(deadline).is_err() {
            let _ = child.kill();
            let _ = child.wait();
            return Err(Error::Deadline);
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    check_deadline(deadline)?;
    if !status.success() {
        let mut diagnostic = String::new();
        for path in [&stdout_path, &stderr_path] {
            if let Ok(mut file) = File::open(path) {
                let len = file.metadata().map(|m| m.len()).unwrap_or(0);
                let _ = file.seek(SeekFrom::Start(len.saturating_sub(4096)));
                let mut bytes = Vec::new();
                let _ = file.take(4096).read_to_end(&mut bytes);
                diagnostic.push_str(&String::from_utf8_lossy(&bytes));
            }
        }
        return Err(Error::Failed(format!(
            "{label} exited with {status}:\n{}",
            diagnostic.trim()
        )));
    }
    Ok(())
}
