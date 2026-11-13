# Quick start

## Build

Install [Rust with rustup](https://rustup.rs), then:

```bash
git clone https://github.com/HarrisonOates/potoroo.git
cd potoroo
cargo build --release
cargo test
```

The repository pins Rust 1.99.1 (including Clippy and rustfmt) in
`rust-toolchain.toml`; rustup selects it automatically. CI uses the same version.

The executable is `target/release/potoroo`. The default build is pure Rust.
For a faster Lplan LP backend, use `cargo build --release --features highs-lp`;
this also requires CMake and a C++ compiler.

## Solve an example

```bash
# Lifted POCL with the default ADD/LIFO ranking
./target/release/potoroo examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Greedy search
./target/release/potoroo -s GBFS -h ADD examples/gripper-domain.pddl examples/gripper-4.pddl

# Ground actions with the Lplan LP heuristic
./target/release/potoroo -g -h LPLAN examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl

# Finite-domain POCL, with progress on stderr
./target/release/potoroo --fdr-pocl -v examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl
```

## Fast Downward

[Fast Downward](https://github.com/aibasel/downward) is required for finite-domain
search (`--fdr-pocl`), `LPSAS`, and `COMPILE*` heuristics. Ground mode (`-g`) uses
its reachability-based grounder when available and otherwise falls back to Cartesian
instantiation with static-precondition filtering.

```bash
git clone https://github.com/aibasel/downward.git
cd downward
python build.py
export POTOROO_FD="$PWD/fast-downward.py"
export POTOROO_DOWNWARD="$PWD/builds/release/bin/downward"
cd ..
```

Alternatively, put `fast-downward.py` on `PATH`. `POTOROO_DOWNWARD` selects the
C++ executable used to evaluate compiled tasks. Tests requiring Fast Downward
skip automatically when it is unavailable.

See [Command-line reference](planner-usage.md) for input and output conventions, defaults, and limits.
