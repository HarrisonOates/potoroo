# Potoroo

A partial-order causal-link (POCL) planner written in Rust, supporting lifted,
ground, and finite-domain classical planning.

## Quick start

Install [Rust with rustup](https://rustup.rs), then:

```bash
git clone https://github.com/HarrisonOates/potoroo.git
cd potoroo
cargo build --release
./target/release/potoroo examples/blocks-world-domain.pddl examples/sussman-anomaly.pddl
```

The repository pins Rust 1.99.1. The default build is pure Rust.
Run `cargo test` for the test suite and `./target/release/potoroo -H` for help
(`-h` selects a heuristic).

Input files may appear in either order; a single file or stdin may contain a
domain and problems. Plans are printed to stdout. Add `-v` for search progress.

[Fast Downward](https://github.com/aibasel/downward) is required for
`--fdr-pocl` and some heuristics. The optional HTN executable is built with
`--features htn`.

## Documentation

See the [documentation](docs/README.md) for [installation](docs/quick-start.md),
[planner usage](docs/planner-usage.md), [heuristics](docs/heuristics.md),
and [PDDL support](docs/pddl-support.md).

Report bugs and feature requests in [Issues](https://github.com/HarrisonOates/potoroo/issues).

## License

Copyright 2026 Harrison Oates. Licensed under the [Apache License 2.0](LICENSE).
See [NOTICE](NOTICE) for attribution and license notices.
