# HTN planning

The optional HTN planner is built separately from the classical planner:

```bash
cargo build --release --features htn --bin potoroo-htn
./target/release/potoroo-htn --help
```

The HTN layer is work in progress. Its default input pipeline accepts an HDDL domain and problem and invokes `pandaPIparser` and `pandaPIgrounder`. Select executable paths with `--parser` and `--grounder`, or the `POTOROO_HTN_PARSER` and `POTOROO_HTN_GROUNDER` environment variables.

```bash
./target/release/potoroo-htn domain.hddl problem.hddl
```

`--lifted` accepts one parser-produced `.htn` file and runs the grounder. `--grounded` accepts one grounded PANDA `.sas` file; this is not the Fast Downward SAS+ format used by classical finite-domain search.

Use `--help` for the current search strategies, flaw policies, bounds, and resource limits.
