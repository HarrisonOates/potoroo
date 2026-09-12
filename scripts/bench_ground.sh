#!/usr/bin/env bash
# Repeated-run wall-clock benchmark for the ground representations (`-g` and
# `--fdr-pocl`), the harness for performance work on those two search paths.
#
# `bench.sh` runs each case once, which on a loaded machine buries a few percent
# of real change under scheduling noise. Here every case runs REPS times and the
# *minimum* wall time is reported: the fastest sample is the one least polluted
# by other work on the machine, so it is the stable statistic to hill-climb on.
# Node counts are exact and are reported alongside — a change that moves them has
# changed search behaviour, not just its speed.
#
# Usage:
#   scripts/bench_ground.sh [REPS] [TIMEOUT_SECS]
# Defaults:
#   REPS          = 5
#   TIMEOUT_SECS  = 120
#
# Env:
#   POTOROO_BIN    planner binary (default: target/release/potoroo)
#   POTOROO_MEM_MB address-space cap per run in MB (default: 4096). Ground
#                  search on a hard instance will otherwise grow until the
#                  machine swaps, which measures the swap, not the planner.
#   POTOROO_MODES  space-separated modes (default: "-g --fdr-pocl")
#   POTOROO_JSON   file to append the per-case STATS rows to, for bench.py.
set -uo pipefail

REPS="${1:-5}"
TIMEOUT="${2:-120}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
EX="$ROOT/examples"
BIN="${POTOROO_BIN:-$ROOT/target/release/potoroo}"
MEM_MB="${POTOROO_MEM_MB:-4096}"
MODES="${POTOROO_MODES:--g --fdr-pocl}"

# Both ground paths need Fast Downward; default to the in-repo checkout so a run
# never silently falls back to naive grounding and measures a different task.
if [ -z "${POTOROO_FD:-}" ] && [ -x "$ROOT/downward/fast-downward.py" ]; then
  export POTOROO_FD="$ROOT/downward/fast-downward.py"
fi
if [ -z "${POTOROO_DOWNWARD:-}" ]; then
  dw="$(ls "$ROOT"/downward/builds/*/bin/downward 2>/dev/null | head -1 || true)"
  [ -n "$dw" ] && export POTOROO_DOWNWARD="$dw"
fi

# Cases spanning the domains ground search is actually exercised on, sized so
# each solves well inside the timeout but runs long enough to time.
CASES=(
  "blocks-world-domain.pddl:sussman-anomaly.pddl"
  "gripper-domain.pddl:gripper-12.pddl"
  "gripper-domain.pddl:gripper-20.pddl"
  "gripper-domain.pddl:gripper-40.pddl"
  "logistics-domain.pddl:logistics-c.pddl"
  "logistics-domain.pddl:logistics-e.pddl"
  "rocket-domain.pddl:rocket-ext-a.pddl"
  "rocket-domain.pddl:rocket-ext-b.pddl"
  "grid-domain.pddl:simple-grid2.pddl"
  "ferry-domain.pddl:test-ferry.pddl"
)

echo "Building release binary..." >&2
( cd "$ROOT" && cargo build --release --quiet ) || exit 1

JSON="${POTOROO_JSON:-}"
[ -n "$JSON" ] && : > "$JSON"

printf '%-11s %-22s %9s %9s %8s %8s\n' mode problem generated visited min_ms max_ms
printf -- '---------------------------------------------------------------------\n'

total=0
for mode in $MODES; do
  for c in "${CASES[@]}"; do
    dom="$EX/${c%%:*}"
    prob="$EX/${c##*:}"
    [ -f "$dom" ] && [ -f "$prob" ] || { echo "skip (missing): $c" >&2; continue; }

    # Node counts come from one extra run under POTOROO_STATS_JSON. The timed
    # runs below deliberately leave it unset: requesting telemetry turns on
    # per-evaluation heuristic timing, and timing a configuration nobody runs by
    # default would report a number no user sees. The planner's own `Time:` line
    # is the same search timer the STATS row reports.
    row=$(
      ulimit -v $((MEM_MB * 1024)) 2>/dev/null
      POTOROO_STATS_JSON=1 timeout "$TIMEOUT" "$BIN" $mode "$dom" "$prob" 2>&1 >/dev/null \
        | grep '^STATS ' | head -1
    )
    gen=$(printf '%s' "$row" | grep -o '"nodes_generated":[0-9]*' | cut -d: -f2)
    vis=$(printf '%s' "$row" | grep -o '"nodes_visited":[0-9]*' | cut -d: -f2)
    : "${gen:=-}" "${vis:=-}"

    best=""; worst=""
    for _ in $(seq "$REPS"); do
      # The cap is on address space, applied in a subshell so it never leaks
      # into the rest of this script.
      ms=$(
        ulimit -v $((MEM_MB * 1024)) 2>/dev/null
        timeout "$TIMEOUT" "$BIN" $mode "$dom" "$prob" 2>/dev/null \
          | sed -n 's/^Time: //p' | head -1
      )
      [ -z "$ms" ] && { best="FAIL"; break; }
      [ -z "$best" ] && { best="$ms"; worst="$ms"; }
      [ "$ms" -lt "$best" ] && best="$ms"
      [ "$ms" -gt "$worst" ] && worst="$ms"
    done

    printf '%-11s %-22s %9s %9s %8s %8s\n' "$mode" "${c##*:}" "$gen" "$vis" "$best" "${worst:--}"
    case "$best" in
      ''|FAIL) ;;
      *) total=$((total + best)) ;;
    esac
    # Record the fastest sample's row, relabelled by mode so bench.py groups it.
    if [ -n "$JSON" ] && [ -n "$row" ] && [ "$best" != "FAIL" ]; then
      printf '%s\n' "$row" \
        | sed -e "s/\"heuristic\":\"[^\"]*\"/\"heuristic\":\"$mode\"/" \
              -e "s/\"wall_ms\":[0-9]*/\"wall_ms\":$best/" >> "$JSON"
    fi
  done
done

printf -- '---------------------------------------------------------------------\n'
printf 'total of minima: %s ms  (reps=%s, mem cap %s MB)\n' "$total" "$REPS" "$MEM_MB"
