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
# Pass POTOROO_BASE to compare two binaries. The two are then run *interleaved*,
# rep by rep on the same case, and each gets its own minimum. This is the only
# way to read a change worth a few percent: consecutive whole-harness runs drift
# with whatever else the machine is doing, enough to invert the sign of a real
# 1% improvement. Do not compare two separate invocations of this script.
#
# What this can resolve: pointing POTOROO_BASE at the very binary under test is
# a null experiment, and at REPS=7 it reports 0% overall but per-case figures
# spanning -6%..+3%. So read the total, and per case trust only the instances
# that run long enough to swamp process startup -- gripper-20 and simple-grid2
# hold to within 2%, while anything near 40 ms is noise. A per-case claim below
# those bounds needs more reps before it means anything.
#
# Usage:
#   scripts/bench_ground.sh [REPS] [TIMEOUT_SECS]
# Defaults:
#   REPS          = 5
#   TIMEOUT_SECS  = 120
#
# Env:
#   POTOROO_BIN    planner binary (default: target/release/potoroo)
#   POTOROO_BASE   second binary to compare against; enables the paired columns
#                  and suppresses the release build (both binaries are given).
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
BASE="${POTOROO_BASE:-}"
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

if [ -z "$BASE" ]; then
  echo "Building release binary..." >&2
  ( cd "$ROOT" && cargo build --release --quiet ) || exit 1
fi

JSON="${POTOROO_JSON:-}"
[ -n "$JSON" ] && : > "$JSON"

# One timed run of $1 on the case, printing the planner's own `Time:` line.
#
# POTOROO_STATS_JSON is deliberately left unset here: requesting telemetry turns
# on per-evaluation heuristic timing, and timing a configuration nobody runs by
# default would report a number no user sees. `Time:` is the same search timer
# the STATS row reports. The address-space cap is applied in a subshell so it
# never leaks into the rest of this script.
time_once() {
  (
    ulimit -v $((MEM_MB * 1024)) 2>/dev/null
    timeout "$TIMEOUT" "$1" $mode "$dom" "$prob" 2>/dev/null \
      | sed -n 's/^Time: //p' | head -1
  )
}

if [ -n "$BASE" ]; then
  printf '%-11s %-22s %9s %9s %9s %8s\n' mode problem generated base_ms now_ms change
else
  printf '%-11s %-22s %9s %9s %8s %8s\n' mode problem generated visited min_ms max_ms
fi
printf -- '---------------------------------------------------------------------------\n'

total=0
base_total=0
for mode in $MODES; do
  for c in "${CASES[@]}"; do
    dom="$EX/${c%%:*}"
    prob="$EX/${c##*:}"
    [ -f "$dom" ] && [ -f "$prob" ] || { echo "skip (missing): $c" >&2; continue; }

    # Node counts come from one extra run under POTOROO_STATS_JSON.
    row=$(
      ulimit -v $((MEM_MB * 1024)) 2>/dev/null
      POTOROO_STATS_JSON=1 timeout "$TIMEOUT" "$BIN" $mode "$dom" "$prob" 2>&1 >/dev/null \
        | grep '^STATS ' | head -1
    )
    gen=$(printf '%s' "$row" | grep -o '"nodes_generated":[0-9]*' | cut -d: -f2)
    vis=$(printf '%s' "$row" | grep -o '"nodes_visited":[0-9]*' | cut -d: -f2)
    : "${gen:=-}" "${vis:=-}"

    best=""; worst=""; base_best=""
    for _ in $(seq "$REPS"); do
      # Interleaved: the two binaries see the same machine conditions within a
      # rep, so a drift that would swamp the difference hits both alike.
      if [ -n "$BASE" ]; then
        bms=$(time_once "$BASE")
        if [ -z "$bms" ]; then base_best="FAIL"; else
          if [ -z "$base_best" ] || { [ "$base_best" != FAIL ] && [ "$bms" -lt "$base_best" ]; }; then
            base_best="$bms"
          fi
        fi
      fi
      ms=$(time_once "$BIN")
      [ -z "$ms" ] && { best="FAIL"; break; }
      [ -z "$best" ] && { best="$ms"; worst="$ms"; }
      [ "$ms" -lt "$best" ] && best="$ms"
      [ "$ms" -gt "$worst" ] && worst="$ms"
    done

    if [ -n "$BASE" ]; then
      change="-"
      if [ "$best" != FAIL ] && [ "$base_best" != FAIL ] && [ -n "$base_best" ] \
         && [ "$base_best" -gt 0 ] 2>/dev/null; then
        change="$(( (best - base_best) * 100 / base_best ))%"
        base_total=$((base_total + base_best))
        total=$((total + best))
      fi
      printf '%-11s %-22s %9s %9s %9s %8s\n' \
        "$mode" "${c##*:}" "$gen" "${base_best:--}" "$best" "$change"
    else
      printf '%-11s %-22s %9s %9s %8s %8s\n' \
        "$mode" "${c##*:}" "$gen" "$vis" "$best" "${worst:--}"
      case "$best" in
        ''|FAIL) ;;
        *) total=$((total + best)) ;;
      esac
    fi

    # Record the fastest sample's row, relabelled by mode so bench.py groups it.
    if [ -n "$JSON" ] && [ -n "$row" ] && [ "$best" != "FAIL" ]; then
      printf '%s\n' "$row" \
        | sed -e "s/\"heuristic\":\"[^\"]*\"/\"heuristic\":\"$mode\"/" \
              -e "s/\"wall_ms\":[0-9]*/\"wall_ms\":$best/" >> "$JSON"
    fi
  done
done

printf -- '---------------------------------------------------------------------------\n'
if [ -n "$BASE" ]; then
  change="-"
  [ "$base_total" -gt 0 ] && change="$(( (total - base_total) * 100 / base_total ))%"
  printf 'total of minima: %s ms -> %s ms (%s)  (reps=%s, mem cap %s MB)\n' \
    "$base_total" "$total" "$change" "$REPS" "$MEM_MB"
  printf 'base: %s\n now: %s\n' "$BASE" "$BIN"
else
  printf 'total of minima: %s ms  (reps=%s, mem cap %s MB)\n' "$total" "$REPS" "$MEM_MB"
fi
