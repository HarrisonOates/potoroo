#!/usr/bin/env bash
# Benchmark harness (Phase 0b). Runs the Potoroo binary with one or more
# heuristics across a curated set of benchmark problems, collecting the opt-in
# `POTOROO_STATS_JSON` lines (coverage + search-node counts), and prints a
# per-problem comparison table via bench.py.
#
# Usage:
#   scripts/bench.sh [TARGET_HEURISTIC] [BASELINES_CSV] [TIMEOUT_SECS]
# Defaults:
#   TARGET_HEURISTIC = ADD
#   BASELINES_CSV    = UCPOP,ADD       (the target is appended if missing)
#   TIMEOUT_SECS     = 60
#
# Env:
#   POTOROO_GROUND=1   pass -g (ground mode) to the planner.
set -euo pipefail

TARGET="${1:-ADD}"
BASELINES="${2:-UCPOP,ADD}"
TIMEOUT="${3:-60}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUST_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
EX="$RUST_DIR/examples"
BIN="$RUST_DIR/target/release/potoroo"

# Ground runs need Fast Downward for reachability-based grounding; default to
# the in-repo checkout so they don't silently fall back to naive grounding.
if [ -z "${POTOROO_FD:-}" ] && [ -x "$RUST_DIR/downward/fast-downward.py" ]; then
  export POTOROO_FD="$RUST_DIR/downward/fast-downward.py"
fi
if [ -z "${POTOROO_DOWNWARD:-}" ]; then
  dw="$(ls "$RUST_DIR"/downward/builds/*/bin/downward 2>/dev/null | head -1)"
  [ -n "$dw" ] && export POTOROO_DOWNWARD="$dw"
fi

# Curated (problem) list covering the paper's domains (blocks/gripper/logistics)
# plus a few classics. Domains are auto-resolved from each problem's (:domain X).
PROBLEMS=(
  sussman-anomaly.pddl
  bw-large-a.pddl
  gripper-2.pddl
  gripper-4.pddl
  gripper-6.pddl
  logistics-a.pddl
  logistics-b.pddl
  hanoi-3.pddl
  rocket-ext-a.pddl
  ferry-domain.pddl       # skipped (a domain, not a problem) -- filtered below
)

# Build the heuristic set: baselines, with the target appended if not present.
IFS=',' read -r -a HEURS <<< "$BASELINES"
case ",$BASELINES," in
  *",$TARGET,"*) ;;
  *) HEURS+=("$TARGET") ;;
esac

GROUND_FLAG=()
[ "${POTOROO_GROUND:-0}" = "1" ] && GROUND_FLAG=(-g)

echo "Building release binary..." >&2
( cd "$RUST_DIR" && cargo build --release --quiet )

# Map a problem's (:domain NAME) to the domain file declaring (domain NAME).
resolve_domain() {
  local prob="$1"
  local dname
  dname="$(grep -ohiE '\(:domain[[:space:]]+[a-zA-Z0-9_-]+' "$prob" | head -1 \
            | sed -E 's/.*\(:domain[[:space:]]+//I')"
  [ -z "$dname" ] && return 1
  local f
  for f in "$EX"/*domain*.pddl "$EX"/*.pddl; do
    if grep -qiE "\(define[[:space:]]*\(domain[[:space:]]+$dname\)" "$f"; then
      echo "$f"; return 0
    fi
  done
  return 1
}

STATS_FILE="$(mktemp)"
trap 'rm -f "$STATS_FILE"' EXIT

for pf in "${PROBLEMS[@]}"; do
  prob="$EX/$pf"
  [ -f "$prob" ] || { echo "skip (missing): $pf" >&2; continue; }
  # Filter out files that are domains (no (:domain ...) problem header).
  grep -qiE '\(:domain' "$prob" || { echo "skip (not a problem): $pf" >&2; continue; }
  dom="$(resolve_domain "$prob")" || { echo "skip (no domain): $pf" >&2; continue; }

  for h in "${HEURS[@]}"; do
    echo "run: $pf  -h $h ${GROUND_FLAG[*]}" >&2
    # The binary prints STATS to stderr; capture stderr, keep only STATS lines.
    POTOROO_STATS_JSON=1 timeout "$TIMEOUT" \
      "$BIN" -h "$h" "${GROUND_FLAG[@]}" "$dom" "$prob" \
      >/dev/null 2>>"$STATS_FILE" || {
        # Timeout / nonzero: synthesize an unsolved STATS row so the table shows it.
        pname="$(grep -ohiE '\(problem[[:space:]]+[a-zA-Z0-9_-]+' "$prob" | head -1 \
                  | sed -E 's/.*\(problem[[:space:]]+//I')"
        # Label must match the binary's "ALG(HEUR)" so the row lands in the
        # same table column (bench.sh always runs the default algorithm A).
        echo "STATS {\"problem\":\"${pname:-$pf}\",\"heuristic\":\"A($h)\",\"ground\":${POTOROO_GROUND:-false},\"solved\":false,\"plan_len\":0,\"nodes_generated\":0,\"nodes_visited\":0,\"wall_ms\":$((TIMEOUT*1000))}" >>"$STATS_FILE"
      }
  done
done

# Keep only the STATS lines and tabulate.
grep '^STATS ' "$STATS_FILE" | sed 's/^STATS //' | python3 "$SCRIPT_DIR/bench.py"
