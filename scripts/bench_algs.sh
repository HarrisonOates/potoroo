#!/usr/bin/env bash
# Benchmark new state-based search algorithms (BFS, GBFS, LGBFS, LGBFS-D) vs
# the A* baseline, using the hadd heuristic (-H ADD), across key benchmark
# problems in both lifted and ground modes.
#
# Usage:
#   scripts/bench_algs.sh [TIMEOUT_SECS]
# Defaults:
#   TIMEOUT_SECS = 60
#
# Set POTOROO_GROUND=1 to skip ground mode (lifted only); unset for both modes.
set -euo pipefail

TIMEOUT="${1:-60}"

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
  dw="$(ls "$RUST_DIR"/downward/builds/*/bin/downward 2>/dev/null | head -1 || true)"
  if [ -n "$dw" ]; then
    export POTOROO_DOWNWARD="$dw"
  fi
fi

# Benchmark problems: small-to-medium instances across blocks, gripper, logistics, hanoi.
PROBLEMS=(
  sussman-anomaly.pddl
  bw-large-a.pddl
#  bw-large-b.pddl
#  bw-large-c.pddl
  gripper-2.pddl
  gripper-4.pddl
  gripper-6.pddl
#  gripper-8.pddl
#  gripper-10.pddl
#  gripper-12.pddl
  logistics-a.pddl
  logistics-b.pddl
  hanoi-3.pddl
  rocket-ext-a.pddl
)

# Algorithms to benchmark. Each entry is "-S ALG [-H HEUR]" flags.
ALGORITHMS=(
  "-s A    -h ADD"
  "-s GBFS -h ADD"
  "-s LGBFS -h ADD"
  "-s LGBFS-D -h ADD"
  "-s ALT  -h ADD"
  "-s BFS"
)

echo "Building release binary..." >&2
( cd "$RUST_DIR" && cargo build --release --quiet )

resolve_domain() {
  local prob="$1"
  local dname
  dname="$(grep -ohiE '\(:domain[[:space:]]+[a-zA-Z0-9_-]+' "$prob" | head -1 \
            | sed -E 's/.*\(:domain[[:space:]]+//I')"
  [ -z "$dname" ] && return 1
  for f in "$EX"/*domain*.pddl "$EX"/*.pddl; do
    if grep -qiE "\(define[[:space:]]*\(domain[[:space:]]+$dname\)" "$f"; then
      echo "$f"; return 0
    fi
  done
  return 1
}

STATS_FILE="$(mktemp)"
trap 'rm -f "$STATS_FILE"' EXIT

run_mode() {
  local mode="$1"   # "lifted" or "ground"
  local gflag=()
  [ "$mode" = "ground" ] && gflag=(-g)

  for pf in "${PROBLEMS[@]}"; do
    prob="$EX/$pf"
    [ -f "$prob" ] || { echo "skip (missing): $pf" >&2; continue; }
    grep -qiE '\(:domain' "$prob" || { echo "skip (not a problem): $pf" >&2; continue; }
    dom="$(resolve_domain "$prob")" || { echo "skip (no domain): $pf" >&2; continue; }

    pname="$(grep -ohiE '\(problem[[:space:]]+[a-zA-Z0-9_-]+' "$prob" | head -1 \
              | sed -E 's/.*\(problem[[:space:]]+//I')"

    for alg_flags in "${ALGORITHMS[@]}"; do
      # Build the "ALG(HEUR)" label the binary emits, so synthesized timeout
      # rows land in the same table column as real runs.
      alg="$(echo "$alg_flags" | sed -nE 's/.*-s +([^ ]+).*/\1/p')"
      heur="$(echo "$alg_flags" | sed -nE 's/.*-h +([^ ]+).*/\1/p')"
      alg_label="${alg:-A}(${heur:-UCPOP})"
      echo "run [$mode]: $pf  $alg_flags" >&2

      # shellcheck disable=SC2086
      POTOROO_STATS_JSON=1 timeout "$TIMEOUT" \
        "$BIN" $alg_flags "${gflag[@]}" "$dom" "$prob" \
        >/dev/null 2>>"$STATS_FILE" || {
          echo "STATS {\"problem\":\"${pname:-$pf}\",\"heuristic\":\"${alg_label}\",\"ground\":$([ "$mode" = "ground" ] && echo true || echo false),\"solved\":false,\"plan_len\":0,\"nodes_generated\":0,\"nodes_visited\":0,\"wall_ms\":$((TIMEOUT*1000))}" >>"$STATS_FILE"
        }
    done
  done
}

echo ""
echo "=== LIFTED MODE ==="
run_mode "lifted"

if [ "${POTOROO_GROUND:-0}" != "1" ]; then
  echo ""
  echo "=== GROUND MODE ==="
  run_mode "ground"
fi

echo ""
echo "=== RESULTS ==="
grep '^STATS ' "$STATS_FILE" | sed 's/^STATS //' | python3 "$SCRIPT_DIR/bench.py"
