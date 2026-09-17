#!/usr/bin/env bash
# Coverage sweep over a benchmark corpus (downward-benchmarks by default).
#
#   scripts/lm_sweep.sh [OPTIONS]
#     -b DIR      benchmark root, one directory per domain family
#                 (default: ../downward-benchmarks)
#     -c CSV      heuristic configurations to compare
#                 (default: ADD,RELAX,LM,LMF,LMFO)
#     -t SECS     per-run wall timeout (default 60)
#     -n N        problems per family, smallest first (default 5)
#     -j N        concurrent runs (default 4)
#     -m MB       per-run address-space cap (default 4096)
#     -o FILE     result CSV (default sweep-results.csv)
#
# Writes one CSV row per (family, problem, config) and prints a per-family and
# per-config coverage table. Runs are capped in both time and address space, so
# a run that blows up is recorded as unsolved rather than taking the machine
# down with it.
set -u

BENCH="../downward-benchmarks"
CONFIGS="ADD,RELAX,LM,LMF,LMFO"
TIMEOUT=60
PER_FAMILY=5
JOBS=4
MEM_MB=4096
OUT="sweep-results.csv"

while getopts "b:c:t:n:j:m:o:" opt; do
  case "$opt" in
    b) BENCH="$OPTARG" ;;
    c) CONFIGS="$OPTARG" ;;
    t) TIMEOUT="$OPTARG" ;;
    n) PER_FAMILY="$OPTARG" ;;
    j) JOBS="$OPTARG" ;;
    m) MEM_MB="$OPTARG" ;;
    o) OUT="$OPTARG" ;;
    *) sed -n '2,20p' "$0" >&2; exit 2 ;;
  esac
done

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/.." && pwd)"
BIN="$root/target/release/potoroo"

[ -d "$BENCH" ] || { echo "no benchmark directory at $BENCH" >&2; exit 2; }
[ -x "$BIN" ]   || { echo "no planner binary at $BIN (cargo build --release)" >&2; exit 2; }

# One run, printing a CSV row. Kept as a function so xargs can call it.
#
# The row is assembled in a variable and written with a single `printf`: several
# runs append to the same file at once, and one write per row is what keeps them
# from interleaving into a row that parses as neither.
run_one() {
  family="$1"; domain="$2"; problem="$3"; config="$4"
  name="$(basename "$problem" .pddl)"
  stats="$(
    ulimit -v $((MEM_MB * 1024)) 2>/dev/null
    POTOROO_STATS_JSON=1 timeout "$TIMEOUT" "$BIN" -h "$config" "$domain" "$problem" \
      2>&1 >/dev/null | grep '^STATS ' | head -1
  )"
  if [ -z "$stats" ]; then
    printf '%s,%s,%s,0,0,0,%s\n' "$family" "$name" "$config" "$((TIMEOUT * 1000))"
    return
  fi
  measured="$(
    printf '%s\n' "${stats#STATS }" | python3 -c '
import json, sys
d = json.load(sys.stdin)
print("%d,%d,%d,%d" % (1 if d.get("solved") else 0, d.get("plan_len", 0),
                       d.get("nodes_generated", 0), d.get("wall_ms", 0)))'
  )"
  if [ -z "$measured" ]; then
    printf '%s,%s,%s,0,0,0,%s\n' "$family" "$name" "$config" "$((TIMEOUT * 1000))"
    return
  fi
  printf '%s,%s,%s,%s\n' "$family" "$name" "$config" "$measured"
}
export -f run_one
export BIN TIMEOUT MEM_MB

# Every (family, problem, config) triple, as a null-separated work list.
work="$(mktemp)"
trap 'rm -f "$work"' EXIT
IFS=',' read -r -a configs <<< "$CONFIGS"
for dir in "$BENCH"/*/; do
  family="$(basename "$dir")"
  # Smallest problems first: the sweep is about coverage at the easy end, where
  # a heuristic difference shows up as solved-vs-not rather than as a timeout
  # for every configuration alike.
  problems="$(ls -S -r "$dir"/*.pddl 2>/dev/null | grep -vi domain | head -"$PER_FAMILY")"
  [ -z "$problems" ] && continue
  for problem in $problems; do
    # Families like `airport` ship one domain per problem alongside it; the
    # rest share a single `domain.pddl`.
    domain="${problem%.pddl}-domain.pddl"
    [ -f "$domain" ] || domain="$dir/domain.pddl"
    [ -f "$domain" ] || domain="$(ls "$dir"/*domain*.pddl 2>/dev/null | head -1)"
    [ -f "$domain" ] || continue
    for config in "${configs[@]}"; do
      printf '%s\t%s\t%s\t%s\0' "$family" "$domain" "$problem" "$config" >> "$work"
    done
  done
done

total="$(tr -dc '\0' < "$work" | wc -c)"
echo "running $total planner invocations, $JOBS at a time" >&2

echo "family,problem,config,solved,cost,nodes,ms" > "$OUT"
# shellcheck disable=SC2016
tr '\0' '\n' < "$work" \
  | xargs -d '\n' -P "$JOBS" -I{} bash -c 'IFS=$(printf "\t"); set -- $1; run_one "$1" "$2" "$3" "$4"' _ {} \
  >> "$OUT"

python3 "$here/lm_sweep.py" "$OUT"
