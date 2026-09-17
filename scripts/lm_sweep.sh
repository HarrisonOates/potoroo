#!/usr/bin/env bash
# Coverage sweep over a benchmark corpus (downward-benchmarks by default).
#
#   scripts/lm_sweep.sh [OPTIONS]
#     -b DIR      benchmark root, one directory per domain family
#                 (default: ../downward-benchmarks)
#     -c CSV      configurations to compare, as [MODE:]HEURISTIC[+PRUNE-RULES][@SEARCH]
#                 (default: ADD,RELAX,LM,LMF,LMFO)
#                 MODE is lifted (default), g (-g) or fdr (--fdr-pocl);
#                 SEARCH is a -s value; several rules are joined with `+`.
#                 e.g. ADD, ADD+cutset, fdr:ADD@ALT, g:ADD,
#                 fdr:LMCUT+cutset+edelete+disjunctive
#     -t SECS     per-run wall timeout (default 60)
#     -n N        problems per family, smallest first (default 5)
#     -j N        concurrent runs (default 4)
#     -m MB       per-run address-space cap (default 4096)
#     -o FILE     result CSV (default sweep-results.csv)
#     -x FLAGS    extra planner flags applied to every configuration,
#                 e.g. -x "--mem-mb 600" for a run under -m 768
#     -r          resume: keep the rows already in the result CSV and run
#                 only the (family, problem, config) triples it lacks
#
# Writes one CSV row per (family, problem, config) and prints a per-family and
# per-config coverage table. Runs are capped in both time and address space, so
# a run that blows up is recorded as unsolved rather than taking the machine
# down with it — and the `outcome` column says which of the two it was, since a
# planner that dies of memory at 4s and one that runs out of time at 60s need
# different fixes.
set -u

BENCH="../downward-benchmarks"
CONFIGS="ADD,RELAX,LM,LMF,LMFO"
TIMEOUT=60
PER_FAMILY=5
JOBS=4
MEM_MB=4096
OUT="sweep-results.csv"
EXTRA=""
RESUME=0

while getopts "b:c:t:n:j:m:o:x:r" opt; do
  case "$opt" in
    b) BENCH="$OPTARG" ;;
    c) CONFIGS="$OPTARG" ;;
    t) TIMEOUT="$OPTARG" ;;
    n) PER_FAMILY="$OPTARG" ;;
    j) JOBS="$OPTARG" ;;
    m) MEM_MB="$OPTARG" ;;
    o) OUT="$OPTARG" ;;
    x) EXTRA="$OPTARG" ;;
    r) RESUME=1 ;;
    *) sed -n '2,28p' "$0" >&2; exit 2 ;;
  esac
done

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/.." && pwd)"
BIN="${POTOROO_BIN:-$root/target/release/potoroo}"

[ -d "$BENCH" ] || { echo "no benchmark directory at $BENCH" >&2; exit 2; }
[ -x "$BIN" ]   || { echo "no planner binary at $BIN (cargo build --release)" >&2; exit 2; }

# The ground representations need Fast Downward; default to the in-repo
# checkout so a run never silently falls back to naive grounding and measures a
# different task.
if [ -z "${POTOROO_FD:-}" ] && [ -x "$root/downward/fast-downward.py" ]; then
  export POTOROO_FD="$root/downward/fast-downward.py"
fi
if [ -z "${POTOROO_DOWNWARD:-}" ]; then
  dw="$(ls "$root"/downward/builds/*/bin/downward 2>/dev/null | head -1 || true)"
  [ -n "$dw" ] && export POTOROO_DOWNWARD="$dw"
fi

# One run, printing a CSV row. Kept as a function so xargs can call it.
#
# The row is assembled in a variable and written with a single `printf`: several
# runs append to the same file at once, and one write per row is what keeps them
# from interleaving into a row that parses as neither.
run_one() {
  family="$1"; domain="$2"; problem="$3"; config="$4"
  name="$(basename "$problem" .pddl)"
  # A configuration is [MODE:]HEURISTIC[+RULES][@SEARCH].
  cfg="$config"; mode="lifted"; search=""
  case "$cfg" in *:*) mode="${cfg%%:*}"; cfg="${cfg#*:}" ;; esac
  case "$cfg" in *@*) search="${cfg##*@}"; cfg="${cfg%@*}" ;; esac
  heuristic="${cfg%%+*}"
  if [ "$heuristic" = "$cfg" ]; then prune="none"; else prune="${cfg#*+}"; prune="${prune//+/,}"; fi
  # Built as an array: the xargs wrapper below sets IFS to a tab, so a
  # space-separated "-s ALT" in a string would reach the planner as one word.
  args=()
  case "$mode" in
    lifted) ;;
    g) args+=(-g) ;;
    fdr) args+=(--fdr-pocl) ;;
    *) printf '%s,%s,%s,0,0,0,0,badconfig,0,0\n' "$family" "$name" "$config"; return ;;
  esac
  [ -n "$search" ] && args+=(-s "$search")
  # shellcheck disable=SC2206
  [ -n "$EXTRA" ] && args+=($EXTRA)
  err="$(mktemp)"
  # `-v` costs one progress line a second and is what lets a run that dies of
  # memory still report how many nodes it had generated.
  (
    ulimit -v $((MEM_MB * 1024)) 2>/dev/null
    POTOROO_STATS_JSON=1 timeout "$TIMEOUT" "$BIN" "${args[@]}" -v -h "$heuristic" -p "$prune" \
      "$domain" "$problem" >/dev/null 2>"$err"
  ) 2>/dev/null
  code=$?
  stats="$(grep '^STATS ' "$err" | head -1)"
  if [ -n "$stats" ]; then
    measured="$(
      printf '%s\n' "${stats#STATS }" | python3 -c '
import json, sys
d = json.load(sys.stdin)
print("%d,%d,%d,%d,%s,%d,%d" % (1 if d.get("solved") else 0, d.get("plan_len", 0),
                                d.get("nodes_generated", 0), d.get("wall_ms", 0),
                                d.get("outcome", "solved" if d.get("solved") else "noplan"),
                                d.get("peak_rss_kb", 0), d.get("max_queued", 0)))'
    )"
  else
    # No STATS line: the process was killed or crashed before it could report.
    # `timeout` exits 124; an allocation failure aborts (134) after printing
    # the message the Rust runtime uses; anything else is a crash or a
    # front-end rejection, both worth telling apart from search failures.
    # Node and queue counts come from the last progress line; a run killed
    # for memory had the whole address-space cap resident, so that is its
    # peak RSS to within the last second's growth.
    rss=0
    if [ "$code" -eq 124 ]; then outcome="timeout"
    elif grep -q 'memory allocation' "$err"; then outcome="oom"; rss=$((MEM_MB * 1024))
    elif [ "$code" -eq 134 ] || [ "$code" -eq 137 ]; then outcome="oom"; rss=$((MEM_MB * 1024))
    else outcome="error"
    fi
    last="$(grep 'generated [0-9]* | queued' "$err" | tail -1)"
    nodes="$(printf '%s' "$last" | sed -n 's/.*generated \([0-9]*\).*/\1/p')"
    queued="$(printf '%s' "$last" | sed -n 's/.*queued \([0-9]*\).*/\1/p')"
    measured="0,0,${nodes:-0},$((TIMEOUT * 1000)),$outcome,$rss,${queued:-0}"
  fi
  rm -f "$err"
  printf '%s,%s,%s,%s\n' "$family" "$name" "$config" "$measured"
}
export -f run_one
export BIN TIMEOUT MEM_MB EXTRA

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
    # Families like `airport` ship one domain per problem alongside it, under
    # one of several naming schemes (`p01-domain.pddl` for `p01-airport1-p1`,
    # `domain_p20_1.pddl` for `p20_1`, `domain-p04.pddl` for `p04`); the rest
    # share a single `domain.pddl`. A wrong match is a front-end error that
    # looks like a failure of the planner, so try every scheme before falling
    # back to any domain file at all.
    stem="$(basename "$problem" .pddl)"
    prefix="${stem%%-*}"
    domain=""
    for candidate in "$dir/$stem-domain.pddl" "$dir/domain_$stem.pddl" "$dir/domain-$stem.pddl" \
                     "$dir/$prefix-domain.pddl" "$dir/domain_$prefix.pddl" "$dir/domain-$prefix.pddl" \
                     "$dir/domain.pddl"; do
      if [ -f "$candidate" ]; then domain="$candidate"; break; fi
    done
    [ -n "$domain" ] || domain="$(ls "$dir"/*domain*.pddl 2>/dev/null | head -1)"
    [ -f "$domain" ] || continue
    for config in "${configs[@]}"; do
      printf '%s\t%s\t%s\t%s\0' "$family" "$domain" "$problem" "$config" >> "$work"
    done
  done
done

# Resuming: drop every triple the result file already has a row for. A sweep
# is hours of machine time, and being killed part-way should not cost it.
if [ "$RESUME" -eq 1 ] && [ -f "$OUT" ]; then
  done_keys="$(mktemp)"
  awk -F, 'NR > 1 { print $1 "\t" $2 "\t" $3 }' "$OUT" > "$done_keys"
  remaining="$(mktemp)"
  tr '\0' '\n' < "$work" | awk -F'\t' -v keys="$done_keys" '
    BEGIN { while ((getline line < keys) > 0) done[line] = 1 }
    { name = $3; sub(/.*\//, "", name); sub(/\.pddl$/, "", name)
      if (!(($1 "\t" name "\t" $4) in done)) print }' | tr '\n' '\0' > "$remaining"
  mv "$remaining" "$work"
  rm -f "$done_keys"
else
  echo "family,problem,config,solved,cost,nodes,ms,outcome,rss_kb,max_queued" > "$OUT"
fi

total="$(tr -dc '\0' < "$work" | wc -c)"
echo "running $total planner invocations, $JOBS at a time" >&2

# shellcheck disable=SC2016
tr '\0' '\n' < "$work" \
  | xargs -d '\n' -P "$JOBS" -I{} bash -c 'IFS=$(printf "\t"); set -- $1; run_one "$1" "$2" "$3" "$4"' _ {} \
  >> "$OUT"

python3 "$here/lm_sweep.py" "$OUT"
