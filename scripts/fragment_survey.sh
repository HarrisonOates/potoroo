#!/usr/bin/env bash
# Classifies how far Potoroo's front end gets on a benchmark corpus: one domain
# and its first problem per family, with a one-node search limit so the result
# reflects lowering rather than search.
#
#   scripts/fragment_survey.sh [benchmark-dir] [binary]
#
# The acceptance baseline for the IPC 2027 fragment work is that the only
# remaining failures are features outside the fragment (derived predicates).
set -u
BENCH="${1:-../downward-benchmarks}"
BIN="${2:-./target/release/potoroo}"

if [ ! -d "$BENCH" ]; then
  echo "no benchmark directory at $BENCH" >&2
  exit 2
fi
if [ ! -x "$BIN" ]; then
  echo "no planner binary at $BIN (cargo build --release)" >&2
  exit 2
fi

rows=$(
for dir in "$BENCH"/*/; do
  family=$(basename "$dir")
  domain=$(ls "$dir"/domain.pddl 2>/dev/null || ls "$dir"/*domain*.pddl 2>/dev/null | head -1)
  [ -z "$domain" ] && continue
  problem=$(ls "$dir"/*.pddl 2>/dev/null | grep -v -i domain | sort | head -1)
  [ -z "$problem" ] && continue
  out=$(timeout 10 "$BIN" -l 1 "$domain" "$problem" 2>&1 | head -1)
  case "$out" in
    ";"*)                        class="ok" ;;
    *"parse error"*)             class="parse-error" ;;
    *"unsupported requirement"*) class="requirement: ${out#*requirement: }" ;;
    *"action-cost"*)             class="action-cost: ${out#*expression: }" ;;
    *"fluent"*)                  class="fluent: ${out#*subset: }" ;;
    *)                           class="other: $out" ;;
  esac
  printf '%s\t%s\n' "$class" "$family"
done | sort
)

printf '%s\n' "$rows"
echo
echo "summary:"
printf '%s\n' "$rows" | cut -f1 | cut -c1-48 | sort | uniq -c | sort -rn
printf 'families surveyed: %s\n' "$(printf '%s\n' "$rows" | grep -c .)" 
