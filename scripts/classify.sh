#!/usr/bin/env bash
# Classify sweep mismatches: for each problem given as an argument, report
# whether the Rust port found a plan with the same number of steps as the C++
# reference (TIEBREAK — acceptable) or something genuinely different.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
root="$here/../.."
ex="$root/examples"
REF="${REF_VHPOP:-$root/vhpop}"
RUST="${RUST_VHPOP:-$here/../target/release/vhpop}"
T="${TIMEOUT:-60}"

declare -A domain_file
for f in "$ex"/*.pddl; do
  name=$(grep -ioE '\(define[[:space:]]*\(domain[[:space:]]+[^) ]+' "$f" \
         | head -1 | sed -E 's/.*domain[[:space:]]+//I')
  [ -n "$name" ] && domain_file["$name"]="$f"
done

for p in "$@"; do
  f="$ex/$p"
  dname=$(grep -ioE '\(:domain[[:space:]]+[^) ]+' "$f" | head -1 | sed -E 's/.*domain[[:space:]]+//I')
  dfile="${domain_file[$dname]:-MISSING}"
  r=$(timeout "$T" "$REF"  "$dfile" "$f" 2>/dev/null | grep -v '^Time:')
  u=$(timeout "$T" "$RUST" "$dfile" "$f" 2>/dev/null | grep -v '^Time:')
  rc=$(printf '%s\n' "$r" | grep -cE '^[0-9]+:')
  uc=$(printf '%s\n' "$u" | grep -cE '^[0-9]+:')
  if [ "$r" = "$u" ]; then
    tag="MATCH"
  elif printf '%s\n' "$u" | grep -q 'no plan'; then
    tag="RUST-NOPLAN  (ref steps=$rc)"
  elif [ "$uc" -eq 0 ]; then
    tag="RUST-NO-OUTPUT (dfile=$dfile)"
  elif [ "$rc" != "$uc" ]; then
    tag="STEPCOUNT  ref=$rc rust=$uc"
  else
    tag="TIEBREAK   (both=$rc steps)"
  fi
  printf '%-26s %s\n' "$p" "$tag"
done
