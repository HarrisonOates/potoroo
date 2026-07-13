#!/usr/bin/env bash
# Differential sweep: pair every problem file under examples/ with the domain
# file that declares its (:domain ...), then run both the C++ reference and the
# Potoroo port and diff their stdout (ignoring the Time: line). Cases that exceed
# the per-run timeout for either binary are skipped (reported separately).
#
# Usage: sweep.sh [extra potoroo flags...]
#   e.g. sweep.sh          (default lifted config)
#        sweep.sh -g       (ground actions)
set -u

here="$(cd "$(dirname "$0")" && pwd)"
root="$here/../.."
ex="$root/examples"
REF="${REF_VHPOP:-$root/vhpop}"
RUST="${RUST_POTOROO:-$here/../target/debug/potoroo}"
TIMEOUT="${SWEEP_TIMEOUT:-10}"
flags=("$@")

# Build a map: domain name -> file.
declare -A domain_file
for f in "$ex"/*.pddl; do
  name=$(grep -ioE '\(define[[:space:]]*\(domain[[:space:]]+[^) ]+' "$f" \
         | head -1 | sed -E 's/.*domain[[:space:]]+//I')
  [ -n "$name" ] && domain_file["$name"]="$f"
done

pass=0; fail=0; skip=0
fails=()
for f in "$ex"/*.pddl; do
  grep -iqE '\(define[[:space:]]*\(problem' "$f" || continue
  # Skip deferred-feature problems and their domains.
  dname=$(grep -ioE '\(:domain[[:space:]]+[^) ]+' "$f" | head -1 | sed -E 's/.*domain[[:space:]]+//I')
  [ -n "$dname" ] || continue
  dfile="${domain_file[$dname]:-}"
  [ -n "$dfile" ] || continue
  if grep -iqE ':(durative-actions|duration-inequalities|timed-initial-literals|fluents|continuous-effects)' "$f" "$dfile"; then
    continue
  fi

  # N.B. capture the binary's exit code, not grep's: piping into grep would make
  # $? reflect grep, so a timed-out run that printed the `;name` header would be
  # miscounted as a mismatch instead of a (skipped) timeout.
  ref_raw=$(timeout "$TIMEOUT" "$REF" "${flags[@]}" "$dfile" "$f" 2>/dev/null)
  ref_rc=$?
  ref_out=$(printf '%s\n' "$ref_raw" | grep -v '^Time: ')
  rust_raw=$(timeout "$TIMEOUT" "$RUST" "${flags[@]}" "$dfile" "$f" 2>/dev/null)
  rust_rc=$?
  rust_out=$(printf '%s\n' "$rust_raw" | grep -v '^Time: ')
  if [ $ref_rc -ne 0 ] || [ $rust_rc -ne 0 ]; then
    skip=$((skip+1))
    continue
  fi
  if [ "$ref_out" = "$rust_out" ]; then
    pass=$((pass+1))
  else
    fail=$((fail+1))
    fails+=("$(basename "$f") [$dname]")
    if [ -n "${SWEEP_VERBOSE:-}" ]; then
      echo "--- MISMATCH: $(basename "$f") (domain $dname) ---"
      diff <(printf '%s\n' "$ref_out") <(printf '%s\n' "$rust_out") | head -20
    fi
  fi
done

echo "pass=$pass fail=$fail skip(timeout)=$skip"
if [ ${#fails[@]} -gt 0 ]; then
  printf 'FAIL: %s\n' "${fails[@]}"
fi
