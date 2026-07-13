#!/usr/bin/env bash
# Differential test helper: run the C++ reference vhpop and the Potoroo port on the
# same inputs/flags and diff their stdout (ignoring the nondeterministic
# "Time:" line). Exit 0 if identical.
#
# Usage: diff.sh <domain.pddl> <problem.pddl> [potoroo flags...]
#
# Env:
#   REF_VHPOP      path to the C++ reference binary (default: ../../vhpop)
#   RUST_POTOROO   path to the Potoroo binary (default: ../target/debug/potoroo)
set -u

here="$(cd "$(dirname "$0")" && pwd)"
REF_VHPOP="${REF_VHPOP:-$here/../../vhpop}"
RUST_POTOROO="${RUST_POTOROO:-$here/../target/debug/potoroo}"

domain="$1"; problem="$2"; shift 2
flags=("$@")

strip() { grep -v '^Time: '; }

ref_out="$("$REF_VHPOP" "${flags[@]}" "$domain" "$problem" 2>/dev/null | strip)"
rust_out="$("$RUST_POTOROO" "${flags[@]}" "$domain" "$problem" 2>/dev/null | strip)"

if [ "$ref_out" = "$rust_out" ]; then
  exit 0
else
  echo "MISMATCH: $domain $problem ${flags[*]}"
  diff <(printf '%s\n' "$ref_out") <(printf '%s\n' "$rust_out")
  exit 1
fi
