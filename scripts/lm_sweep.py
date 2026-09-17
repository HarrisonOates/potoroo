#!/usr/bin/env python3
"""Tabulates a sweep CSV from lm_sweep.sh: coverage per configuration, overall
and per domain family, plus the families where the configurations disagree."""

import collections
import csv
import sys


def main(path: str) -> None:
    raw = list(csv.DictReader(open(path)))
    # Runs append concurrently, so a truncated or interleaved row is possible;
    # drop it loudly rather than let it become a phantom configuration.
    rows = [r for r in raw if r.get("solved") in ("0", "1") and r.get("config")]
    dropped = len(raw) - len(rows)
    if dropped:
        print(f"warning: dropped {dropped} malformed row(s)\n")
    if not rows:
        print("no rows")
        return
    configs = sorted({row["config"] for row in rows}, key=lambda c: (len(c), c))
    solved = collections.defaultdict(set)
    attempted = set()
    for row in rows:
        key = (row["family"], row["problem"])
        attempted.add(key)
        if row["solved"] == "1":
            solved[row["config"]].add(key)

    width = max(len(c) for c in configs)
    print(f"{len(attempted)} problems, {len(configs)} configurations\n")
    print("coverage")
    for config in configs:
        n = len(solved[config])
        print(f"  {config:<{width}}  {n:4d} / {len(attempted)}  ({100 * n / len(attempted):.1f}%)")

    families = sorted({family for family, _ in attempted})
    disagreeing = []
    for family in families:
        here = {p for f, p in attempted if f == family}
        counts = [len({p for f, p in solved[c] if f == family}) for c in configs]
        if len(set(counts)) > 1:
            disagreeing.append((family, len(here), counts))

    if not disagreeing:
        print("\nno family separates the configurations")
        return
    print(f"\nfamilies where coverage differs ({len(disagreeing)} of {len(families)})")
    header = "  " + "family".ljust(28) + "n".rjust(4)
    for config in configs:
        header += config.rjust(width + 2)
    print(header)
    for family, n, counts in sorted(disagreeing, key=lambda r: -max(r[2]) + min(r[2])):
        line = "  " + family[:28].ljust(28) + str(n).rjust(4)
        for count in counts:
            line += str(count).rjust(width + 2)
        print(line)

    # Problems only one configuration gets: the coverage each one uniquely buys.
    print("\nuniquely solved")
    for config in configs:
        others = set().union(*(solved[c] for c in configs if c != config)) if len(configs) > 1 else set()
        unique = sorted(solved[config] - others)
        print(f"  {config:<{width}}  {len(unique):3d}" + ("  " + ", ".join(f"{f}/{p}" for f, p in unique[:6]) if unique else ""))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "sweep-results.csv")
