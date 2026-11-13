#!/usr/bin/env python3
"""Validate recorded FF runs against final logs, inputs, source and manifests."""
import csv
import hashlib
import json
import re
import tarfile
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


records, hashes = [], {}
binary_hash = None
frozen = json.loads((HERE / "ff-frozen.json").read_text()) if (HERE / "ff-frozen.json").exists() else None
archived_sources = None
if frozen:
    archive = ROOT / frozen["source_archive"]
    assert digest(archive) == frozen["source_archive_sha256"]
    with tarfile.open(archive) as stream:
        archived_sources = {m.name: stream.extractfile(m).read() for m in stream if m.isfile()}
for prefix, expected in [("ff", 63), ("ff-vhpop-domains", 27)]:
    provenance = json.loads((HERE / f"{prefix}-provenance.json").read_text())
    binary_hash = binary_hash or provenance["binary_sha256"]
    assert provenance["binary_sha256"] == binary_hash
    assert digest(ROOT / (frozen["binary"] if frozen else "target/release/potoroo")) == binary_hash
    for name, value in provenance["source_hashes"].items():
        content = archived_sources[name] if archived_sources is not None else (ROOT / name).read_bytes()
        assert hashlib.sha256(content).hexdigest() == value, name
    metadata = json.loads((HERE / f"{prefix}.manifest.json").read_text())
    assert set(metadata["hashes"].values()) == {binary_hash}
    rows = list(csv.DictReader((HERE / f"{prefix}.csv").open()))
    assert len(rows) == expected
    assert len({r["label"] for r in rows}) == expected
    evidence = {(c["domain"], c["instance"]): c for c in provenance["cases"]}
    for r, run in zip(rows, metadata["runs"], strict=True):
        assert r["label"] == run["label"]
        assert r["binary_sha256"] == binary_hash
        assert (r["node_limit"], r["planner_seconds"], r["memory_mb"]) == ("200000", "10", "1024")
        assert r["stats_source"] == "final"
        assert r["outcome"] in {"solved", "limit", "timeout", "memory"}
        case = f"{r['family']}-{r['problem']}"
        ev = evidence[r["family"], r["problem"]]
        assert digest(Path(run["domain"])) == ev["domain_sha256"]
        assert digest(Path(run["problem"])) == ev["problem_sha256"]
        stem = ROOT / "target/relax-investigation" / prefix / f"{int(r['run']):03d}-{r['label']}"
        err = stem.with_suffix(".err").read_text()
        stats = json.loads(re.search(r"^STATS (.+)$", err, re.MULTILINE)[1])
        for key in ["outcome", "nodes_generated", "nodes_visited", "plan_cost", "wall_ms", "h_evals", "h_eval_ms"]:
            assert str(stats[key]) == r[key], (r["label"], key)
        for suffix in [".err", ".out", ".time"]:
            p = stem.with_suffix(suffix)
            hashes[str(p.relative_to(ROOT))] = digest(p)
        records.append(dict(suite=prefix, case=case, profile=r["label"].removeprefix(case + "-"),
                            solved=r["outcome"] == "solved", outcome=r["outcome"],
                            generated=int(r["nodes_generated"]), visited=int(r["nodes_visited"]),
                            cost=int(r["plan_cost"]) if r["outcome"] == "solved" else None,
                            wall_ms=int(r["wall_ms"]), h_eval_ms=int(r["h_eval_ms"])))
    for suffix in [".csv", ".manifest.json", "-manifest.json", "-provenance.json"]:
        p = HERE / f"{prefix}{suffix}"
        hashes[str(p.relative_to(ROOT))] = digest(p)

counts = defaultdict(Counter)
for r in records:
    if r["suite"] == "ff" and not r["case"].startswith("parcprinter"):
        counts[r["profile"]]["attempted"] += 1
        counts[r["profile"]]["solved"] += r["solved"]
assert all(c["attempted"] == 6 for c in counts.values())
result = dict(binary_sha256=binary_hash, run_count=len(records), target_count=6,
              solved_counts={p: dict(c) for p, c in counts.items()}, records=records,
              artifact_hashes=hashes)
(HERE / "ff-summary.json").write_text(json.dumps(result, indent=2) + "\n")
for profile, count in counts.items():
    print(profile, dict(count))
print("Parcprinter:", [r for r in records if r["case"].startswith("parcprinter")])
