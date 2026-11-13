#!/usr/bin/env python3
"""Check complete paired runs and summarize the native RePOP investigation."""
import csv
import hashlib
import json
import tarfile
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
binary_hash = None
records = []
sources = {}
frozen = HERE / "repop-frozen.json"
archived_sources = None
if frozen.exists():
    saved = json.loads(frozen.read_text())
    archive = ROOT / saved["source_archive"]
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == saved["source_archive_sha256"]
    with tarfile.open(archive) as stream:
        archived_sources = {m.name: stream.extractfile(m).read() for m in stream if m.isfile()}
for suite, expected in [("main", 56), ("controls", 21), ("extended", 4)]:
    prefix = "repop" if suite == "main" else f"repop-{suite}"
    path = HERE / f"{prefix}.csv"
    rows = list(csv.DictReader(path.open()))
    assert len(rows) == expected, (suite, len(rows), expected)
    assert len({r["label"] for r in rows}) == len(rows)
    provenance = json.loads((HERE / f"{prefix}-provenance.json").read_text())
    if binary_hash is None:
        binary_hash = provenance["binary_sha256"]
    assert binary_hash == provenance["binary_sha256"]
    for name, digest in provenance["source_hashes"].items():
        content = archived_sources[name] if archived_sources is not None else (ROOT / name).read_bytes()
        assert hashlib.sha256(content).hexdigest() == digest, name
    metadata = json.loads((HERE / f"{prefix}.manifest.json").read_text())
    assert set(metadata["hashes"].values()) == {binary_hash}
    for r in rows:
        assert r["binary_sha256"] == binary_hash
        assert r["outcome"] in {"solved", "limit", "timeout", "memory"}, r
        assert r["stats_source"] == "final", r
        assert int(r["node_limit"]) == (2000000 if suite == "extended" else 200000)
        assert int(r["planner_seconds"]) == (60 if suite == "extended" else 10)
        assert int(r["memory_mb"]) == (2048 if suite == "extended" else 1024)
        if r["label"].endswith("_ce"):
            assert r["h2_status"] == "complete", r
        case = f"{r['family']}-{r['problem']}"
        profile = r["label"].removeprefix(case + "-")
        records.append(dict(suite=suite, case=case, profile=profile,
                            solved=r["outcome"] == "solved", outcome=r["outcome"],
                            generated=int(r["nodes_generated"]), visited=int(r["nodes_visited"]),
                            cost=int(r["plan_cost"]) if r["outcome"] == "solved" else None,
                            wall_ms=int(r["wall_ms"]), h2_status=r["h2_status"]))
    for suffix in [".csv", ".manifest.json", "-provenance.json", "-manifest.json"]:
        p = HERE / f"{prefix}{suffix}"
        sources[p.name] = hashlib.sha256(p.read_bytes()).hexdigest()
    logs = ROOT / "target/relax-investigation" / prefix
    for p in sorted(logs.glob("*")):
        sources[str(p.relative_to(ROOT))] = hashlib.sha256(p.read_bytes()).hexdigest()

counts = defaultdict(Counter)
for r in records:
    if r["suite"] != "extended" and not r["case"].startswith("parcprinter"):
        counts[r["profile"]]["solved"] += r["solved"]
        counts[r["profile"]]["attempted"] += 1
assert all(v["attempted"] == 6 for v in counts.values())
result = dict(binary_sha256=binary_hash, run_count=len(records),
              target_count=6, solved_counts={k: dict(v) for k, v in counts.items()},
              records=records, artifact_hashes=sources)
(HERE / "repop-summary.json").write_text(json.dumps(result, indent=2) + "\n")
for k, v in counts.items():
    print(k, dict(v))
print("Extended:", [r for r in records if r["suite"] == "extended"])
