#!/usr/bin/env python3
"""Validate recorded FF runs against final logs, inputs, source and manifests."""
import csv
import hashlib
import json
import re
import shlex
import tarfile
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


records, hashes = [], {}
binary_hash = None
frozen = json.loads((HERE / "ff-ties-frozen.json").read_text()) if (HERE / "ff-ties-frozen.json").exists() else None
archived_sources = None
if frozen:
    archive = ROOT / frozen["source_archive"]
    assert digest(archive) == frozen["source_archive_sha256"]
    with tarfile.open(archive) as stream:
        archived_sources = {m.name: stream.extractfile(m).read() for m in stream if m.isfile()}
for prefix, expected in [("ff-ties", 21), ("ff-ties-vhpop-domains", 9)]:
    provenance = json.loads((HERE / f"{prefix}-provenance.json").read_text())
    binary_hash = binary_hash or provenance["binary_sha256"]
    assert provenance["binary_sha256"] == binary_hash
    assert digest(HERE / "compiled_ties_probe.py") == provenance["probe_sha256"]
    assert digest(HERE / "ff_capture_translate.py") == provenance["wrapper_sha256"]
    assert digest(ROOT.parent / "potoroo-cluster/scripts/potoroo/pocl_probe.py") == provenance["harness_sha256"]
    for name, value in provenance["translator_hashes"].items():
        assert digest(Path(provenance["translator_root"]) / name) == value
    assert digest(ROOT / (frozen["binary"] if frozen else "target/release/potoroo")) == binary_hash
    for name, value in provenance["source_hashes"].items():
        content = archived_sources[name] if archived_sources is not None else (ROOT / name).read_bytes()
        assert hashlib.sha256(content).hexdigest() == value, name
    metadata = json.loads((HERE / f"{prefix}.manifest.json").read_text())
    assert set(metadata["hashes"].values()) == {binary_hash}
    assert (metadata["seconds"], metadata["memory_mb"], metadata["node_limit"]) == (15, 1024, "200000")
    rows = list(csv.DictReader((HERE / f"{prefix}.csv").open()))
    assert len(rows) == expected
    assert len({r["label"] for r in rows}) == expected
    evidence = {(c["domain"], c["instance"]): c for c in provenance["cases"]}
    sas_dir = ROOT / "target/relax-investigation" / f"{prefix}-sas"
    captures = [json.loads(p.read_text()) for p in sorted(sas_dir.glob("invocation-*.json"))]
    assert len(captures) == expected
    case_sas = defaultdict(set)
    canonical_inputs = defaultdict(set)
    for r, run, capture in zip(rows, metadata["runs"], captures, strict=True):
        assert r["label"] == run["label"]
        command = [run["binary"], *run["args"], "-v", "--time-limit", "10",
                   "--stage-mem-mb", "1024", "-l", "200000", run["domain"], run["problem"]]
        assert shlex.split(r["command"]) == command
        assert r["binary_sha256"] == binary_hash
        assert (r["node_limit"], r["planner_seconds"], r["memory_mb"]) == ("200000", "10", "1024")
        assert r["stats_source"] == "final"
        assert r["outcome"] in {"solved", "limit", "timeout", "memory"}
        case = f"{r['family']}-{r['problem']}"
        ev = evidence[r["family"], r["problem"]]
        assert digest(Path(run["domain"])) == ev["domain_sha256"]
        assert digest(Path(run["problem"])) == ev["problem_sha256"]
        # FDR translation serializes the parsed model into normalized PDDL;
        # these hashes need not equal the original benchmark text hashes.
        canonical_inputs[case].add((capture["domain_sha256"], capture["problem_sha256"]))
        assert digest(sas_dir / capture["sas_file"]) == capture["sas_sha256"]
        case_sas[case].add(capture["sas_sha256"])
        stem = ROOT / "target/relax-investigation" / prefix / f"{int(r['run']):03d}-{r['label']}"
        err = stem.with_suffix(".err").read_text()
        stats = json.loads(re.search(r"^STATS (.+)$", err, re.MULTILINE)[1])
        for key in ["outcome", "nodes_generated", "nodes_visited", "plan_cost", "wall_ms", "h_evals", "h_eval_ms"]:
            assert str(stats[key]) == r[key], (r["label"], key)
        for suffix in [".err", ".out", ".time"]:
            p = stem.with_suffix(suffix)
            hashes[str(p.relative_to(ROOT))] = digest(p)
        is_preferred = "--preferred" in run["args"]
        assert (stats["preferred_generated"] > 0) == is_preferred
        assert (stats["preferred_selected"] > 0) == is_preferred
        assert stats["preferred_selected"] <= stats["preferred_generated"] <= stats["nodes_generated"]
        records.append(dict(suite=prefix, case=case, profile=r["label"].removeprefix(case + "-"),
                            solved=r["outcome"] == "solved", outcome=r["outcome"],
                            generated=int(r["nodes_generated"]), visited=int(r["nodes_visited"]),
                            preferred_generated=stats["preferred_generated"], preferred_selected=stats["preferred_selected"],
                            cost=int(r["plan_cost"]) if r["outcome"] == "solved" else None,
                            wall_ms=int(r["wall_ms"]), h_eval_ms=int(r["h_eval_ms"])))
    assert all(len(hashes) == 1 for hashes in case_sas.values()), case_sas
    assert all(len(inputs) == 1 for inputs in canonical_inputs.values()), canonical_inputs
    for p in sorted(sas_dir.iterdir()):
        hashes[str(p.relative_to(ROOT))] = digest(p)
    for suffix in [".csv", ".manifest.json", "-manifest.json", "-provenance.json"]:
        p = HERE / f"{prefix}{suffix}"
        hashes[str(p.relative_to(ROOT))] = digest(p)

counts = defaultdict(Counter)
for r in records:
    if r["suite"] == "ff-ties" and not r["case"].startswith("parcprinter"):
        counts[r["profile"]]["attempted"] += 1
        counts[r["profile"]]["solved"] += r["solved"]
assert all(c["attempted"] == 6 for c in counts.values())
result = dict(binary_sha256=binary_hash, run_count=len(records), target_count=6,
              solved_counts={p: dict(c) for p, c in counts.items()}, records=records,
              artifact_hashes=hashes)
summary = HERE / "ff-ties-summary.json"
if summary.exists():
    assert json.loads(summary.read_text()) == result, "recorded summary or artifact hashes changed"
summary.write_text(json.dumps(result, indent=2) + "\n")
for profile, count in counts.items():
    print(profile, dict(count))
print("Parcprinter:", [r for r in records if r["case"].startswith("parcprinter")])
