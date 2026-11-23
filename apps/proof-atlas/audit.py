#!/usr/bin/env python3
"""Audit every displayed theorem statement against actual Lean source files.

This is source-provenance testing, NOT Lean typechecking or proof synthesis.
The canonical proof-term dependency evidence is already audited separately
by games/primitive-foundry/check_dag.py.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "apps" / "proof-atlas"


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> None:
    graph = load(BASE / "graph.json")
    original = load(ROOT / "games/primitive-foundry/tech.json")
    sources = load(BASE / "proofs.json")
    explain = load(BASE / "narratives.json")
    assert graph == original, "DAG must not be rewritten by the atlas"
    assert graph["summary"]["nodes"] == len(graph["nodes"]) == 465
    assert graph["summary"]["proofEdges"] == 629
    assert len(sources["records"]) == 465
    assert set(explain["narratives"]) <= {n["name"] for n in graph["nodes"]}
    expected_parts = [
        *(f"elastica-{i}.json" for i in range(4)),
        *(f"linearinput-{i}.json" for i in range(6)),
    ]
    fragments = {}
    for name in expected_parts:
        batch = load(BASE / "data" / name)
        for item in batch["records"]:
            assert item["id"] not in fragments
            fragments[item["id"]] = item
    assert len(fragments) == 465
    proof_edges, lines, annotated, comments = 0, set(), 0, 0
    file_cache = {}
    for idx, (node, recorded) in enumerate(zip(graph["nodes"], sources["records"])):
        assert node["id"] == recorded["id"] == idx
        assert recorded == fragments[idx]
        assert recorded["statement"] and recorded["proof"], node["name"]
        if node["file"] not in file_cache:
            file_cache[node["file"]] = (ROOT / node["file"]).read_text(encoding="utf-8")
        text = file_cache[node["file"]]
        original_lines = text.splitlines()
        line = recorded["line"]
        assert 1 <= line <= len(original_lines)
        short = node["name"].split(".")[-1]
        assert re.search(r"\b(theorem|lemma)\s+" + re.escape(short) + r"\b", original_lines[line - 1]), (
            "theorem mismatched source line", idx, line, node["name"]
        )
        # The visible statement and the proof excerpt must come from this file.
        # Line endings are normalized for direct substring checking.
        assert recorded["statement"] in text, ("non-source proposition", idx)
        assert recorded["proof"] in text, ("non-source proof", idx)
        lines.add((node["file"], line))
        proof_edges += len(node["parents"])
        comments += bool(recorded.get("comment"))
        if node["name"] in explain["narratives"]:
            annotation = explain["narratives"][node["name"]]
            assert annotation["summary"] and annotation["steps"] and annotation["assumptions"]
            annotated += 1
    assert proof_edges == 629
    assert annotated == 22
    assert comments == 340
    assert len(file_cache) == 60
    print("ATLAS_SOURCE_AUDIT_PASS", json.dumps({
        "theorems": 465, "source_files": len(file_cache), "proof_edges": proof_edges,
        "propositions_and_proofs": len(lines), "author_comments": comments,
        "reviewed_japanese_argument_sketches": annotated
    }, ensure_ascii=False))


if __name__ == "__main__":
    main()
