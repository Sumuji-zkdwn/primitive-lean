#!/usr/bin/env python3
"""Verify every theorem-level dependency edge against retained proof-term data.

Input A: original 465-theorem joint verification inventory.
Input B: kernel-accepted constant-reference snapshot (deps.json).
Output: validated 465-node graph with 629 direct theorem proof references.
Importantly: proof-term *occurrence* does not prove a dependency is necessary.
"""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
G = ROOT / "games/primitive-foundry/tech.json"
C = ROOT / "games/rogue465/theorems.json"
D = ROOT / "docs/dependency/data/deps.json"
B = ROOT / "evidence/local/2026-10-30-f0/joint.json"
U = ROOT / "games/primitive-foundry/upgrades.json"


def main() -> int:
    graph = json.loads(G.read_text(encoding="utf-8"))
    base = json.loads(C.read_text(encoding="utf-8"))
    deps = json.loads(D.read_text(encoding="utf-8"))
    joint = json.loads(B.read_text(encoding="utf-8"))
    engineering = json.loads(U.read_text(encoding="utf-8"))

    expected = [
        *[x for x in joint["parent_declarations"] if x["kind"] == "theorem"],
        *[x for x in joint["declarations"] if x["kind"] == "theorem"],
    ]
    assert len(expected) == 465
    assert joint["parent_theorem_count"] == 214
    assert joint["theorem_count"] == 251
    assert len(base["cards"]) == len(graph["nodes"]) == 465
    assert graph["schema"] == 2
    assert graph["kernelReferences"] == "docs/dependency/data/deps.json"
    assert graph["provenance"]["baselineBlobSha"] == base["source_blob_sha"]
    assert graph["provenance"]["dependencyInputs"] == deps["inputs"]

    byname = {x["name"]: i for i, x in enumerate(expected)}
    assert len(byname) == 465
    counts = Counter()
    visiting, visited = set(), set()
    nodes = graph["nodes"]
    for i, (original, card, node) in enumerate(zip(expected, base["cards"], nodes)):
        assert original["name"] == card["name"] == node["name"]
        assert node["id"] == i and card["id"] == i
        assert node["school"] == card["school"]
        assert node["file"] == card["file"] and node["line"] == card["line"]
        assert node["label"] and node["label"] != node["name"]
        source = deps["nodes"][node["name"]]
        assert source["kind"] == "theorem" and source["layer"] == "initial"
        original_parents = sorted({byname[name] for name in source["direct"]["proof"]
                                   if name in byname})
        other = sorted({name for name in source["direct"]["proof"] if name not in byname})
        assert node["parents"] == original_parents, ("invalid theorem dependency", i)
        assert node["otherProjectRefs"] == other, ("lost auxiliary reference", i)
        assert node["statementRefs"] == sorted({name for name in source["direct"]["statement"]
                                                  if name not in byname})
        for ref in other:
            kind = deps["nodes"][ref]["kind"]
            assert kind in ("def", "theorem")
            counts["other_" + kind] += 1
        counts["edges"] += len(node["parents"])
        counts["roots"] += not bool(node["parents"])
        counts["school_" + node["school"]] += 1
        assert Path(ROOT / node["file"]).is_file(), ("missing original theorem source", node["file"])

    def depth(i: int) -> int:
        if i in visited:
            return nodes[i]["depth"]
        assert i not in visiting, ("proof dependency cycle", i)
        visiting.add(i)
        computed = 1 + max(depth(p) for p in nodes[i]["parents"]) if nodes[i]["parents"] else 0
        assert nodes[i]["depth"] == computed, ("incorrect topo layer", i)
        visiting.remove(i)
        visited.add(i)
        return computed

    max_depth = max(depth(i) for i in range(465))
    assert len(visited) == 465
    assert counts == {
        "other_def": 783,
        "other_theorem": 9,
        "edges": 629,
        "roots": 146,
        "school_Elastica": 214,
        "school_LinearInput": 251,
    }, counts
    assert graph["summary"]["nodes"] == 465
    assert graph["summary"]["proofEdges"] == 629
    assert graph["summary"]["roots"] == 146
    assert graph["summary"]["maxDepth"] == max_depth == 12
    assert graph["summary"]["otherDeclarationReferences"] == 783
    assert graph["summary"]["auxiliaryTheoremReferences"] == 9
    assert sum(graph["summary"]["depthCounts"].values()) == 465

    # Game upgrades are *separate* from theorem nodes; their gates point to
    # actual baseline theorems rather than unrelated or invented references.
    gates = [u["gateProof"] for u in engineering["nodes"] if "gateProof" in u]
    assert len(gates) >= 6
    assert all(g in byname for g in gates)
    assert len({u["id"] for u in engineering["nodes"]}) == len(engineering["nodes"]) == 10

    print("FOUNDARY_465_DAG_OK", json.dumps({
        "theorems": 465, "proof_edges": 629, "other_def_refs": 783,
        "auxiliary_theorem_refs": 9, "root_theorems": 146,
        "max_depth": 12, "upgrade_gates": len(gates)
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
