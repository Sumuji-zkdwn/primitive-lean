#!/usr/bin/env python3
"""Lossless reachability projection of strong source edges, not proof compression.

Inputs are immutable *content* of the saved graph snapshot; this tool never
mixes its edges with the current worktree or live GitHub PR metadata.
"""
from __future__ import annotations

import argparse
import hashlib
import heapq
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
GRAPH = ROOT / "docs/dependency/generated/graph.json"
OUTPUT = ROOT / "docs/compression/source-reachability.json"
STRONG = frozenset({"exact_import", "qualified_reference"})


def reach_from(adjacency: dict[str, set[str]], start: str) -> set[str]:
    seen: set[str] = set()
    stack = list(adjacency[start])
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        stack.extend(adjacency[current] - seen)
    return seen


def compress_graph(graph: dict, raw: bytes) -> dict:
    """Return a transitive reduction if the *strong* source graph is a DAG.

    A -> B means A lexically references/imports B. We preserve reachable pairs,
    NOT the identity or necessity of the removed direct references.
    """
    nodes = sorted(n["id"] for n in graph["nodes"])
    if len(set(nodes)) != len(nodes):
        raise ValueError("duplicate source node ID")
    adjacency: dict[str, set[str]] = {n: set() for n in nodes}
    indegree = dict.fromkeys(nodes, 0)
    pairs: set[tuple[str, str]] = set()
    eligible_edges = 0
    for edge in graph["edges"]:
        if edge["kind"] not in STRONG:
            continue
        eligible_edges += 1
        a, b = edge["from"], edge["to"]
        if a not in adjacency or b not in adjacency:
            raise ValueError("strong source edge has unknown endpoint")
        if a == b:
            raise ValueError("self-edge in strong source graph")
        pairs.add((a, b))
    for a, b in pairs:
        adjacency[a].add(b)
        indegree[b] += 1

    # Deterministic topological order. Refuse cycles rather than misreport a
    # DAG reduction for a graph with mutually reachable source components.
    ready = [n for n in nodes if indegree[n] == 0]
    heapq.heapify(ready)
    order: list[str] = []
    while ready:
        a = heapq.heappop(ready)
        order.append(a)
        for b in sorted(adjacency[a]):
            indegree[b] -= 1
            if indegree[b] == 0:
                heapq.heappush(ready, b)
    if len(order) != len(nodes):
        raise ValueError("strong source graph contains a directed cycle")

    # For each node, visit immediate targets in topological order: any
    # alternative multi-hop path must begin with a *prior* target.
    rank = {n: i for i, n in enumerate(order)}
    closure: dict[str, set[str]] = {}
    retained: set[tuple[str, str]] = set()
    for a in reversed(order):
        seen: set[str] = set()
        for b in sorted(adjacency[a], key=rank.__getitem__):
            if b not in seen:
                retained.add((a, b))
            seen.add(b)
            seen.update(closure[b])
        closure[a] = seen

    reduced = {n: set() for n in nodes}
    for a, b in retained:
        reduced[a].add(b)
    for a in nodes:
        if reach_from(reduced, a) != closure[a]:
            raise AssertionError("transitive reduction changed reachability")

    return {
        "schema_version": 1,
        "semantics": "strong lexical source reachability only; not Lean proof implication",
        "source": {
            "graph_sha256": hashlib.sha256(raw).hexdigest(),
            "main_commit": graph["main_commit"],
            "pr_snapshot": graph["pr_snapshot"],
        },
        "source_link_kinds": sorted(STRONG),
        "counts": {
            "nodes": len(nodes),
            "all_source_edges": len(graph["edges"]),
            "eligible_direct_edges": eligible_edges,
            "unique_eligible_pairs": len(pairs),
            "retained_pairs": len(retained),
            "transitive_pairs_removed": len(pairs) - len(retained),
            "weak_edges_excluded": len(graph["edges"]) - eligible_edges,
        },
        "nodes": nodes,
        "edges": [list(pair) for pair in sorted(retained)],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, default=GRAPH)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true",
                        help="fail unless the stored reduced view matches the graph")
    args = parser.parse_args()
    raw = args.graph.read_bytes()
    view = compress_graph(json.loads(raw), raw)
    encoded = (json.dumps(view, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()
    if args.check:
        if not args.output.is_file() or args.output.read_bytes() != encoded:
            print("Outdated source reachability snapshot: " + str(args.output),
                  file=sys.stderr)
            return 1
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(encoded)
    c = view["counts"]
    print(f"strong source pairs: {c['unique_eligible_pairs']} -> "
          f"{c['retained_pairs']} (removed {c['transitive_pairs_removed']})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
