"""Exhaustive observable relation pruning for tiny labelled undirected graphs.

The graph state, observation and action alphabet are deliberately independent.
For finite graphs, connects directly to shortest_cross_trace.shortest_word.
Only selected outputs and actions are preserved; no physical dynamics is inferred.

Example (from the repository root):
    python tools/relation_pruning.py --demo triangle
    python tools/relation_pruning.py --demo triangle --actions stay
    python tools/relation_pruning.py --demo triangle --actions delete:A-B
    python tools/relation_pruning.py --demo triangle --observe edge:A-B
"""

import argparse
from dataclasses import dataclass
from itertools import combinations
import json
from pathlib import Path

from shortest_cross_trace import Machine, shortest_word, verify_certificate


@dataclass(frozen=True)
class GraphSpace:
    vertices: tuple[str, ...]

    def __post_init__(self):
        if not 1 <= len(self.vertices) <= 4:
            raise ValueError("this exhaustive toy implementation supports 1..4 vertices")
        if len(set(self.vertices)) != len(self.vertices) or any(
            not name or any(c in name for c in ",-:") for name in self.vertices
        ):
            raise ValueError("vertex names must be distinct and exclude comma, colon, hyphen")

    @property
    def universe(self):
        return tuple(combinations(self.vertices, 2))

    def parse_edge(self, text):
        parts = text.split("-")
        if len(parts) != 2 or parts[0] == parts[1] or any(
            part not in self.vertices for part in parts
        ):
            raise ValueError(f"invalid edge: {text!r}")
        return tuple(sorted(parts, key=self.vertices.index))

    def edge_index(self, edge):
        return self.universe.index(edge)

    def bit(self, edge):
        return 1 << self.edge_index(edge)

    def to_mask(self, edges):
        mask = 0
        for edge in edges:
            bit = self.bit(edge)
            if mask & bit:
                raise ValueError(f"duplicate edge: {edge}")
            mask |= bit
        return mask

    def edges(self, mask):
        if type(mask) is not int or not 0 <= mask < (1 << len(self.universe)):
            raise ValueError("graph mask outside finite graph space")
        return tuple(e for i, e in enumerate(self.universe) if mask & (1 << i))

    def labels(self, mask):
        return ["-".join(edge) for edge in self.edges(mask)]

    def partition(self, mask):
        """Canonical connected components, including isolated vertices."""
        parent = {v: v for v in self.vertices}

        def root(v):
            while parent[v] != v:
                v = parent[v]
            return v

        for u, v in self.edges(mask):
            parent[root(v)] = root(u)
        comps = {}
        for vertex in self.vertices:
            comps.setdefault(root(vertex), []).append(vertex)
        return tuple(sorted((tuple(part) for part in comps.values()),
                            key=lambda part: self.vertices.index(part[0])))


@dataclass(frozen=True)
class Observation:
    kind: str
    pair: tuple[str, str] | None = None

    def value(self, space, mask):
        if self.kind == "components":
            return space.partition(mask)
        if self.kind == "connected":
            return len(space.partition(mask)) == 1
        if self.kind == "edge":
            return bool(mask & space.bit(self.pair))
        if self.kind == "reachable":
            return any(all(v in component for v in self.pair)
                       for component in space.partition(mask))
        raise ValueError(f"unknown observation: {self.kind}")

    @property
    def label(self):
        return self.kind if self.pair is None else f"{self.kind}:{'-'.join(self.pair)}"


def parse_observation(space, name):
    if name in ("connected", "components"):
        return Observation(name)
    if ":" in name:
        kind, edge = name.split(":", 1)
        if kind in ("edge", "reachable"):
            return Observation(kind, space.parse_edge(edge))
    raise ValueError(f"unsupported observation: {name!r}")


@dataclass(frozen=True)
class GraphAction:
    kind: str
    edge: tuple[str, str] | None = None

    @property
    def label(self):
        return "stay" if self.kind == "stay" else f"{self.kind}:{'-'.join(self.edge)}"

    def apply(self, space, mask):
        if self.kind == "stay":
            return mask
        bit = space.bit(self.edge)
        if self.kind == "delete":
            return mask & ~bit
        if self.kind == "add":
            return mask | bit
        raise ValueError(f"unknown action: {self.kind}")


def parse_actions(space, names):
    actions = []
    for raw in names:
        if raw == "stay":
            actions.append(GraphAction("stay"))
        elif ":" in raw:
            kind, raw_edge = raw.split(":", 1)
            if kind not in ("delete", "add"):
                raise ValueError(f"unknown action: {raw!r}")
            actions.append(GraphAction(kind, space.parse_edge(raw_edge)))
        else:
            raise ValueError(f"unknown action: {raw!r}")
    labels = [a.label for a in actions]
    if not labels or len(labels) != len(set(labels)):
        raise ValueError("actions must be nonempty and distinct")
    return tuple(actions)


def graph_machine(space, observation, actions):
    """One complete deterministic machine whose states are all graph masks."""
    states = range(1 << len(space.universe))
    return Machine(
        tuple(observation.value(space, mask) for mask in states),
        tuple(tuple(action.apply(space, mask) for mask in states)
              for action in actions),
    )


def curve_walk(space, mask):
    """One continuous labelled edge-covering walk, or None if disconnected.

    For Eulerian graphs no edge repeats. Otherwise DFS may double each edge.
    A labelled vertex sequence is an exact combinatorial edge encoding, not
    by itself a claim of a non-crossing planar embedding or physical identity.
    """
    if len(space.partition(mask)) != 1:
        return None
    edges = space.edges(mask)
    if not edges:
        return [space.vertices[0]]
    neighbors = {v: [] for v in space.vertices}
    for index, (u, v) in enumerate(edges):
        neighbors[u].append((v, index))
        neighbors[v].append((u, index))
    for v in neighbors:
        neighbors[v].sort(key=lambda pair: space.vertices.index(pair[0]))
    odd = [v for v in space.vertices if len(neighbors[v]) % 2]
    if len(odd) <= 2:
        start = odd[0] if odd else space.vertices[0]
        used = set()
        stack = [start]
        trail = []
        while stack:
            candidates = [(other, index) for other, index in neighbors[stack[-1]]
                          if index not in used]
            if candidates:
                other, index = candidates[0]
                used.add(index)
                stack.append(other)
            else:
                trail.append(stack.pop())
        assert len(used) == len(edges)
        return trail[::-1]

    # A connected non-Eulerian graph still has one edge-covering walk:
    # traverse each undirected edge out-and-back, at most 2|E| steps.
    seen = set()
    walk = [space.vertices[0]]

    def visit(v):
        for other, index in neighbors[v]:
            if index not in seen:
                seen.add(index)
                walk.append(other)
                visit(other)
                walk.append(v)

    visit(space.vertices[0])
    assert len(seen) == len(edges)
    return walk


def encode_edges(space, mask):
    """An injective operator word, assuming the known vertices and empty start."""
    return ["add:" + label for label in space.labels(mask)]


def analyze_pruning(space, original_mask, observation, actions):
    """Compare all subgraphs F⊆E against E for ALL selected action words."""
    machine = graph_machine(space, observation, actions)
    names = tuple(a.label for a in actions)
    candidates = []
    submask = original_mask
    while True:
        result = shortest_word(machine, machine, names, (original_mask, submask))
        if not verify_certificate(machine, machine, names, (original_mask, submask), result):
            raise AssertionError("cross-trace record failed independent certificate check")
        row = {
            "kept": space.labels(submask),
            "deleted": space.labels(original_mask & ~submask),
            "current_observation_preserved": machine.outputs[original_mask]
                                             == machine.outputs[submask],
            "all_action_words_preserved": result["status"] == "equivalent",
            "shortest_distinguishing_word": result["word"],
            "shortest_length": result.get("length"),
            "witness_trace": result.get("trace"),
            "certificate_verified": True,
            "curve_walk": curve_walk(space, submask),
            "exact_addition_word": encode_edges(space, submask),
        }
        candidates.append(row)
        if submask == 0:
            break
        submask = (submask - 1) & original_mask
    candidates.sort(key=lambda row: (len(row["deleted"]), row["deleted"]))
    equivalent = [c for c in candidates if c["all_action_words_preserved"]]
    best_size = min(len(c["kept"]) for c in equivalent)
    return {
        "vertices": list(space.vertices),
        "original": space.labels(original_mask),
        "observation": observation.label,
        "initial_observation": machine.outputs[original_mask],
        "allowed_actions": list(names),
        "candidate_count": len(candidates),
        "all_subsets_exhausted": True,
        "cross_trace_engine": "shortest_cross_trace.shortest_word",
        "minimum_retained_count": best_size,
        "minimum_retention": [c["kept"] for c in equivalent
                              if len(c["kept"]) == best_size],
        "candidates": candidates,
        "scope": "finite labelled simple undirected graphs; selected output/actions only",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--demo", choices=["triangle"], default="triangle")
    parser.add_argument("--vertices", default="A,B,C")
    parser.add_argument("--edges", default="A-B,A-C,B-C")
    parser.add_argument("--observe", default="connected")
    parser.add_argument("--actions", default="delete:A-B,delete:A-C,delete:B-C",
                        help="comma-separated; use 'stay' to test current observation only")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    space = GraphSpace(tuple(args.vertices.split(",")))
    edges = [space.parse_edge(s) for s in args.edges.split(",") if s]
    original = space.to_mask(edges)
    observation = parse_observation(space, args.observe)
    actions = parse_actions(space, args.actions.split(","))
    report = analyze_pruning(space, original, observation, actions)
    output = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
