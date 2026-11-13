"""Finite diagnostics for the binary, j=3 Laakso graph approximation.

Construction: Cheeger--Kleiner, Example 1.4, laaksoplus.pdf.
Parallel edges are retained. This is not a proof about the infinite limit,
nor an identification with the existing triangular-panel model.
"""
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json


def refine(heights, edges):
    new_heights = []
    old_copies = {}
    for vertex, height in enumerate(heights):
        for sheet in (0, 1):
            old_copies[vertex, sheet] = len(new_heights)
            new_heights.append(height)
    new_edges = []
    for left, right in edges:
        shared = []
        for numerator in (1, 2):
            shared.append(len(new_heights))
            new_heights.append(
                heights[left] + Q(numerator, 3) * (heights[right] - heights[left])
            )
        for sheet in (0, 1):
            chain = [old_copies[left, sheet], *shared, old_copies[right, sheet]]
            new_edges.extend(zip(chain, chain[1:]))
    return new_heights, new_edges


def graph_record(level, heights, edges):
    degree = Counter(vertex for edge in edges for vertex in edge)
    histogram = Counter(degree.values())
    assert set(degree) == set(range(len(heights)))
    assert set(histogram) <= {1, 4}
    assert len(edges) == 6**level
    assert histogram[1] == 2 ** (level + 1)
    if level:
        assert len(heights) == 2 ** (level - 1) * (3**level + 3)
    assert all(heights[b] - heights[a] == Q(1, 3**level) for a, b in edges)
    neighbors = {vertex: [] for vertex in range(len(heights))}
    for left, right in edges:
        neighbors[left].append(right)
        neighbors[right].append(left)
    seen, pending = {0}, [0]
    while pending:
        for adjacent in neighbors[pending.pop()]:
            if adjacent not in seen:
                seen.add(adjacent)
                pending.append(adjacent)
    assert len(seen) == len(heights)
    return {
        "level": level,
        "vertices": len(heights),
        "edges": len(edges),
        "degree_counts": dict(sorted(histogram.items())),
        "cycle_rank": len(edges) - len(heights) + 1,
        "edge_length": str(Q(1, 3**level)),
    }


def signature_level_two(increments):
    displacement = [Q(0), Q(0)]
    tensor = [[Q(0), Q(0)], [Q(0), Q(0)]]
    for vector in increments:
        for i in range(2):
            for j in range(2):
                tensor[i][j] += displacement[i] * vector[j] + vector[i] * vector[j] / 2
        displacement = [displacement[i] + vector[i] for i in range(2)]
    return displacement, (tensor[0][1] - tensor[1][0]) / 2


def relay(samples):
    state = 0
    for sample in samples:
        if sample >= Q(1, 12):
            state = 1
        elif sample <= -Q(1, 12):
            state = 0
    return state


if __name__ == "__main__":
    heights, edges = [Q(0), Q(1)], [(0, 1)]
    levels = []
    for level in range(5):
        levels.append(graph_record(level, heights, edges))
        if level < 4:
            heights, edges = refine(heights, edges)
    # F1 parallel edges between heights 1/3 and 2/3.
    # Continuous observation f is zero at endpoints, +/-1/6 at midpoint.
    up = [(Q(1, 6), Q(1, 6)), (Q(1, 6), -Q(1, 6))]
    down = [(Q(1, 6), -Q(1, 6)), (Q(1, 6), Q(1, 6))]
    displacement_up, area_up = signature_level_two(up)
    displacement_down, area_down = signature_level_two(down)
    assert displacement_up == displacement_down == [Q(1, 3), Q(0)]
    assert area_up == -Q(1, 36) and area_down == Q(1, 36)
    assert relay([0, Q(1, 6), 0]) == 1
    assert relay([0, -Q(1, 6), 0]) == 0
    source = Path(__file__).resolve()
    report = {
        "scope": "Finite graph topology and exact two-route observation example only.",
        "script_sha256": sha256(source.read_bytes()).hexdigest(),
        "construction": "trisect, duplicate, identify only newly inserted vertices",
        "levels": levels,
        "two_routes": {
            "same_geometric_start_and_end": True,
            "common_first_level": list(map(str, displacement_up)),
            "log_signature_area_coefficients": [str(area_up), str(area_down)],
            "relay_initial_state": 0,
            "relay_thresholds": {"on": "1/12", "off": "-1/12"},
            "terminal_relay_states": [1, 0],
        },
    }
    source.with_name("laakso_connection_checks.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, ensure_ascii=False, indent=2))
