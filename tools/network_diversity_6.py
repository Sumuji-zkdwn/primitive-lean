#!/usr/bin/env python3
"""Independent finite checks for six-vertex information-network diversity.

Python 3.10+; standard library only. No access to primitive-lean is needed.
Run: python network_diversity_6.py > network_diversity_6_results.json
No repository files are changed.
"""
from collections import Counter, defaultdict, deque
from fractions import Fraction
from itertools import combinations, permutations
import json
import math

V = tuple(range(6))
U = tuple(combinations(V, 2))
A = ((0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (3, 5))
B = ((0, 2), (1, 2), (1, 3), (1, 4), (2, 4), (3, 5))
# Counterexample 1: same *vertex-wise* degrees, same long-edge count,
# but a different shortest-path distance distribution.
C = ((0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (2, 5))
D = ((0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3))
# Counterexample 2: same full distance histogram AND long-edge count,
# but a different Freeman degree centralization.
H = ((0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5))
I = ((0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5))
# Counterexample 3: same *vertex-wise* degrees and distance histogram,
# but a different count of spatial long edges at the SAME positions.
J = ((0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5))
K = ((0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 3))
R = ((0, 1), (1, 2), (3, 4), (4, 5))  # 2 components


def canon(edges):
    result = tuple(sorted(tuple(sorted(edge)) for edge in edges))
    assert len(set(result)) == len(result)
    assert all(edge in U for edge in result)
    return result


def neighbors(edges):
    ns = {v: set() for v in V}
    for u, v in canon(edges):
        ns[u].add(v)
        ns[v].add(u)
    return ns


def components(edges):
    ns = neighbors(edges)
    todo, parts = set(V), []
    while todo:
        start = min(todo)
        seen, queue = {start}, deque([start])
        while queue:
            for v in ns[queue.popleft()]:
                if v not in seen:
                    seen.add(v)
                    queue.append(v)
        parts.append(tuple(sorted(seen)))
        todo -= seen
    return tuple(parts)


def shortest_distances(edges):
    ns = neighbors(edges)
    results = {}
    for s in V:
        dist, queue = {s: 0}, deque([s])
        while queue:
            u = queue.popleft()
            for v in ns[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    queue.append(v)
        if len(dist) != len(V):
            return None
        for t in V:
            if s < t:
                results[(s, t)] = dist[t]
    return results


def entropy_from_counts(counts):
    total = sum(counts)
    return -sum((v / total) * math.log2(v / total) for v in counts if v)


def stats(edges, positions=V, threshold=3):
    edges = canon(edges)
    distances = shortest_distances(edges)
    if distances is None:
        return None
    ns = neighbors(edges)
    degree = tuple(len(ns[v]) for v in V)
    hist = tuple(Counter(distances.values()).get(i, 0) for i in range(1, 6))
    freeman = Fraction(sum(max(degree) - d for d in degree), (6 - 1) * (6 - 2))
    long_count = sum(abs(positions[u] - positions[v]) >= threshold for u, v in edges)
    triangle_count = sum(
        all(v in ns[u] for u, v in combinations(t, 2))
        for t in combinations(V, 3)
    )
    return {
        "edges": edges,
        "degree_per_vertex": degree,
        "degree_sequence": tuple(sorted(degree, reverse=True)),
        "degree_entropy_bits": entropy_from_counts(Counter(degree).values()),
        "freeman_centralization": str(freeman),
        "distance_sum": sum(distances.values()),
        "mean_distance": str(Fraction(sum(distances.values()), 15)),
        "distance_hist_1_to_5": hist,
        "distance_entropy_bits": entropy_from_counts(hist),
        "diameter": max(distances.values()),
        "triangle_count": triangle_count,
        "long_edges_ge_3": long_count,
        "total_spatial_length": sum(abs(positions[u] - positions[v]) for u, v in edges),
    }


def parity_edges(edges, x):
    return tuple(((x >> u) ^ (x >> v)) & 1 for u, v in canon(edges))


def fibers(edges):
    groups = defaultdict(list)
    for x in range(64):
        groups[parity_edges(edges, x)].append(x)
    return dict(groups)


def factors_through(groups, q):
    return all(len({q(x) for x in xs}) == 1 for xs in groups.values())


def induced_transition_exists(edges, update):
    groups = fibers(edges)
    return factors_through(groups, lambda x: parity_edges(edges, update(x)))


def measure_observation(states, observer):
    return len({observer(g) for g in states})


def run():
    a, b = stats(A), stats(B)
    assert a["degree_sequence"] == b["degree_sequence"] == (3, 3, 2, 2, 1, 1)
    assert a["distance_sum"] == 27 and b["distance_sum"] == 29
    assert a["diameter"] == 3 and b["diameter"] == 4
    assert a["distance_hist_1_to_5"] == (6, 6, 3, 0, 0)
    assert b["distance_hist_1_to_5"] == (6, 5, 3, 1, 0)
    assert a["freeman_centralization"] == b["freeman_centralization"] == "3/10"
    assert (a["triangle_count"], b["triangle_count"]) == (0, 1)
    assert (a["long_edges_ge_3"], b["long_edges_ge_3"]) == (2, 1)

    c, d, h, i, j, k = map(stats, (C, D, H, I, J, K))
    assert c["degree_per_vertex"] == d["degree_per_vertex"]
    assert c["long_edges_ge_3"] == d["long_edges_ge_3"] == 3
    assert (c["distance_sum"], d["distance_sum"]) == (27, 26)
    assert h["distance_hist_1_to_5"] == i["distance_hist_1_to_5"] == (6, 7, 2, 0, 0)
    assert h["long_edges_ge_3"] == i["long_edges_ge_3"] == 3
    assert (h["freeman_centralization"], i["freeman_centralization"]) == ("3/5", "3/10")
    assert j["degree_per_vertex"] == k["degree_per_vertex"]
    assert j["distance_hist_1_to_5"] == k["distance_hist_1_to_5"]
    assert (j["long_edges_ge_3"], k["long_edges_ge_3"]) == (3, 2)

    # Exhaust all labelled 6-vertex graphs with exactly six edges.
    six_edges_total = 0
    six_edges_connected = 0
    classes_degree_long = defaultdict(set)
    classes_distance_long = defaultdict(set)
    classes_degree_distance = defaultdict(set)
    for edges in combinations(U, 6):
        six_edges_total += 1
        row = stats(edges)
        if row is None:
            continue
        six_edges_connected += 1
        classes_degree_long[(row["degree_per_vertex"], row["long_edges_ge_3"])].add(row["distance_hist_1_to_5"])
        classes_distance_long[(row["distance_hist_1_to_5"], row["long_edges_ge_3"])].add(row["freeman_centralization"])
        classes_degree_distance[(row["degree_per_vertex"], row["distance_hist_1_to_5"])].add(row["long_edges_ge_3"])
    assert (six_edges_total, six_edges_connected) == (5005, 3660)
    count_degree_long_ambiguous = sum(len(v) > 1 for v in classes_degree_long.values())
    count_distance_long_ambiguous = sum(len(v) > 1 for v in classes_distance_long.values())
    count_degree_distance_ambiguous = sum(len(v) > 1 for v in classes_degree_distance.values())
    assert min(count_degree_long_ambiguous, count_distance_long_ambiguous,
               count_degree_distance_ambiguous) > 0

    # Same graph, different placements p:V -> {0,...,5}; topology unchanged.
    p_zero = (1, 4, 2, 3, 0, 5)
    p_all = (0, 1, 4, 5, 3, 2)
    assert (stats(A, p_zero)["long_edges_ge_3"], stats(A, p_all)["long_edges_ge_3"]) == (0, 6)
    distribution_placements = Counter(stats(A, p)["long_edges_ge_3"] for p in permutations(V))
    assert sum(distribution_placements.values()) == 720
    assert min(distribution_placements) == 0 and max(distribution_placements) == 6

    # A and B look alike under connectivity, and differ after deleting (0,2).
    remove02 = lambda edges: tuple(edge for edge in edges if edge != (0, 2))
    assert len(components(A)) == len(components(B)) == 1
    assert len(components(remove02(A))) == 1
    assert len(components(remove02(B))) == 2
    assert measure_observation((A, B), lambda g: len(components(g)) == 1) == 1
    assert measure_observation((A, B), lambda g: stats(g)["degree_sequence"]) == 1
    assert measure_observation((A, B), lambda g: len(components(remove02(g))) == 1) == 2
    assert measure_observation((A, B), lambda g: stats(g)["distance_hist_1_to_5"]) == 2

    # Node-to-edge information transformation: y_uv = x_u XOR x_v.
    aa, bb, rr = fibers(A), fibers(B), fibers(R)
    assert len(aa) == len(bb) == 32 and len(rr) == 16
    assert {len(xs) for xs in aa.values()} == {2}
    assert {len(xs) for xs in bb.values()} == {2}
    assert {len(xs) for xs in rr.values()} == {4}
    for g, cyc in ((A, ((0, 2), (1, 2), (1, 3), (0, 3))),
                   (B, ((1, 2), (1, 4), (2, 4)))):
        ce = canon(g)
        for obs in fibers(g):
            assert sum(obs[ce.index(e)] for e in cyc) % 2 == 0

    # Relative local information is recoverable if the vertices are connected.
    assert factors_through(aa, lambda x: ((x >> 0) ^ (x >> 5)) & 1)
    assert not factors_through(aa, lambda x: (x >> 0) & 1)
    assert not factors_through(rr, lambda x: ((x >> 2) ^ (x >> 3)) & 1)
    # Updates that are compatible/incompatible with the quotient.
    assert induced_transition_exists(A, lambda x: x ^ 1)   # flip bit 0
    assert not induced_transition_exists(A, lambda x: x & ~1)  # reset bit 0
    # Adding a within-component edge is predictable; a between-component edge is not.
    assert factors_through(aa, lambda x: ((x >> 0) ^ (x >> 1)) & 1)
    assert not factors_through(rr, lambda x: ((x >> 2) ^ (x >> 3)) & 1)

    summary = {
        "six_vertex_six_edge_enumeration": {
            "labelled_simple_graphs": six_edges_total,
            "connected_graphs": six_edges_connected,
            "fixed_labeled_degrees_and_long_edges_groups_with_variable_distance_histogram": count_degree_long_ambiguous,
            "fixed_distance_histogram_and_long_edges_groups_with_variable_hub_centralization": count_distance_long_ambiguous,
            "fixed_labeled_degrees_and_distance_histogram_groups_with_variable_long_edges": count_degree_distance_ambiguous,
        },
        "input_graphs": {"A": a, "B": b},
        "counterexamples": {
            "same_labeled_degrees_and_spatial_long_edges_but_different_distance": {"C": c, "D": d},
            "same_distance_histogram_and_long_edges_but_different_hub_centralization": {"H": h, "I": i},
            "same_labeled_degrees_and_distance_histogram_but_different_spatial_long_edges": {"J": j, "K": k},
        },
        "spatial_embedding": {
            "threshold": 3,
            "positions_default": V,
            "positions_zero_long_edges": p_zero,
            "positions_six_long_edges": p_all,
            "long_edge_counts_across_720_permutations": dict(sorted(distribution_placements.items())),
        },
        "observability_AB": {
            "connectivity_present": [True, True],
            "connectivity_after_delete_0_2": [True, False],
            "distinguishable_states_with_connectivity_only": 1,
            "distinguishable_states_with_connectivity_after_delete_0_2": 2,
        },
        "bit_to_edge_xor": {
            "connected_A": {"source_assignments": 64, "network_outputs": len(aa), "source_assignments_per_output": 2},
            "connected_B": {"source_assignments": 64, "network_outputs": len(bb), "source_assignments_per_output": 2},
            "two_component_R": {"source_assignments": 64, "network_outputs": len(rr), "source_assignments_per_output": 4},
            "relative_bit_0_xor_bit_5_recovers_from_A": True,
            "absolute_bit_0_recovers_from_A": False,
            "flip_bit_0_descends_to_edge_XOR": True,
            "reset_bit_0_descends_to_edge_XOR": False,
            "new_edge_within_one_component_predictable": True,
            "new_edge_across_two_components_predictable": False,
        },
        "status": "All executable assertions passed; no Lean proof claimed",
    }
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    run()
