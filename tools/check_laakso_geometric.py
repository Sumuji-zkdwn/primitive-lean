"""Exact rational instance checks for the ternary Laakso bonding formula.

The finite graph builder is shared with check_laakso_finite.  The point normal
form, bonding map, section and checks below are independent of the Lean proofs.
Only edge endpoints are identified with vertices; labelled parallel edge
interiors stay distinct.  Passing samples do not prove continuity, a path
metric statement, an inverse-limit theorem, or a metric-measure theorem.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import json

from check_laakso_finite import refine


ROOT = Path(__file__).resolve().parents[1]
FINE_PARAMETERS = tuple(map(Q, ("0", "1/7", "1/3", "1/2", "2/3", "6/7", "1")))
COARSE_PARAMETERS = tuple(map(Q, ("0", "1/9", "1/6", "1/3", "2/5", "1/2",
                                  "2/3", "5/6", "8/9", "1")))


def vertex_point(vertex):
    return ("vertex", vertex)


def edge_point(edges, edge, parameter):
    """Normal form for a closed-edge representative; edge IDs are essential."""
    assert 0 <= edge < len(edges) and Q(0) <= parameter <= Q(1)
    if parameter == 0:
        return vertex_point(edges[edge][0])
    if parameter == 1:
        return vertex_point(edges[edge][1])
    return ("edge", edge, parameter)


def point_height(heights, edges, point):
    if point[0] == "vertex":
        return heights[point[1]]
    _, edge, parameter = point
    left, right = edges[edge]
    return heights[left] + parameter * (heights[right] - heights[left])


def vertex_image(heights, edges, vertex):
    """Old sheet vertices go to vertices; new thirds go to edge interiors."""
    old_copies = 2 * len(heights)
    assert 0 <= vertex < old_copies + 2 * len(edges)
    if vertex < old_copies:
        return vertex_point(vertex // 2)
    edge, third = divmod(vertex - old_copies, 2)
    return edge_point(edges, edge, Q(third + 1, 3))


def edge_image(edges, fine_edge, parameter):
    edge, local_edge = divmod(fine_edge, 6)
    _, third = divmod(local_edge, 3)
    return edge_point(edges, edge, (third + parameter) / 3)


def point_image(heights, edges, point):
    if point[0] == "vertex":
        return vertex_image(heights, edges, point[1])
    return edge_image(edges, point[1], point[2])


def section(fine_edges, point, sheet=0):
    """A rational point of the chosen sheet; boundary choices normalize."""
    assert sheet in (0, 1)
    if point[0] == "vertex":
        return vertex_point(2 * point[1] + sheet)
    _, edge, parameter = point
    third = min(int(3 * parameter), 2)
    return edge_point(fine_edges, 6 * edge + 3 * sheet + third,
                      3 * parameter - third)


def describe(point):
    return [str(part) if isinstance(part, Q) else part for part in point]


def check_level(n, heights, edges):
    fine_heights, fine_edges = refine(heights, edges)
    coarse_length, fine_length = Q(1, 3**n), Q(1, 3**(n + 1))
    assert len(fine_edges) == 6 * len(edges)
    assert len(fine_heights) == 2 * len(heights) + 2 * len(edges)
    endpoint_checks = edge_sample_checks = length_checks = 0

    # Check every closed-edge endpoint against the independent vertex formula.
    for fine_edge, (left, right) in enumerate(fine_edges):
        for parameter, vertex in ((Q(0), left), (Q(1), right)):
            image = edge_image(edges, fine_edge, parameter)
            assert image == vertex_image(heights, edges, vertex)
            assert image == point_image(heights, edges,
                                        edge_point(fine_edges, fine_edge, parameter))
            endpoint_checks += 1
        for parameter in FINE_PARAMETERS:
            point = edge_point(fine_edges, fine_edge, parameter)
            image = point_image(heights, edges, point)
            assert image == edge_image(edges, fine_edge, parameter)
            assert point_height(fine_heights, fine_edges, point) == point_height(heights, edges, image)
            edge_sample_checks += 1
        third = fine_edge % 3
        for left_parameter, right_parameter in combinations(FINE_PARAMETERS, 2):
            mapped_left = (third + left_parameter) / 3
            mapped_right = (third + right_parameter) / 3
            assert fine_length * abs(right_parameter - left_parameter) == coarse_length * abs(mapped_right - mapped_left)
            length_checks += 1

    for vertex, height in enumerate(fine_heights):
        assert height == point_height(heights, edges, vertex_image(heights, edges, vertex))

    # Use each labelled coarse edge, including its endpoints and both thirds.
    # Also check every coarse vertex independently of any incident edge.
    targets = {vertex_point(v) for v in range(len(heights))}
    targets.update(edge_point(edges, edge, parameter)
                   for edge in range(len(edges)) for parameter in COARSE_PARAMETERS)
    fiber_sizes = defaultdict(int)
    for point in targets:
        lifts = {section(fine_edges, point, sheet) for sheet in (0, 1)}
        for lift in lifts:
            assert point_image(heights, edges, lift) == point
        is_new_third = point[0] == "edge" and point[2] in (Q(1, 3), Q(2, 3))
        assert len(lifts) == (1 if is_new_third else 2)

        # Enumerate all possible representatives over this target exactly.
        # Fine vertices are checked globally; edge-interior candidates solve
        # (third + parameter)/3 = target_parameter with 0 < parameter < 1.
        candidates = {vertex_point(v) for v in range(len(fine_heights))
                      if vertex_image(heights, edges, v) == point}
        if point[0] == "edge":
            _, edge, parameter = point
            for third in range(3):
                fine_parameter = 3 * parameter - third
                if 0 < fine_parameter < 1:
                    candidates.update(edge_point(fine_edges, 6 * edge + 3 * sheet + third,
                                                 fine_parameter) for sheet in (0, 1))
        assert candidates == lifts
        fiber_sizes[str(len(lifts))] += 1

    noninjective_checks = 0
    for edge in range(len(edges)):
        left = edge_point(fine_edges, 6 * edge, Q(1, 2))
        right = edge_point(fine_edges, 6 * edge + 3, Q(1, 2))
        assert left != right
        assert point_image(heights, edges, left) == point_image(heights, edges, right)
        noninjective_checks += 1

    # Mutation: forgetting the third-offset disagrees at a shared endpoint.
    mutant_edge, mutant_parameter = 1, Q(0)
    mutant_image = edge_point(edges, mutant_edge // 6, mutant_parameter / 3)
    expected_image = edge_image(edges, mutant_edge, mutant_parameter)
    fine_endpoint = edge_point(fine_edges, mutant_edge, mutant_parameter)
    assert mutant_image != expected_image
    assert point_height(heights, edges, mutant_image) != point_height(fine_heights, fine_edges, fine_endpoint)
    mutations = [dict(name="forgotten_third_offset", rejected=True,
                      fine_edge=mutant_edge, parameter=str(mutant_parameter),
                      expected=describe(expected_image), mutated=describe(mutant_image))]

    # Mutation: treating endpoint pairs as edge IDs collapses distinct points.
    by_endpoints = defaultdict(list)
    for edge, endpoints in enumerate(edges):
        by_endpoints[endpoints].append(edge)
    parallel_groups = [group for group in by_endpoints.values() if len(group) > 1]
    if parallel_groups:
        a, b = parallel_groups[0][:2]
        point_a, point_b = edge_point(edges, a, Q(1, 2)), edge_point(edges, b, Q(1, 2))
        assert point_a != point_b
        representatives = {edge: group[0] for group in by_endpoints.values() for edge in group}
        mutated_a = edge_point(edges, representatives[a], Q(1, 2))
        mutated_b = edge_point(edges, representatives[b], Q(1, 2))
        assert mutated_a == mutated_b
        collapsed_edges = list(by_endpoints)
        collapsed_heights, collapsed_fine_edges = refine(heights, collapsed_edges)
        assert len(collapsed_fine_edges) != len(fine_edges)
        assert len(collapsed_heights) != len(fine_heights)
        mutations.append(dict(name="early_parallel_edge_collapse", rejected=True,
                              distinct_edge_ids=[a, b], distinct_points=[describe(point_a), describe(point_b)],
                              mutated_common_point=describe(mutated_a),
                              expected_refined_edges=len(fine_edges),
                              mutated_refined_edges=len(collapsed_fine_edges)))

    row = dict(coarse_level=n, fine_level=n + 1,
               coarse_vertices=len(heights), coarse_edges=len(edges),
               fine_vertices=len(fine_heights), fine_edges=len(fine_edges),
               coarse_edge_length=str(coarse_length), fine_edge_length=str(fine_length),
               endpoint_compatibility_checks=endpoint_checks,
               vertex_height_checks=len(fine_heights),
               edge_point_height_checks=edge_sample_checks,
               scaled_edge_parameter_length_checks=length_checks,
               distinct_surjectivity_targets=len(targets), sampled_fiber_sizes=dict(sorted(fiber_sizes.items())),
               noninjective_sheet_pairs=noninjective_checks,
               labelled_parallel_edge_groups=len(parallel_groups), mutation_controls=mutations)
    return row, fine_heights, fine_edges


def check():
    heights, edges = [Q(0), Q(1)], [(0, 1)]
    levels = []
    for n in range(4):
        row, heights, edges = check_level(n, heights, edges)
        levels.append(row)
    mutation_count = sum(len(row["mutation_controls"]) for row in levels)
    assert mutation_count == 7
    return dict(passed=True,
                scope="Exact finite rational checks for bondings from levels 1..4 to 0..3; samples do not prove continuity, global path-metric claims, inverse-limit or metric-measure results",
                point_equality="Vertex identity at endpoints; labelled edge ID and rational parameter in interiors",
                fine_parameters=list(map(str, FINE_PARAMETERS)),
                coarse_parameters=list(map(str, COARSE_PARAMETERS)),
                graph_levels=levels, mutation_controls_rejected=mutation_count)


if __name__ == "__main__":
    result = check()
    result["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    builder = Path(__file__).with_name("check_laakso_finite.py")
    result["graph_builder_sha256"] = hashlib.sha256(builder.read_bytes()).hexdigest()
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    (out / "laakso-geometric.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
