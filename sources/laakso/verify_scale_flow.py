"""Exact finite diagnostics for quartic gradient flows on Laakso graphs.

This file does not implement the reinterpreter or prove an infinite-limit
theorem. All arithmetic uses fractions.Fraction, including sparse polynomial
identities and the invariant row-space closure computation.
"""
from collections import deque
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json
import sys

sys.dont_write_bytecode = True
from verify_laakso_connection import refine


def clean(poly):
    return {powers: Q(value) for powers, value in poly.items() if value}


def variable(index, count):
    powers = [0] * count
    powers[index] = 1
    return {tuple(powers): Q(1)}


def add(*polys):
    answer = {}
    for poly in polys:
        for powers, value in poly.items():
            answer[powers] = answer.get(powers, Q(0)) + value
    return clean(answer)


def scale(poly, coefficient):
    return clean({powers: Q(coefficient) * value for powers, value in poly.items()})


def multiply(left, right):
    answer = {}
    for powers_a, a in left.items():
        for powers_b, b in right.items():
            powers = tuple(i + j for i, j in zip(powers_a, powers_b))
            answer[powers] = answer.get(powers, Q(0)) + a * b
    return clean(answer)


def reaction(poly):
    return add(scale(poly, 3), scale(multiply(multiply(poly, poly), poly), -4))


def evaluate(poly, values):
    answer = Q(0)
    for powers, coefficient in poly.items():
        term = coefficient
        for value, power in zip(values, powers):
            term *= Q(value) ** power
        answer += term
    return answer


def polynomial_record(poly, names):
    return {
        "variables": names,
        "terms": [
            {"powers": list(powers), "coefficient": str(value)}
            for powers, value in sorted(poly.items())
        ],
    }


def polynomial_flow(values, edges, coupling, masses=None, conductances=None):
    masses = [Q(1)] * len(values) if masses is None else list(map(Q, masses))
    conductances = (
        [Q(1)] * len(edges)
        if conductances is None
        else list(map(Q, conductances))
    )
    laplacian = [{} for _ in values]
    for (left, right), conductance in zip(edges, conductances):
        difference = add(values[left], scale(values[right], -1))
        laplacian[left] = add(laplacian[left], scale(difference, conductance))
        laplacian[right] = add(laplacian[right], scale(difference, -conductance))
    return [
        add(reaction(value), scale(multiply(coupling, lap), -1 / mass))
        for value, lap, mass in zip(values, laplacian, masses)
    ]


def laplacian_matrix(count, edges):
    matrix = [[Q(0) for _ in range(count)] for _ in range(count)]
    for left, right in edges:
        matrix[left][left] += 1
        matrix[right][right] += 1
        matrix[left][right] -= 1
        matrix[right][left] -= 1
    return matrix


def right_multiply(row, matrix):
    answer = [Q(0)] * len(row)
    for i, coefficient in enumerate(row):
        if coefficient:
            for j, entry in enumerate(matrix[i]):
                if entry:
                    answer[j] += coefficient * entry
    return tuple(answer)


class RationalRowSpace:
    def __init__(self, width):
        self.width = width
        self.rows = {}

    def reduce(self, row):
        row = list(map(Q, row))
        for pivot, basis_row in sorted(self.rows.items()):
            factor = row[pivot]
            if factor:
                row = [a - factor * b for a, b in zip(row, basis_row)]
        return row

    def insert(self, row):
        row = self.reduce(row)
        pivot = next((i for i, entry in enumerate(row) if entry), None)
        if pivot is None:
            return None
        divisor = row[pivot]
        row = tuple(entry / divisor for entry in row)
        self.rows[pivot] = row
        return row

    def contains(self, row):
        return not any(self.reduce(row))


def coefficient_images(row, constant):
    yield right_multiply(row, constant)
    for i, entry in enumerate(row):
        if entry:
            image = [Q(0)] * len(row)
            image[i] = -12 * entry
            yield tuple(image)


def closure_record(level, coarse_count, heights, edges, coupling):
    count = len(heights)
    laplacian = laplacian_matrix(count, edges)
    constant = [
        [Q(3 if i == j else 0) - coupling * laplacian[i][j] for j in range(count)]
        for i in range(count)
    ]
    space = RationalRowSpace(count)
    pending = deque()
    for vertex in range(coarse_count):
        row = [Q(0)] * count
        row[2 * vertex] = row[2 * vertex + 1] = Q(1, 2)
        inserted = space.insert(row)
        assert inserted is not None
        pending.append(inserted)
    initial_rank = len(space.rows)
    processed = 0
    while pending:
        row = pending.popleft()
        processed += 1
        for image in coefficient_images(row, constant):
            inserted = space.insert(image)
            if inserted is not None:
                pending.append(inserted)
    for row in space.rows.values():
        assert all(space.contains(image) for image in coefficient_images(row, constant))
    expected = count if coupling else 2 * coarse_count
    assert len(space.rows) == expected
    return {
        "fine_level": level,
        "fine_vertices": count,
        "fine_edges_including_parallel_edges": len(edges),
        "coarse_vertices": coarse_count,
        "coupling_lambda": str(coupling),
        "initial_projection_rank": initial_rank,
        "closed_row_space_rank": len(space.rows),
        "expected_rank": expected,
        "processed_independent_rows": processed,
        "closure_invariance_rechecked": True,
        "coefficient_matrices": "3I-lambda L and -12 E_ii for every fine vertex i",
        "projection": "pair mean of the two copies of each old vertex; new vertices ignored",
    }


def main():
    h0, e0 = [Q(0), Q(1)], [(0, 1)]
    h1, e1 = refine(h0, e0)
    h2, e2 = refine(h1, e1)
    assert len(h1) == 6 and len(e1) == 6
    assert len(h2) == 24 and len(e2) == 36
    assert h1 == [Q(0), Q(0), Q(1), Q(1), Q(1, 3), Q(2, 3)]

    m, d, coupling = [variable(i, 3) for i in range(3)]
    perturbed = [add(m, d), add(m, scale(d, -1)), m, m, m, m]
    fine_flow = polynomial_flow(perturbed, e1, coupling)
    projected_flow = [
        scale(add(fine_flow[0], fine_flow[1]), Q(1, 2)),
        scale(add(fine_flow[2], fine_flow[3]), Q(1, 2)),
    ]
    coarse_flow = polynomial_flow([m, m], e0, coupling)
    residual = [add(a, scale(b, -1)) for a, b in zip(projected_flow, coarse_flow)]
    expected_residual = scale(multiply(m, multiply(d, d)), -12)
    assert residual == [expected_residual, {}]
    assert all(powers[2] == 0 for powers in residual[0])
    uniform = [m] * 6
    uniform_flow = polynomial_flow(uniform, e1, coupling)
    assert scale(add(uniform_flow[0], uniform_flow[1]), Q(1, 2)) == coarse_flow[0]
    assert scale(add(uniform_flow[2], uniform_flow[3]), Q(1, 2)) == coarse_flow[1]
    numeric_values = [Q(1, 2), Q(1, 4), Q(7)]
    assert evaluate(projected_flow[0], numeric_values) == Q(5, 8)
    assert evaluate(coarse_flow[0], numeric_values) == Q(1)
    assert evaluate(residual[0], numeric_values) == -Q(3, 8)

    q = [variable(i, 5) for i in range(4)]
    symbolic_coupling = variable(4, 5)
    lift_indices = [0, 0, 1, 1, 2, 3]
    lifted = [q[i] for i in lift_indices]
    lifted_flow = polynomial_flow(lifted, e1, symbolic_coupling)
    quotient_edges = [(0, 2), (2, 3), (3, 1)]
    masses = [Q(2), Q(2), Q(1), Q(1)]
    conductances = [Q(2)] * 3
    quotient_flow = polynomial_flow(
        q, quotient_edges, symbolic_coupling, masses, conductances
    )
    assert lifted_flow == [quotient_flow[i] for i in lift_indices]
    # The restriction is to a synchronized invariant subspace, not arbitrary
    # states with the same pair averages.
    assert lifted_flow[0] == lifted_flow[1]
    assert lifted_flow[2] == lifted_flow[3]

    closures = []
    for level, coarse_count, heights, edges in (
        (1, len(h0), h1, e1),
        (2, len(h1), h2, e2),
    ):
        for value in (Q(0), Q(1)):
            closures.append(closure_record(level, coarse_count, heights, edges, value))

    source = Path(__file__).resolve()
    graph_source = source.with_name("verify_laakso_connection.py")
    report = {
        "status": "PASS",
        "scope": (
            "Exact finite rational-polynomial diagnostics for G0, G1, G2 only. "
            "No infinite Laakso limit, continuum convergence, numerical ODE "
            "integration, or formal proof-kernel verification is performed. "
            "The general no-linear-lumping theorem requires a separate proof."
        ),
        "arithmetic": "Python standard library fractions.Fraction; no floating-point tests",
        "script_sha256": sha256(source.read_bytes()).hexdigest(),
        "graph_constructor": {
            "file": graph_source.name,
            "sha256": sha256(graph_source.read_bytes()).hexdigest(),
            "function": "refine",
            "construction": "trisect, duplicate, identify only new subdivision vertices",
        },
        "model": {
            "fine_flow": "F_i(x)=3x_i-4x_i^3-lambda (Lx)_i; input u=0",
            "laplacian": "unweighted undirected multigraph; parallel edges counted",
            "projection_is_separate_from_geometric_graph_map": True,
        },
        "nonfactorization_witness": {
            "fine_coordinates": ["m+d", "m-d", "m", "m", "m", "m"],
            "fine_vertices": ["left sheet 0", "left sheet 1", "right sheet 0",
                              "right sheet 1", "shared at 1/3", "shared at 2/3"],
            "projection": ["(x0+x1)/2", "(x2+x3)/2"],
            "common_coarse_state": ["m", "m"],
            "left_residual": polynomial_record(residual[0], ["m", "d", "lambda"]),
            "right_residual": polynomial_record(residual[1], ["m", "d", "lambda"]),
            "symbolic_identity": "left residual = -12 m d^2 for every lambda",
            "uniform_fine_state_has_zero_residual": True,
            "concrete_values": {
                "m": "1/2", "d": "1/4",
                "fine_projected_left_derivative": "5/8",
                "coarse_left_derivative": "1",
                "uniform_fine_projected_left_derivative": "1",
                "left_defect": "-3/8",
                "applies_to": "all lambda, by the symbolic coefficient check",
            },
        },
        "jacobian_row_space_closures": closures,
        "synchronized_subspace": {
            "state_order": ["L", "R", "W1", "W2"],
            "lift": ["L", "L", "R", "R", "W1", "W2"],
            "quotient_edges_by_index": quotient_edges,
            "vertex_masses": list(map(str, masses)),
            "edge_conductances": list(map(str, conductances)),
            "quotient_flow": "f(q)-lambda M^-1 L_conductance q",
            "identity": "F_G1(Jq)=J F_H(q)",
            "checked_for_all_q_and_lambda_as_polynomial_identity": True,
            "fine_component_identities_checked": len(lifted_flow),
            "restriction": "only states with x0=x1 and x2=x3; not a global mean closure",
            "quotient_component_polynomials": [
                polynomial_record(poly, ["L", "R", "W1", "W2", "lambda"])
                for poly in quotient_flow
            ],
        },
    }
    destination = source.with_name("scale_flow_checks.json")
    destination.write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps({
        "status": report["status"],
        "output": str(destination),
        "witness_defect": "-3/8",
        "row_space_closures": [
            [item["fine_level"], item["coupling_lambda"], item["initial_projection_rank"],
             item["closed_row_space_rank"]]
            for item in closures
        ],
        "synchronized_component_identities": len(lifted_flow),
        "script_sha256": report["script_sha256"],
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
