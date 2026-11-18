"""Check the sharp odd-sector minimum on the first Laakso graph using exact LDL pivots.

Run python -B tools/check_laakso_minimum.py to create verification/laakso-minimum.json.
"""

import argparse
from fractions import Fraction
from itertools import product
import json
from math import prod
from pathlib import Path

from check_laakso_signed import ZERO_EXPONENT, add, energy, first_graph, polynomial_terms


ROOT = Path(__file__).resolve().parents[1]


def quadratic_hessian(edges, signature, vertex_count):
    """Extract H from E = 3/2 + sum(x_i^4)/4 + (x,z)^T H (x,z)/2."""
    local, coupling = polynomial_terms(edges, signature)
    terms = add(*local, *coupling)
    assert terms.pop(ZERO_EXPONENT) == Fraction(3, 2)
    for vertex in range(vertex_count):
        powers = [0] * (2 * vertex_count)
        powers[2 * vertex] = 4
        assert terms.pop(tuple(powers)) == Fraction(1, 4)

    # The source polynomial interleaves x_i,z_i. Group x first, then z in H.
    order = [2 * v + axis for axis in (0, 1) for v in range(vertex_count)]
    matrix = [[Fraction(0) for _ in order] for _ in order]
    for powers, coefficient in terms.items():
        assert sum(powers) == 2
        i, j = [index for index, source in enumerate(order) for _ in range(powers[source])]
        matrix[i][j] += coefficient
        matrix[j][i] += coefficient
    return matrix


def positive_pivots(matrix):
    """Eliminate one coordinate per step, requiring a positive exact pivot."""
    pivots = []
    while matrix:
        pivot = matrix[0][0]
        assert pivot > 0, f"nonpositive LDL pivot at index {len(pivots)}: {pivot}"
        pivots.append(pivot)
        remaining = range(1, len(matrix))
        matrix = [[matrix[i][j] - matrix[i][0] * matrix[0][j] / pivot for j in remaining]
                  for i in remaining]
    return pivots


def check():
    heights, edges = first_graph()
    vertex_count = len(heights)
    zero_state = [(Fraction(0), Fraction(0))] * vertex_count
    odd_signatures = [s for s in product((0, 1), repeat=len(edges)) if s[2] != s[3]]
    assert len(odd_signatures) == 32
    certificates = []
    for signature in odd_signatures:
        assert energy(edges, signature, zero_state) == Fraction(3, 2)
        certificates.append(positive_pivots(quadratic_hessian(edges, signature, vertex_count)))

    pivots = certificates[0]
    assert len(pivots) == 2 * vertex_count and all(cert == pivots for cert in certificates)
    assert prod(pivots) == 1024
    return {
        "passed": True,
        "scope": "First Laakso approximant, lambda=kappa=1, u=0, odd middle-cycle parity",
        "coordinates": "q_i=(x_i,sqrt(2)*z_i)",
        "variable_order": [f"{axis}{i}" for axis in ("x", "z") for i in range(vertex_count)],
        "labelled_edges": edges,
        "odd_signatures_checked": len(certificates),
        "polynomial_identity": "E=3/2+sum_i(x_i^4)/4+w^T H w/2",
        "common_exact_ldl_pivots": [str(d) for d in pivots],
        "hessian_determinant": str(prod(pivots)),
        "attained_minimum": "3/2",
        "unique_minimizer": "all x_i=z_i=0",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "verification/laakso-minimum.json")
    args = parser.parse_args()
    report = check()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8", newline="\n")
    print(f"PASS: {report['odd_signatures_checked']} odd signatures, positive exact LDL pivots; "
          f"unique minimum {report['attained_minimum']} at zero")


if __name__ == "__main__":
    main()
