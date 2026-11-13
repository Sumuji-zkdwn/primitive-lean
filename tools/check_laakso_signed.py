"""Exact finite checks for signed connections on the first Laakso graph.

Run: python -B tools/check_laakso_signed.py --output verification/laakso-signed.json

All 64 edge signatures and 64 vertex-spin assignments are enumerated.  Lift
vertices are connected by labelled edges, never identified.  Energy uses
q_i=(x_i, sqrt(2)*z_i), with rational x_i,z_i and lambda=kappa=1.  Sparse
polynomial coefficient checks and sampled evaluations are separate evidence
from the Lean all-real proofs.  No ODE, minimizer, or infinite-space claim is
made by this checker.  Only the standard library and the existing finite
Laakso graph builder are imported.
"""
import argparse
from collections import Counter, deque
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json

from check_laakso_finite import refine


ROOT = Path(__file__).resolve().parents[1]
BUILDER_TO_FIRST_EDGE = (0, 3, 1, 4, 2, 5)
VARIABLE_COUNT = 12
ZERO_EXPONENT = (0,) * VARIABLE_COUNT


def first_graph():
    heights, builder_edges = refine([Q(0), Q(1)], [(0, 1)])
    edges = [builder_edges[i] for i in BUILDER_TO_FIRST_EDGE]
    assert heights == [Q(0), Q(0), Q(1), Q(1), Q(1, 3), Q(2, 3)]
    assert edges == [(0, 4), (1, 4), (4, 5), (4, 5), (5, 2), (5, 3)]
    assert len(edges) - len(heights) + 1 == 1
    assert edges[2] == edges[3] and len(set(edges)) == 5
    return heights, edges


def components(vertex_count, edges):
    adjacency = [set() for _ in range(vertex_count)]
    for a, b in edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    unseen = set(range(vertex_count))
    result = []
    while unseen:
        start = min(unseen)
        reached, pending = {start}, deque([start])
        while pending:
            a = pending.popleft()
            for b in sorted(adjacency[a] - reached):
                reached.add(b)
                pending.append(b)
        unseen.difference_update(reached)
        result.append(sorted(reached))
    return result


def lift_edges(edges, signature):
    assert len(edges) == len(signature) and set(signature) <= {0, 1}
    return [(2 * a + sheet, 2 * b + (sheet ^ signature[e]))
            for e, (a, b) in enumerate(edges) for sheet in (0, 1)]


def feasible(edges, signature, spins):
    return all(spins[a] == (-1 if bit else 1) * spins[b]
               for (a, b), bit in zip(edges, signature))


def norm_squared(q):
    x, z = q
    return x * x + 2 * z * z


def dot(q, r):
    return q[0] * r[0] + 2 * q[1] * r[1]


def local_energy(q):
    x, z = q
    return (x * x - 1)**2 / 4 + (z - x)**2


def coupling_energy(q, r, bit, coefficient=Q(1, 2)):
    sign = -1 if bit else 1
    return coefficient * norm_squared((q[0] - sign * r[0], q[1] - sign * r[1]))


def energy_terms(edges, signature, state, coefficient=Q(1, 2)):
    local = [local_energy(q) for q in state]
    coupling = [coupling_energy(state[a], state[b], bit, coefficient)
                for (a, b), bit in zip(edges, signature)]
    return local, coupling


def energy(edges, signature, state, coefficient=Q(1, 2)):
    local, coupling = energy_terms(edges, signature, state, coefficient)
    return sum(local, Q(0)) + sum(coupling, Q(0))


def certificate_terms(edges, negative_signature, state):
    local, coupling = energy_terms(edges, negative_signature, state)
    residual = local[:4] + [coupling[e] for e in (0, 1, 4, 5)]
    middle = []
    for vertex in (4, 5):
        x, z = state[vertex]
        middle.extend((x**4 / 4, x*x / 2, (z-x)**2, 2*z*z))
    return middle, residual


# Sparse coefficient arithmetic: keys are exponent vectors for x0,z0,...,x5,z5.
def constant(value):
    return {ZERO_EXPONENT: Q(value)} if value else {}


def variable(index):
    powers = list(ZERO_EXPONENT)
    powers[index] = 1
    return {tuple(powers): Q(1)}


def add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for powers, coefficient in polynomial.items():
            result[powers] = result.get(powers, Q(0)) + coefficient
    return {powers: coefficient for powers, coefficient in result.items() if coefficient}


def scale(polynomial, factor):
    return {powers: coefficient * factor for powers, coefficient in polynomial.items()
            if coefficient * factor}


def multiply(left, right):
    result = {}
    for a, ca in left.items():
        for b, cb in right.items():
            powers = tuple(x + y for x, y in zip(a, b))
            result[powers] = result.get(powers, Q(0)) + ca * cb
    return {powers: coefficient for powers, coefficient in result.items() if coefficient}


def square(polynomial):
    return multiply(polynomial, polynomial)


def polynomial_terms(edges, signature, coefficient=Q(1, 2)):
    x = [variable(2*i) for i in range(6)]
    z = [variable(2*i+1) for i in range(6)]
    local = [add(scale(square(add(square(x[i]), constant(-1))), Q(1, 4)),
                 square(add(z[i], scale(x[i], -1)))) for i in range(6)]
    coupling = []
    for (a, b), bit in zip(edges, signature):
        sign = -1 if bit else 1
        coupling.append(scale(add(square(add(x[a], scale(x[b], -sign))),
                                  scale(square(add(z[a], scale(z[b], -sign))), 2)), coefficient))
    return local, coupling


def polynomial_check(edges, positive, negative):
    local, coupling = polynomial_terms(edges, negative)
    total = add(*local, *coupling)
    certificate = [constant(Q(1, 2)), *local[:4], *(coupling[e] for e in (0, 1, 4, 5))]
    for vertex in (4, 5):
        x, z = variable(2*vertex), variable(2*vertex+1)
        certificate.extend((scale(square(square(x)), Q(1, 4)),
                            scale(square(x), Q(1, 2)),
                            square(add(z, scale(x, -1))), scale(square(z), 2)))
    certificate = add(*certificate)
    assert add(total, scale(certificate, -1)) == {}
    pos_local, pos_coupling = polynomial_terms(edges, positive)
    jump = add(total, scale(add(*pos_local, *pos_coupling), -1))
    expected_jump = add(scale(multiply(variable(8), variable(10)), 2),
                        scale(multiply(variable(9), variable(11)), 4))
    assert jump == expected_jump
    wrong_local, wrong_coupling = polynomial_terms(edges, negative, coefficient=Q(1))
    wrong_residual = add(*wrong_local, *wrong_coupling, scale(certificate, -1))
    assert wrong_residual
    return dict(variable_order=[name for i in range(6) for name in (f"x{i}", f"z{i}")],
                coefficient_domain="fractions.Fraction", energy_monomials=len(total),
                certificate_residual_monomials=0, flip_jump_residual_monomials=0,
                wrong_coupling_coefficient_residual_monomials=len(wrong_residual),
                certificate="F_negative = 1/2 + sum_{i=4,5}(x_i^4/4 + x_i^2/2 + (z_i-x_i)^2 + 2*z_i^2) + residual",
                residual="sum_{i=0..3} localEnergy(i) + sum_{e in {0,1,4,5}} couplingEnergy(e)",
                flip_jump="F_negative-F_positive = 2*x4*x5 + 4*z4*z5 = 2*q4 dot q5")


def check():
    heights, edges = first_graph()
    positive, negative = (0,) * 6, (0, 0, 0, 1, 0, 0)
    spin_states = list(product((-1, 1), repeat=6))
    rows = []
    for mask in range(64):
        signature = tuple((mask >> edge) & 1 for edge in range(6))
        lifted = lift_edges(edges, signature)
        assert len(lifted) == 12
        parts = components(12, lifted)
        parity = signature[2] ^ signature[3]
        assert [len(part) for part in parts] == ([12] if parity else [6, 6])
        solutions = [spins for spins in spin_states if feasible(edges, signature, spins)]
        assert len(solutions) == (0 if parity else 2)
        well_energies = []
        for spins in spin_states:
            state = [(Q(s), Q(s)) for s in spins]
            value = energy(edges, signature, state)
            assert (value == 0) == feasible(edges, signature, spins)
            well_energies.append(value)
        assert min(well_energies) == (Q(6) if parity else Q(0))
        rows.append(dict(mask=mask, signature=list(signature), middle_cycle_parity=parity,
                         lift_vertices=12, lift_labelled_edges=len(lifted),
                         component_sizes=[len(part) for part in parts],
                         reach_from_vertex0_sheet0=len(parts[0]),
                         feasible_spin_assignments=len(solutions),
                         minimum_over_64_discrete_well_states=str(min(well_energies))))
    assert Counter(row["middle_cycle_parity"] for row in rows) == {0: 32, 1: 32}

    well = [(Q(1), Q(1))] * 6
    zero = [(Q(0), Q(0))] * 6
    decreasing = zero[:]
    decreasing[4], decreasing[5] = (Q(1), Q(1)), (Q(-1), Q(-1))
    samples = [("positive_well", well), ("zero", zero), ("opposite_middle_wells", decreasing),
               ("rational_mixed", [(Q(i-2, 3), Q(3-i, 5)) for i in range(6)]),
               ("half_well", [(Q(1, 2), Q(1, 2))] * 6)]
    samples += [(f"spin_wells_{i}", [(Q(s), Q(s)) for s in spins])
                for i, spins in enumerate(spin_states)]
    for _, state in samples:
        middle, residual = certificate_terms(edges, negative, state)
        assert all(term >= 0 for term in middle + residual)
        assert energy(edges, negative, state) == Q(1, 2) + sum(middle) + sum(residual)
        assert energy(edges, negative, state) >= Q(1, 2)
        assert energy(edges, negative, state) - energy(edges, positive, state) == 2 * dot(state[4], state[5])
    examples = []
    for name, state in samples[:5]:
        before, after = energy(edges, positive, state), energy(edges, negative, state)
        examples.append(dict(name=name, state_x_z=[[str(x), str(z)] for x, z in state],
                             before=str(before), after=str(after), jump=str(after-before)))
    assert examples[0]["before"] == "0" and examples[0]["jump"] == "6"
    assert examples[2]["jump"] == "-6"

    # Four deliberately wrong constructions must fail separate invariants.
    kept = list(dict.fromkeys(edges))
    kept_ids = [edges.index(edge) for edge in kept]
    collapsed = lift_edges(kept, [negative[e] for e in kept_ids])
    assert len(collapsed) == 10 and len(components(12, collapsed)) == 2
    correct_negative_parts = components(12, lift_edges(edges, negative))
    quotient_vertex_count = len(correct_negative_parts)
    assert quotient_vertex_count == 1 and quotient_vertex_count != 12
    sign_ignoring_parts = components(12, lift_edges(edges, positive))
    assert len(sign_ignoring_parts) == 2 != len(correct_negative_parts)
    wrong_jump = energy(edges, negative, well, Q(1)) - energy(edges, positive, well, Q(1))
    assert wrong_jump == 12 and wrong_jump != 2 * dot(well[4], well[5])
    mutations = [
        dict(name="deduplicating_parallel_edges", rejected=True, expected_lift_edges=12,
             mutated_lift_edges=len(collapsed), expected_components=1, mutated_components=2),
        dict(name="treating_lift_edges_as_quotient_identifications", rejected=True,
             expected_vertices=12, mutated_vertices=quotient_vertex_count),
        dict(name="ignoring_sign_change_and_reusing_old_components", rejected=True,
             expected_components=1, mutated_components=2, expected_reach=12, mutated_reach=6),
        dict(name="using_coupling_coefficient_one_instead_of_half", rejected=True,
             expected_flip_jump="6", mutated_flip_jump=str(wrong_jump))]
    polynomial = polynomial_check(edges, positive, negative)
    return dict(passed=True,
                scope="Finite first-level Laakso signed graph; exhaustive signatures and spins, exact rational samples and polynomial coefficient identities; distinct from Lean all-real proofs",
                graph=dict(vertices=6, labelled_edges=edges, vertex_heights=list(map(str, heights)),
                           builder_edge_order_to_firstGraph=list(BUILDER_TO_FIRST_EDGE),
                           middle_parallel_edge_ids=[2, 3]),
                signature_count=64, balanced_signatures=32, unbalanced_signatures=32,
                spin_assignments_per_signature=64, signature_spin_checks=4096,
                discrete_well_energy_checks=4096, signatures=rows,
                chosen_pair=dict(changed_edge_ids=[i for i in range(6) if positive[i] != negative[i]],
                                 positive=rows[0], one_negative=rows[8],
                                 unchanged_lift_vertex_count=12, unchanged_lift_edge_count=12),
                energy=dict(lambda_value="1", kappa_value="1", coordinates="q_i=(x_i,sqrt(2)*z_i)",
                            local_energy="(x_i^2-1)^2/4+(z_i-x_i)^2",
                            coupling_energy="((x_i-sigma*x_j)^2+2*(z_i-sigma*z_j)^2)/2",
                            polynomial_coefficient_checks=polynomial,
                            nonnegative_certificate_sample_count=len(samples),
                            fixed_state_flip_sample_count=len(samples), examples=examples,
                            lower_bound="1/2", lower_bound_scope="The one-negative e3 signature with lambda=kappa=1; not claimed sharp or uniform over parameters"),
                mutation_controls=mutations, mutation_controls_rejected=len(mutations),
                limits=["A 2-lift connects distinct vertices; it is not the Laakso refinement quotient.",
                        "Finite reachable vertex counts are not physical mass or geometric volume.",
                        "Discrete well-state minima are not continuous-state global minima.",
                        "No ODE integration, minimizer existence, metric-measure inverse limit, or Poincare theorem is tested."])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "verification/laakso-signed.json",
                        help="Write deterministic JSON evidence (default: verification/laakso-signed.json)")
    args = parser.parse_args()
    result = check()
    result["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    builder = Path(__file__).with_name("check_laakso_finite.py")
    result["graph_builder_sha256"] = hashlib.sha256(builder.read_bytes()).hexdigest()
    source = ROOT / "sources/laakso/signed/SIGNED_CONNECTIONS.md"
    result["signed_connections_source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                               encoding="utf-8", newline="\n")
    print("PASS: 64 signatures, 4096 spin assignments and 4096 exact well-state energy checks")
    print(f"PASS: {result['energy']['nonnegative_certificate_sample_count']} rational certificate and flip-jump samples; sparse polynomial identities")
    print("PASS: all-positive vs e3-negative: 12 vertices, 12 edges; components 2 -> 1; reach 6 -> 12")
    print("PASS: four mutation controls rejected")
    if args.output:
        print(f"Evidence: {args.output}")


if __name__ == "__main__":
    main()
