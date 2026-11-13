"""Independent exact finite checks for the Laakso observation extension.

The graph is built by repeated subdivision, duplication, and gluing only NEW
vertices, independently of the Lean recursive types and six-edge table.
This checks finite instances; the general algebraic statements are in Lean.
Research inputs and their hashes are recorded in docs/laakso/provenance.json.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def refine(heights, edges):
    result = [h for h in heights for _ in range(2)]
    refined = []
    for left, right in edges:
        a, b = len(result), len(result) + 1
        result.extend((heights[left] + (heights[right] - heights[left]) / 3,
                       heights[left] + 2 * (heights[right] - heights[left]) / 3))
        for sheet in range(2):
            refined.extend(((2 * left + sheet, a), (a, b), (b, 2 * right + sheet)))
    return result, refined


def laplacian(values, edges, masses=None, conductances=None):
    masses = [Q(1)] * len(values) if masses is None else masses
    conductances = [Q(1)] * len(edges) if conductances is None else conductances
    result = [Q(0)] * len(values)
    for (a, b), c in zip(edges, conductances):
        delta = c * (values[a] - values[b])
        result[a] += delta
        result[b] -= delta
    return [v / m for v, m in zip(result, masses)]


def field(values, edges, coupling, masses=None, conductances=None):
    lap = laplacian(values, edges, masses, conductances)
    return [3 * v - 4 * v**3 - coupling * d for v, d in zip(values, lap)]


def means(x):
    return ((x[0] + x[1]) / 2, (x[2] + x[3]) / 2)


def lift(q):
    return [q[0], q[0], q[1], q[1], q[2], q[3]]


def euler(x, velocity, step):
    return [v + step * d for v, d in zip(x, velocity)]


def check():
    heights, edges = [Q(0), Q(1)], [(0, 1)]
    levels = []
    first_edges = None
    for n in range(5):
        degrees = Counter(v for edge in edges for v in edge)
        assert len(edges) == 6**n
        expected_v = 2 if n == 0 else 2**(n-1) * (3**n + 3)
        assert len(heights) == expected_v
        assert set(degrees.values()) <= {1, 4}
        assert Counter(degrees.values())[1] == 2**(n+1)
        assert all(heights[b] - heights[a] == Q(1, 3**n) for a, b in edges)
        adjacency = {i: [] for i in range(len(heights))}
        for a, b in edges:
            adjacency[a].append(b)
            adjacency[b].append(a)
        pending, seen = [0], {0}
        while pending:
            for b in adjacency[pending.pop()]:
                if b not in seen:
                    seen.add(b)
                    pending.append(b)
        assert len(seen) == len(heights)
        levels.append(dict(level=n, vertices=len(heights), edges=len(edges),
                           cycle_rank=len(edges)-len(heights)+1))
        if n == 1:
            first_edges = edges[:]
            assert Counter(edges) == Counter(((0, 4), (1, 4), (4, 5),
                                               (4, 5), (5, 2), (5, 3)))
        if n < 4:
            heights, edges = refine(heights, edges)

    # Same mean, different projected velocity, including nonzero coupling.
    uniform = [Q(1, 2)] * 6
    perturbed = [Q(3, 4), Q(1, 4)] + [Q(1, 2)] * 4
    assert means(uniform) == means(perturbed) == (Q(1, 2), Q(1, 2))
    witness_rows = []
    for coupling in (Q(-2), Q(0), Q(1), Q(7, 3)):
        a = means(field(uniform, first_edges, coupling))
        b = means(field(perturbed, first_edges, coupling))
        assert a == (Q(1), Q(1)) and b == (Q(5, 8), Q(1))
        for step in (Q(-1, 10), Q(0), Q(1, 10), Q(1)):
            ua = means(euler(uniform, field(uniform, first_edges, coupling), step))
            ub = means(euler(perturbed, field(perturbed, first_edges, coupling), step))
            assert (ua == ub) == (step == 0)
        witness_rows.append(dict(coupling=str(coupling),
                                 uniform=list(map(str, a)), perturbed=list(map(str, b))))

    # The synchronized subsystem has masses (2,2,1,1), NOT four unit masses.
    coarse_edges = [(0, 2), (2, 3), (3, 1)]
    masses, weights = [Q(2), Q(2), Q(1), Q(1)], [Q(2)] * 3
    sync_cases = 0
    for q in ([Q(0), Q(1), Q(2), Q(-1)], [Q(1, 2)] * 4,
              [Q(1, 3), Q(-2, 5), Q(4, 7), Q(0)]):
        for coupling in (Q(0), Q(1), Q(-3, 2)):
            fine = lift(q)
            coarse = q[:]
            for _ in range(4):
                fine_velocity = field(fine, first_edges, coupling)
                coarse_velocity = field(coarse, coarse_edges, coupling, masses, weights)
                assert fine == lift(coarse) and fine_velocity == lift(coarse_velocity)
                fine = euler(fine, fine_velocity, Q(1, 100))
                coarse = euler(coarse, coarse_velocity, Q(1, 100))
                sync_cases += 1
    # Mutation controls: either losing a parallel edge or ignoring masses
    # changes the actual field; a passing check cannot silently do either.
    q = [Q(0), Q(0), Q(0), Q(1)]
    dropped = first_edges[:]
    dropped.remove((4, 5))
    expected = lift(field(q, coarse_edges, Q(1), masses, weights))
    assert field(lift(q), dropped, Q(1)) != expected
    q = [Q(1), Q(0), Q(0), Q(0)]
    assert field(lift(q), first_edges, Q(1)) != lift(field(q, coarse_edges, Q(1), None, weights))
    return dict(passed=True, scope='Exact finite rational instances, not an infinite-space theorem',
                graph_levels=levels, mean_obstruction=witness_rows,
                synchronized_steps_checked=sync_cases,
                mutation_controls=['missing parallel edge rejected', 'unit masses rejected'])


if __name__ == '__main__':
    result = check()
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    out = ROOT / 'verification'
    out.mkdir(exist_ok=True)
    (out / 'laakso-finite.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
