#!/usr/bin/env python3
"""Audited finite checks for forgetting, quotients, and relational round trips.

Python 3 standard library only. Run: python3 tools/forgetting_roundtrips.py
All checks run under optimized Python too: verify() does not use assert.
All algebra and probabilities are exact (integers/Fraction). Only displayed
entropies use floating-point log2. This is a mathematical verification script,
not a model fit to neural or fluid data and not a Lean kernel compilation.

The original 15 real/integer states are INITIAL CONDITIONS, not an E-invariant
finite state space. A separate F_5 example is a closed finite state system.
"""
from collections import Counter, defaultdict, deque
from fractions import Fraction as F
from itertools import product
from math import log2
import json


def verify(condition, message):
    """Fail a finite certificate even if Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def compose(first, second):
    """Finite relation: second after first. Preserve empty output rows."""
    return {x: {z for y in ys for z in second[y]}
            for x, ys in first.items()}


def converse(rel, target):
    return {y: {x for x, ys in rel.items() if y in ys} for y in target}


def all_relations(domain, codomain):
    for bits in product((False, True), repeat=len(domain)*len(codomain)):
        yield {x: {y for j, y in enumerate(codomain)
                   if bits[i*len(codomain)+j]}
               for i, x in enumerate(domain)}


def relation_audit():
    X, Y = tuple(range(3)), tuple(range(2))
    checked = first_count = second_count = both_count = 0
    for labels in product(Y, repeat=len(X)):
        if set(labels) != set(Y):
            continue
        f = {x: {labels[x]} for x in X}
        for g in all_relations(Y, X):
            first = compose(compose(f, g), f) == f
            second = compose(compose(g, f), g) == g
            fiber_condition = all(g[y] and all(labels[x] == y for x in g[y])
                                  for y in Y)
            verify(
                first == bool(fiber_condition),
                'Fiber condition does not match f-g-f consistency',
            )
            verify(
                not first or second,
                'f-g-f consistency failed to imply g-f-g consistency',
            )
            checked += 1
            first_count += first
            second_count += second
            both_count += first and second
    verify(
        (checked, first_count, second_count, both_count) == (384, 18, 174, 18),
        'Unexpected complete 3-to-2 relational census',
    )

    # General many-valued relation: the converse need not satisfy R R^dagger R=R.
    r = {0: {0}, 1: {0, 1}}
    rd = converse(r, (0, 1))
    triple = compose(compose(r, rd), r)
    verify(
        triple == {0: {0, 1}, 1: {0, 1}} and triple != r,
        'Converse-relation counterexample failed',
    )
    difunctional = 0
    for r2 in all_relations((0, 1), (0, 1)):
        d2 = converse(r2, (0, 1))
        algebraic = compose(compose(r2, d2), r2) == r2
        rectangle = all(y2 in r2[x]
                        for x, xp, y, y2 in product(range(2), repeat=4)
                        if y in r2[x] and y in r2[xp] and y2 in r2[xp])
        verify(
            algebraic == rectangle,
            'Rectangle condition and converse triple disagree',
        )
        difunctional += algebraic
    verify(
        difunctional == 12,
        'Unexpected 2-by-2 difunctional relation count',
    )
    return {"surjection_decoder_pairs": checked,
            "fgf_equals_f": first_count, "gfg_equals_g": second_count,
            "both": both_count, "two_by_two_relations": 16,
            "difunctional_two_by_two_relations": difunctional}


def matmul(a, b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def row_tv(a, b):
    return sum((abs(x-y) for x, y in zip(a, b)), F(0))/2


def kernel_distance(a, b):
    return max(row_tv(x, y) for x, y in zip(a, b))


def kernel_audit():
    """Row-stochastic matrices: FGF is chronological f, G, f."""
    distributions = [[F(a, 3), F(b, 3), F(3-a-b, 3)]
                     for a in range(4) for b in range(4-a)]
    checked = 0
    for labels in product(range(2), repeat=3):
        if set(labels) != {0, 1}:
            continue
        encoder = [[F(labels[x] == y) for y in range(2)] for x in range(3)]
        for rows in product(distributions, repeat=2):
            decoder = [list(row) for row in rows]
            delta = max(1-sum((decoder[y][x] for x in range(3)
                               if labels[x] == y), F(0)) for y in range(2))
            first_error = kernel_distance(matmul(matmul(encoder, decoder), encoder), encoder)
            second_error = kernel_distance(matmul(matmul(decoder, encoder), decoder), decoder)
            verify(
                first_error == delta and second_error <= delta,
                'Exact total-variation round-trip bound failed',
            )
            checked += 1
    verify(
        checked == 600,
        'Unexpected rational-kernel census size',
    )
    # Perfect consistency and marginal recovery do not recover the original draw.
    n = 7
    encoder = [[F(1)] for _ in range(n)]
    decoder = [[F(1, n)]*n]
    transition = matmul(encoder, decoder)
    prior = [[F(1, n)]*n]
    verify(
        matmul(prior, transition) == prior,
        'Uniform marginal was not reconstructed',
    )
    verify(
        matmul(transition, transition) == transition,
        'Fiber resampling is not idempotent',
    )
    verify(
        kernel_distance(matmul(transition, encoder), encoder) == 0,
        'Uniform resampling changed the coarse label',
    )
    success = sum((prior[0][i]*transition[i][i] for i in range(n)), F(0))
    verify(
        success == F(1, n),
        'Individual recovery was incorrectly inferred from its marginal',
    )
    return {"rational_kernel_pairs": checked,
            "marginal_recovery_counterexample_states": n,
            "marginal_tv": "0", "individual_success": str(success)}


def invariant(z):
    u, v = z
    return v+u**3


def poly_E(z):
    r = invariant(z)
    u = z[0]+r*r
    return u, r-u**3


def inverse_E(z):
    r = invariant(z)
    u = z[0]-r*r
    return u, r-u**3


def probe_R(z):
    return z[0], z[1]+1


def quotient(z):
    return z[0], invariant(z)**2


def readouts(z):
    return z[0], poly_E(z)[0], poly_E(probe_R(z))[0]


def sequential_readouts(z):
    after_e = poly_E(z)
    return z[0], after_e[0], poly_E(probe_R(after_e))[0]


def real_sample_audit():
    X = {(u, r-u**3) for u in (-1, 0, 1) for r in (-2, -1, 0, 1, 2)}
    fibers = defaultdict(set)
    for z in X:
        fibers[quotient(z)].add(z)
        verify(
            inverse_E(poly_E(z)) == z and poly_E(inverse_E(z)) == z,
            'Explicit polynomial inverse failed',
        )
        verify(
            invariant(poly_E(z)) == invariant(z),
            'Polynomial invariant changed under E',
        )
        y = quotient(z)
        verify(
            quotient(poly_E(z)) == (y[0]+y[1], y[1]),
            'Polynomial quotient semiconjugacy failed',
        )
        k0, k1, k2 = readouts(z)
        verify(
            F(k2-k1-1, 2) == invariant(z),
            'Separate-probe sign reconstruction failed',
        )
        a0, a1, a2 = sequential_readouts(z)
        verify(
            F(a2-2*a1+a0-1, 2) == invariant(z),
            'Sequential-probe sign reconstruction failed',
        )
        step = z
        for n in range(9):
            u = z[0]+n*invariant(z)**2
            verify(
                step == (u, invariant(z)-u**3),
                'Closed-form E iteration failed',
            )
            step = poly_E(step)
    f = {z: {quotient(z)} for z in X}
    g = dict(fibers)
    verify(
        compose(compose(f, g), f) == f,
        'Full-fiber decoder failed f-g-f consistency',
    )
    verify(
        compose(compose(g, f), g) == g,
        'Full-fiber decoder failed g-f-g consistency',
    )
    # Keep one representative from each fiber: both identities still hold.
    representatives = {y: {min(zs)} for y, zs in fibers.items()}
    verify(
        compose(compose(f, representatives), f) == f,
        'Representative decoder failed f-g-f consistency',
    )
    verify(
        compose(compose(representatives, f), representatives) == representatives,
        'Representative decoder failed g-f-g consistency',
    )
    omitted = sum(z not in representatives[quotient(z)] for z in X)
    verify(
        omitted == 6,
        'Unexpected representative-decoder omission count',
    )
    success = F(len(fibers), len(X))
    entropy = sum(len(zs)/len(X)*log2(len(zs)) for zs in fibers.values())
    optimal_mse = sum((F(invariant(z)**2) for z in X), F(0))/len(X)
    consistent_mse = sum((F((abs(invariant(z))-invariant(z))**2)
                          for z in X), F(0))/len(X)
    escaped = len({poly_E(z) for z in X}-X)
    verify(
        (len(X), len(fibers), len({readouts(z) for z in X})) == (15, 9, 15),
        'Unexpected real initial-sample class counts',
    )
    verify(
        success == F(3, 5) and abs(entropy-0.8) < 1e-12,
        'Real initial-sample recovery statistics failed',
    )
    verify(
        optimal_mse == 2 and consistent_mse == 4 and escaped > 0,
        'Real sample reconstruction error or nonclosure check failed',
    )
    return {"initial_states": len(X), "coarse_classes": len(fibers),
            "probe_classes": len({readouts(z) for z in X}),
            "fiber_sizes": dict(Counter(map(len, fibers.values()))),
            "uniform_optimal_recovery": str(success), "conditional_bits": entropy,
            "E_images_outside_initial_set": escaped,
            "representative_decoder_omits": omitted,
            "unconstrained_r_mse": str(optimal_mse),
            "consistent_r_mse": str(consistent_mse)}


def finite_field_audit():
    """A genuinely closed finite state system, distinct from the real sample."""
    p = 5
    X = set(product(range(p), repeat=2))
    def e(z):
        return tuple(v % p for v in poly_E(z))
    def r(z):
        return tuple(v % p for v in probe_R(z))
    def q(z):
        return z[0], invariant(z)**2 % p
    def obs(z):
        return z[0], e(z)[0], e(r(z))[0]
    verify(
        {e(z) for z in X} == X and {r(z) for z in X} == X,
        'Finite-field E or R is not a closed permutation',
    )
    fibers = defaultdict(set)
    for z in X:
        fibers[q(z)].add(z)
        y = q(z)
        verify(
            q(e(z)) == ((y[0]+y[1]) % p, y[1]),
            'Finite-field quotient semiconjugacy failed',
        )
        k0, k1, k2 = obs(z)
        recovered_r = (k2-k1-1)*3 % p  # 3 is 2^{-1} in F_5.
        verify(
            recovered_r == invariant(z) % p,
            'Finite-field invariant reconstruction failed',
        )
        verify(
            (k0, (recovered_r-k0**3) % p) == z,
            'Finite-field full-state reconstruction failed',
        )
    f = {z: {q(z)} for z in X}
    g = dict(fibers)
    verify(
        compose(compose(f, g), f) == f,
        'Finite-field f-g-f consistency failed',
    )
    verify(
        compose(compose(g, f), g) == g,
        'Finite-field g-f-g consistency failed',
    )
    verify(
        (len(X), len(fibers), len({obs(z) for z in X})) == (25, 15, 25),
        'Unexpected finite-field class counts',
    )
    entropy = sum(len(zs)/len(X)*log2(len(zs)) for zs in fibers.values())
    return {"field_prime": p, "states": len(X), "coarse_classes": len(fibers),
            "probe_classes": len({obs(z) for z in X}),
            "uniform_optimal_recovery": str(F(len(fibers), len(X))),
            "conditional_bits": entropy, "E_and_R_closed_permutations": True}


def shortest_distance(vertices, edges, source, target):
    neighbors = {v: set() for v in vertices}
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)
    todo, seen = deque([(source, 0)]), {source}
    while todo:
        x, d = todo.popleft()
        if x == target:
            return d
        for y in neighbors[x]-seen:
            seen.add(y)
            todo.append((y, d+1))
    return None


def graph_audit():
    X = set(range(6))
    edges = {(0, 2), (0, 3), (1, 4), (1, 5), (2, 4), (3, 5)}
    p = lambda x: 6 if x in (0, 1) else x
    qedges = {tuple(sorted((p(a), p(b)))) for a, b in edges}
    Y = {p(x) for x in X}
    degree = Counter(v for edge in edges for v in edge)
    qdegree = Counter(v for edge in qedges for v in edge)
    before = shortest_distance(X, edges, 2, 5)
    after = shortest_distance(Y, qedges, 2, 5)
    verify(
        (max(degree.values()), max(qdegree.values()), before, after) == (2, 4, 3, 2),
        'Graph quotient degree or distance counterexample failed',
    )
    # A path 2 -> H -> 5 in the quotient has no length-two lift in the original.
    undirected = {frozenset(edge) for edge in edges}
    verify(
        not any(frozenset((2, h)) in undirected and frozenset((h, 5)) in undirected
                   for h in (0, 1)),
        'Quotient shortcut unexpectedly has a length-two lift',
    )
    return {"vertices_before_after": [6, 5], "max_degree_before_after": [2, 4],
            "distance_2_5_before_after": [before, after],
            "quotient_shortcut_has_original_lift": False}


def relay_audit():
    def update(h, a):
        return 0 if a <= -1 else 1 if a >= 1 else h
    def terminal(inputs):
        h = 0
        for a in inputs:
            h = update(h, a)
        return h
    verify(
        terminal((2, 0)) == 1 and terminal((-2, 0)) == 0,
        'Relay failed to distinguish the chosen histories',
    )
    # Two distinct histories with the same current input produce the same state too.
    verify(
        terminal((2, 0)) == terminal((2, 2, 0)),
        'Relay unexpectedly distinguished every chosen history',
    )
    return {"same_current_input_distinct_mask_states": True,
            "all_input_histories_injectively_recorded": False}


def verify_all():
    """Run the bounded exact checks and return their JSON-compatible report."""
    return {"status": "all checks passed", "relations": relation_audit(),
              "probability_kernels": kernel_audit(),
              "real_initial_sample": real_sample_audit(),
              "closed_finite_field_system": finite_field_audit(),
              "graph": graph_audit(), "hysteretic_relay": relay_audit()}


def main():
    print(json.dumps(verify_all(), ensure_ascii=False, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
