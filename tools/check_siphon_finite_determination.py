#!/usr/bin/env python3
"""Independent exact checks; finite examples are not a universal proof.

Original coordinates, Fraction arithmetic, modular nonzero-minor certificates.
Requires Python 3.10+ and sympy (only for the symbolic degree checks).
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sympy as sp


def invariant(z):
    u, v = z
    return v + u**3


def E(z):
    u, v = z
    # Expanded original-coordinate update, independent of the orbit formula.
    x = u + v*v + 2*v*u**3 + u**6
    return x, v + u**3 - x**3


def L(z):
    u, v = z
    return v, v-u


def orbit(z, n):
    r = invariant(z)
    x = z[0] + n*r*r
    return x, r-x**3


def regularize(z):
    assert z != (0, 0)
    prefix = int(invariant(z) == 0)
    a = L(z) if prefix else z
    assert invariant(a) != 0
    return a, prefix


def candidates(z, d):
    a, prefix = regularize(z)
    starts = [L(orbit(a, n)) for n in range(d+2)]
    levels = [invariant(t) for t in starts]
    assert all(x > y for x, y in zip(levels, levels[1:]))
    assert levels.count(0) <= 1
    selected_curves = [n for n, r in enumerate(levels) if r != 0][:d+1]
    assert len(selected_curves) == d+1
    out = []
    for n in selected_curves:
        current = starts[n]
        for m in range(3*d+1):
            point = orbit(starts[n], m)
            assert point == current  # closed orbit vs expanded recurrence
            assert invariant(point) == levels[n]
            out.append(((n, m), point))
            current = E(current)
    assert len(set(point for _, point in out)) == len(out)
    return out, selected_curves, prefix, [n for n, r in enumerate(levels) if r == 0]


def modq(x, prime):
    x = F(x)
    return (x.numerator % prime) * pow(x.denominator % prime, -1, prime) % prime


def row(point, powers, prime):
    u, v = (modq(t, prime) for t in point)
    return [pow(u, i, prime)*pow(v, j, prime) % prime for i, j in powers]


def pivot_rows(points, powers, prime):
    basis, chosen, original = {}, [], []
    for word, point in points:
        r = row(point, powers, prime)
        before = r[:]
        for j in range(len(r)):
            if not r[j]:
                continue
            if j not in basis:
                inv = pow(r[j], -1, prime)
                basis[j] = [x*inv % prime for x in r]
                chosen.append(word)
                original.append(before)
                break
            factor = r[j]
            r = [(x-factor*y) % prime for x, y in zip(r, basis[j])]
        if len(basis) == len(powers):
            return chosen, original
    return chosen, original


def determinant_mod(matrix, prime):
    a = [r[:] for r in matrix]
    n = len(a)
    assert all(len(r) == n for r in a)
    det = 1
    for j in range(n):
        k = next((k for k in range(j, n) if a[k][j]), None)
        if k is None:
            return 0
        if k != j:
            a[k], a[j] = a[j], a[k]
            det = -det
        pivot = a[j][j]
        det = det*pivot % prime
        inv = pow(pivot, -1, prime)
        for k in range(j+1, n):
            factor = a[k][j]*inv % prime
            for c in range(j, n):
                a[k][c] = (a[k][c]-factor*a[j][c]) % prime
    return det % prime


def symbolic_checks(max_d=12):
    u, r = sp.symbols('u r', real=True)
    outgoing = r-u**3-u+(r-u**3)**3
    assert sp.expand(sp.diff(outgoing, u) + 1 + 3*u**2 + 9*u**2*(r-u**3)**2) == 0
    assert sp.expand((-u**3-u+(-u**3)**3) + u*(u**8+u**2+1)) == 0
    count = 0
    for d in range(max_d+1):
        for i in range(d+1):
            for j in range(d+1-i):
                p = sp.Poly(sp.expand(u**i*(r-u**3)**j), u, r)
                assert p.degree(u) <= 3*d
                assert p.degree(r) <= d
                count += 1
    return count


def main():
    max_d = 12
    seeds = [(0, 1), (1, -1), (-2, 3), (-1, 1), (2, -8),
             (2, 1), (-79, 493048), (F(1, 2), F(-1, 8)),
             (F(-2, 3), F(1, 7))]
    certificates = []
    for seed in seeds:
        for d in range(max_d+1):
            points, curves, prefix, zero_indices = candidates(seed, d)
            powers = [(i, j) for i in range(d+1) for j in range(d+1-i)]
            N = (d+1)*(d+2)//2
            assert len(powers) == N
            for prime in (1009, 1013, 1019, 10007):
                selected, matrix = pivot_rows(points, powers, prime)
                if len(selected) == N:
                    det = determinant_mod(matrix, prime)
                    assert det != 0
                    break
            else:
                raise AssertionError((seed, d, 'no certificate; this is not a counterexample'))
            certificates.append(dict(seed=list(map(str, seed)), degree=d, prefix_L=prefix,
                candidate_bound=(d+2)*(3*d+1), filtered_count=len(points),
                selected_count=N, curves=curves, zero_outgoing_indices=zero_indices,
                prime=prime, determinant_mod_prime=det, selected_nm=selected,
                max_word_length=max(prefix+n+1+m for n, m in selected)))
    # The omitted origin hypothesis is necessary (except for constants).
    for d in range(max_d+1):
        powers = [(i, j) for i in range(d+1) for j in range(d+1-i)]
        selected, _ = pivot_rows([((n,m), (0,0)) for n in range(d+2)
                                 for m in range(3*d+1)], powers, 1009)
        assert len(selected) == 1
    # Omitting regularization fails: I*(I-c), degree six, vanishes on
    # all words with at most one L at a zero-invariant seed.
    for seed in ((1, -1), (-1, 1), (2, -8)):
        c = invariant(L(seed))
        for n in range(9):
            for m in range(19):
                t = orbit(L(orbit(seed, n)), m)
                assert invariant(t)*(invariant(t)-c) == 0
    result = dict(status='PASS', max_degree=max_d, nonzero_seeds=len(seeds),
        certified_cases=len(certificates), monomial_degree_checks=symbolic_checks(max_d),
        origin_rank=1, omission_of_regularization_counterexample_degree=6,
        interpretation='Finite exact certificates only. Universal results are proved separately.',
        certificates=certificates)
    path = Path(__file__).resolve().parents[1] / 'verification' / 'siphon-finite-determination' / 'python_certificates.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'certificates'}, indent=2))


if __name__ == '__main__':
    main()
