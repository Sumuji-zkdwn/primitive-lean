"""Finite standard-library audit for the delayed-aether research ledger.

Checks selected mathematical witnesses; not the complete v1--v10 simulations.
No GR, Lorentzian continuum limit, or Lean proof is claimed.
"""
from itertools import combinations, product, permutations
from math import acos, exp, log, pi, sqrt, tanh
from random import Random
import json

RNG = Random(20261122)
PAIRS = ((0, 1), (0, 2), (1, 2))


def plaquettes(L):
    return {(p, x): 0 for p in PAIRS for x in product(range(L), repeat=3)}


def edges(L):
    return {(i, x): 0 for i in range(3) for x in product(range(L), repeat=3)}


def shift(x, i, L):
    y = list(x)
    y[i] = (y[i] + 1) % L
    return tuple(y)


def d1(a, L):
    B = plaquettes(L)
    for i, j in PAIRS:
        for x in product(range(L), repeat=3):
            B[(i, j), x] = (a[i, x] ^ a[j, x] ^
                             a[i, shift(x, j, L)] ^ a[j, shift(x, i, L)])
    return B


def d2(B, L):
    return {x: (B[(0, 1), x] ^ B[(0, 1), shift(x, 2, L)] ^
                B[(0, 2), x] ^ B[(0, 2), shift(x, 1, L)] ^
                B[(1, 2), x] ^ B[(1, 2), shift(x, 0, L)])
            for x in product(range(L), repeat=3)}


def xor(A, B):
    return {key: A[key] ^ B[key] for key in A}


def representative(L, pair):
    B = plaquettes(L)
    i, j = pair
    for x in product(range(L), repeat=3):
        if x[i] == 0 and x[j] == 0:
            B[pair, x] = 1
    return B


def flux(B, L):
    charges = []
    for i, j in PAIRS:
        other = ({0, 1, 2} - {i, j}).pop()
        charge = 0
        for x in product(range(L), repeat=3):
            if x[other] == 0:
                charge ^= B[(i, j), x]
        charges.append(charge)
    return tuple(charges)


def check_z2():
    counter = 0
    for L in (2, 3, 4):
        reps = [representative(L, p) for p in PAIRS]
        assert all(not any(d2(B, L).values()) for B in reps)
        assert all(sum(B.values()) == L for B in reps)
        for sector in range(8):
            B = plaquettes(L)
            for i, rep in enumerate(reps):
                if (sector >> i) & 1:
                    B = xor(B, rep)
            Q = tuple((sector >> i) & 1 for i in range(3))
            assert flux(B, L) == Q and not any(d2(B, L).values())
            for _ in range(30):
                a = edges(L)
                for key in a:
                    a[key] = RNG.randrange(2)
                delta = d1(a, L)
                assert not any(d2(delta, L).values()), 'd2 d1 != 0'
                successor = xor(B, delta)
                assert flux(successor, L) == Q
                assert sum(successor.values()) >= L * max(Q)
                # Exact mixed time/spatial cube Bianchi identity.
                assert xor(xor(successor, B), delta) == plaquettes(L)
                B = successor
                counter += 1
    return {'checked_updates': counter, 'sectors': 8, 'lattice_lengths': [2, 3, 4]}


OUTER = ((1., 1., 1.), (-1., -1., 1.),
         (-1., 1., -1.), (1., -1., -1.))
TETS = [tuple(sorted((4,) + c)) for c in combinations(range(4), 3)]


def distance(a, b):
    return sqrt(sum((x-y)**2 for x, y in zip(a, b)))


def edge(a, b, r):
    if a == 4:
        return r[b]
    if b == 4:
        return r[a]
    return distance(OUTER[a], OUTER[b])


def angle(tet, ab, r):
    a, b = ab
    c, d = [v for v in tet if v not in ab]
    x, y, z = edge(a, b, r), edge(a, c, r), edge(a, d, r)
    bc, bd, cd = edge(b, c, r), edge(b, d, r), edge(c, d, r)
    ec = (x*x + y*y - bc*bc)/2
    ed = (x*x + z*z - bd*bd)/2
    cdot = (y*y + z*z - cd*cd)/2
    v = (cdot - ec*ed/x**2) / sqrt((y*y - ec**2/x**2)*(z*z - ed**2/x**2))
    return acos(max(-1, min(1, v)))


def deficits(r):
    return [2*pi - sum(angle(tet, (4, i), r) for tet in TETS if i in tet)
            for i in range(4)]


def jacobian(r, eps=1e-5):
    return [[(deficits([r[k] + (eps if k == j else 0) for k in range(4)])[i] -
               deficits([r[k] - (eps if k == j else 0) for k in range(4)])[i])/(2*eps)
             for j in range(4)] for i in range(4)]


def determinant4(A):
    det = 0.
    for p in permutations(range(4)):
        sign = (-1)**sum(p[i] > p[j] for i in range(4) for j in range(i+1,4))
        value = 1.
        for i in range(4):
            value *= A[i][p[i]]
        det += sign*value
    return det


def check_regge():
    base = [sqrt(3)]*4
    assert max(abs(v) for v in deficits(base)) < 1e-12
    J = jacobian(base)
    assert max(abs(v-3) for row in J for v in row) < 1e-7
    for _ in range(100):
        center = [RNG.uniform(-.15, .15) for _ in range(3)]
        r = [distance(v, center) for v in OUTER]
        assert max(abs(v) for v in deficits(r)) < 1e-12
    curved = base.copy()
    curved[0] *= 1.08
    dc = deficits(curved)
    det = determinant4(jacobian(curved))
    assert min(dc) > 0 and abs(det) > .01
    return {'flat_jacobian_entry': J[0][0],
            'curved_jacobian_determinant': det,
            'curved_deficits': dc}


def check_intrinsic_fan():
    def deficit(c):
        return 2*pi - 6*acos(1 - 1/(2*c*c))
    assert abs(deficit(1)) < 1e-12
    assert deficit(.9) < 0 < deficit(1.1)
    return {'flat': deficit(1), 'short_edges': deficit(.9),
            'long_edges': deficit(1.1)}


def check_tt():
    # Wave direction is (0,0,k); the only TT modes are xx=-yy and xy=yx.
    def TT(A):
        a = (A[0][0]-A[1][1])/2
        b = (A[0][1]+A[1][0])/2
        return [[a,b,0],[b,-a,0],[0,0,0]]
    zero = [[0,0,0],[0,0,0],[0,0,0]]
    assert TT([[1,0,0],[0,1,0],[0,0,1]]) == zero
    for _ in range(100):
        u = [RNG.uniform(-1,1) for _ in range(3)]
        k = (0,0,1)
        strain = [[u[i]*k[j]+u[j]*k[i] for j in range(3)] for i in range(3)]
        assert TT(strain) == zero
    return {'displacement_strain_tests': 100, 'TT_modes': 2}


def check_memory():
    k, delta, a = .3, 3., .3
    def psi(y):
        return (k+delta)*y*y/2-delta*a*a*log((exp(y/a)+exp(-y/a))/2)
    for n in range(-300,301):
        y = n/100
        stiff = k+delta*tanh(y/a)**2
        assert k-1e-12 <= stiff <= k+delta+1e-12
        assert psi(y) >= -1e-10
    return {'points':601,'stiffness_lower':k,'stiffness_upper':k+delta}


def main():
    audit = {'Z2_flux': check_z2(), 'Regge_tetra': check_regge(),
             'intrinsic_fan': check_intrinsic_fan(),
             'TT_projection': check_tt(), 'bounded_memory': check_memory()}
    print(json.dumps(audit, indent=2))
    print('PASS: selected finite tests (not the complete ten-run archive).')


if __name__ == '__main__':
    main()
