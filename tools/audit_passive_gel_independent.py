"""Independent, read-only finite audit of primitive-lean PR #183/#217.

Usage: python passive_gel_independent_audit.py
Requires sympy, numpy and scipy. Nothing is written to GitHub.

This checks: a full 3-site energy law, exact reduced/full Hessians,
4--8 vertex ground-state counts and gaps, an 8-site cube, a positive-energy
metastable bump with pinned ends, and two pinned 4-site transient trajectories.
It is NOT a Lean kernel proof or a particle-physics validation.
"""
from collections import deque
from itertools import combinations, product
from math import comb, factorial, sqrt

import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

z = sp.symbols('z', real=True)
W = z**2 * (z**2 - 1)**2
W1, W2 = sp.diff(W, z), sp.diff(W, z, 2)


def mat_for_edges(n, edges):
    mat = sp.zeros(len(edges), n)
    for i, (u, v) in enumerate(edges):
        mat[i, u], mat[i, v] = -1, 1
    return mat


def path(n): return [(j, j + 1) for j in range(n - 1)]


def cycle(n): return path(n) + [(n - 1, 0)]


def complete(n): return list(combinations(range(n), 2))


def cube_edges():
    coordinates = list(product((0, 1), repeat=3))
    return [(i, j) for i in range(8) for j in range(i + 1, 8)
            if sum(abs(p - q) for p, q in zip(coordinates[i], coordinates[j])) == 1]


def exact_three_site():
    B = mat_for_edges(3, path(3))
    x = sp.Matrix([0, 1, 0])
    strain = B * x
    assert list(strain) == [1, -1]
    assert sum(W.subs(z, q) for q in strain) == 0
    assert B.T * sp.Matrix([W1.subs(z, q) for q in strain]) == sp.zeros(3, 1)
    H = B.T * sp.diag(*[W2.subs(z, q) for q in strain]) * B
    assert sorted(H.eigenvals()) == [0, 8, 24]
    # Include the internal memory coordinates for b=1, kappa arbitrary (delta=0).
    b = sp.Integer(1)
    Hfull = sp.BlockMatrix([[(8 + b) * B.T * B, -b * B.T],
                            [-b * B, b * sp.eye(2)]]).as_explicit()
    eigen_set = {0, 5 - sp.sqrt(17), 5 + sp.sqrt(17),
                 14 - 2 * sp.sqrt(43), 14 + 2 * sp.sqrt(43)}
    assert set(Hfull.eigenvals()) == eigen_set
    assert all(float(q) > 0 for q in eigen_set if q != 0)

    # Independent full ODE energy derivative in 3 nodes, not only the edge identity.
    X = sp.Matrix(sp.symbols('x0:3', real=True))
    V = sp.Matrix(sp.symbols('v0:3', real=True))
    h = sp.Matrix(sp.symbols('h0:2', real=True))
    rho, bb, kappa, gamma = sp.symbols('rho bb kappa gamma', positive=True)
    eps, delta = B * X, B * X - h
    g = delta.applyfunc(lambda q: bb * q + kappa * q**3)
    sig = eps.applyfunc(lambda q: W1.subs(z, q)) + g
    kinetic = rho * V.dot(V) / 2
    energy = kinetic + sum(W.subs(z, q) for q in eps) + sum(
        bb * q**2 / 2 + kappa * q**4 / 4 for q in delta)
    rates = list(V) + list(-B.T * sig / rho) + list(gamma * g)
    variables = list(X) + list(V) + list(h)
    edot = sum(sp.diff(energy, u) * du for u, du in zip(variables, rates))
    assert sp.expand(edot + gamma * g.dot(g)) == 0

    # Linearized relaxation+inertia: two shape eigenmodes of B^T B.
    for lam in (1, 3):
        # rho=b=gamma=1; growth exponents are roots of s^3+s^2+9*lam*s+8*lam.
        roots = np.roots([1, 1, 9 * lam, 8 * lam])
        assert np.all(roots.real < -1e-5), roots
    print('PASS exact 3-site energy, gradient, Hessians, full energy law and stable shape modes')


def zero_well_states(n, edges):
    adjacency = [[] for _ in range(n)]
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    visited, queue = {0}, deque([0])
    tree = []
    while queue:
        u = queue.popleft()
        for v in adjacency[u]:
            if v not in visited:
                tree.append((u, v))
                visited.add(v)
                queue.append(v)
    assert len(tree) == n - 1
    states = []
    for deltas in product((-1, 0, 1), repeat=n - 1):
        x = [0] * n
        for (u, v), d in zip(tree, deltas):
            x[v] = x[u] + d
        if all(abs(x[v] - x[u]) <= 1 for u, v in edges):
            states.append(x)
    return states


def weighted_hessian(n, edges, configuration):
    H = np.zeros((n, n))
    for u, v in edges:
        strain = configuration[v] - configuration[u]
        curvature = {0: 2, -1: 8, 1: 8}[int(strain)]
        H[u, u] += curvature
        H[v, v] += curvature
        H[u, v] -= curvature
        H[v, u] -= curvature
    return H


def graph_tests():
    print('n  path  cycle complete  path_spike_smallest_positive_Hessian')
    for n in range(4, 9):
        pp = zero_well_states(n, path(n))
        cc = zero_well_states(n, cycle(n))
        kk = zero_well_states(n, complete(n))
        central_trinomial = sum(factorial(n) // (factorial(j)**2 * factorial(n - 2*j))
                                 for j in range(n // 2 + 1))
        assert len(pp) == 3**(n-1)
        assert len(cc) == central_trinomial
        assert len(kk) == 2**n-1
        spike = np.zeros(n, dtype=int)
        spike[1] = 1
        hessian = weighted_hessian(n, path(n), spike)
        eig = np.linalg.eigvalsh(hessian)
        assert abs(eig[0]) < 1e-10 and eig[1] > 0
        assert eig[1] + 1e-10 >= 2 * (2 - 2 * np.cos(np.pi / n))
        print(f'{n:>1} {len(pp):>5} {len(cc):>6} {len(kk):>8} {eig[1]:>21.12f}')

    cube = cube_edges()
    states = zero_well_states(8, cube)
    assert len(cube) == 12 and len(states) == 495
    spike = np.zeros(8, dtype=int)
    spike[0] = 1
    eig = np.linalg.eigvalsh(weighted_hessian(8, cube, spike))
    assert abs(eig[0]) < 1e-10 and eig[1] > 4
    print(f'PASS cube Q3: {len(states)} states; smallest positive spike Hessian eigenvalue {eig[1]:.12f}')


def pinned_positive_energy_minimum():
    a = sp.Rational(1,10)
    d = sp.sqrt(1 - 3*a/2)
    s_plus = sp.sqrt((2 + d)/3)
    s_minus = sp.sqrt((2 - d)/3)
    potential = lambda val: W.subs(z, val) + a*val**2/2
    fprime = W1 + a*z
    fsecond = W2 + a
    assert sp.simplify(fprime.subs(z,s_plus)) == 0
    assert sp.simplify(fprime.subs(z,s_minus)) == 0
    assert float(fsecond.subs(z,s_plus)) > 0
    assert float(fsecond.subs(z,s_minus)) < 0
    barrier = sp.simplify(2*(potential(s_minus)-potential(s_plus)))
    assert sp.simplify(barrier - 8*d**3/27) == 0
    print(f'PASS pinned a=0.1: s+={float(s_plus):.12f}, E+={float(2*potential(s_plus)):.12f}, '
          f'barrier={float(barrier):.12f}')


def transient_hopping():
    B = np.array(mat_for_edges(4, path(4)), dtype=float)
    def energy(y):
        u, v, ud, vd = y[:4]
        eps = B @ np.array([0, u, v, 0])
        delta = eps - y[4:]
        return (ud*ud+vd*vd)/2 + np.sum(eps**2*(eps**2-1)**2 + delta**2/2)
    def ode(t, y):
        u, v, ud, vd = y[:4]
        eps = B @ np.array([0, u, v, 0])
        delta = eps - y[4:]
        stress = 6*eps**5-8*eps**3+2*eps + delta
        force = -B.T @ stress
        return np.r_[ud, vd, force[1:3], 5*delta]
    for s in (0.7, 1.4):
        x0 = np.array([0., 1., 0., 0.])
        y0 = np.r_[1.,0.,-s/sqrt(2),s/sqrt(2), B@x0]
        sol = solve_ivp(ode, (0, 150), y0, method='DOP853',
                        rtol=1e-10, atol=1e-12, max_step=0.12)
        assert sol.success
        final = sol.y[:2, -1]
        target = np.array([1.,0.]) if s == 0.7 else np.array([0.,1.])
        assert np.linalg.norm(final - target) < 1e-4
        assert energy(sol.y[:, -1]) < 1e-10
        print(f'PASS pinned 4-site impulse s={s:.1f}: E_initial={energy(y0):.6f}, '
              f'(u,v)_final={np.array2string(final, precision=8)}')


if __name__ == '__main__':
    exact_three_site()
    graph_tests()
    pinned_positive_energy_minimum()
    transient_hopping()
    print('ALL INDEPENDENT CHECKS PASSED (numerics are not Lean proofs)')