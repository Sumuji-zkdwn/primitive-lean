"""Finite-graph diagnostic for a proposed radial Laakso metric estimate.

Checks d_phi <= 2 Omega_s(d_0) on every ordered pair of vertices of
the first three ternary-gate quotients, for three different reparametrizations.
Float/inverse-bisection only: NOT a continuum proof or doubling certificate.
Python stdlib only.
"""
from heapq import heappush, heappop
from math import inf


def good(s):
    return s / 2 if s <= 1 / 3 else 1 / 6 + 1.25 * (s - 1 / 3)


def power2(s):
    return s * s


def F_bad(z):
    if z <= 0:
        return 0.
    if z >= 1 / 6:
        return 1 / 3 + 0.8 * (z - 1 / 6)
    n = 1
    while 6. ** (-(n + 1)) > z:
        n += 1
    a, b = 6. ** (-(n + 1)), 6. ** (-n)
    t, ell = z - a, b - a
    H = 1.6 * (2 ** n - 1)
    area = t * t / ell if t <= ell / 2 else ell / 2 - (ell - t) ** 2 / ell
    return 3. ** (-(n + 1)) + 0.8 * t + H * area


def bad(s):
    if s <= 0:
        return 0.
    if s >= 1:
        return 1.
    lo, hi = 0., 1.
    for _ in range(64):
        mid = (lo + hi) / 2
        if F_bad(mid) < s:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def graph_at(n, phi):
    M, sheets = 3 ** n, 2 ** n
    g = [[] for _ in range((M + 1) * sheets)]
    h = [j / M for j in range(M + 1)]
    z = [phi(t) for t in h]
    def edge(a, b, w):
        g[a].append((b, w))
        g[b].append((a, w))
    for j in range(M):
        for bits in range(sheets):
            edge(j * sheets + bits, (j + 1) * sheets + bits, z[j + 1] - z[j])
    for j in range(1, M):
        v, p = j, 0
        while v % 3 == 0:
            v //= 3
            p += 1
        mask = 1 << p
        for bits in range(sheets):
            if not bits & mask:
                edge(j * sheets + bits, j * sheets + (bits ^ mask), 0.)
    return g, h, sheets


def dijkstra(g, source):
    d = [inf] * len(g)
    d[source] = 0.
    heap = [(0., source)]
    while heap:
        du, u = heappop(heap)
        if du > d[u] + 1e-14:
            continue
        for v, w in g[u]:
            dv = du + w
            if dv + 1e-14 < d[v]:
                d[v] = dv
                heappush(heap, (dv, v))
    return d


def audit(n, phi, label):
    raw, hs, sheets = graph_at(n, lambda s: s)
    gauged, _, _ = graph_at(n, phi)
    count, excess, lower_ratio = 0, 0., 0.
    for i in range(len(raw)):
        s = hs[i // sheets]
        d0, d1 = dijkstra(raw, i), dijkstra(gauged, i)
        for j in range(len(raw)):
            if d0[j] < 1e-11:
                assert d1[j] < 1e-11
                continue
            omega = phi(min(1., s + d0[j])) - phi(max(0., s - d0[j]))
            excess = max(excess, d1[j] - 2 * omega)
            if d1[j] > 1e-11:
                lower_ratio = max(lower_ratio, omega / d1[j])
            count += 1
    assert excess < 2e-12, (label, n, excess)
    print(label, n, count, "max Omega/d_phi", round(lower_ratio, 6))
    return count


if __name__ == "__main__":
    total = sum(audit(n, phi, name)
                for name, phi in (("good", good), ("power2", power2), ("bad", bad))
                for n in (1, 2, 3))
    assert total == 153972
    print("PASS:", total, "finite ordered pairs. Not a continuum proof.")
