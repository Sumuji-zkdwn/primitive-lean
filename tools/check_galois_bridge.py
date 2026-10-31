"""Exact-arithmetic smoke tests for GaloisChebyshev.inc (NOT a Lean proof check).

Run: python -B -X utf8 tools/check_galois_bridge.py
"""
from fractions import Fraction


def joukowski(z):
    return (z + 1 / z) / 2


def check_algebra():
    xs = [Fraction(x) for x in (-8, -3, -2, -1, 1, 2, 3, 8)]
    checks = 0
    for a in xs:
        assert 4 * joukowski(a) ** 3 - 3 * joukowski(a) == joukowski(a ** 3)
        for b in xs:
            assert (joukowski(a) - joukowski(b)) * (2 * a * b) == (
                (a - b) * (a * b - 1)
            )
            assert (joukowski(a) == joukowski(b)) == (a == b or a * b == 1)
            checks += 1
    return checks


def check_critical_reflections():
    for n in range(6):
        m = 3 ** n
        zero = lambda j: (-j) % m
        pi = lambda j: (-j - 1) % m
        for reflect in (zero, pi):
            assert all(reflect(reflect(j)) == j for j in range(m))
            orbits = {tuple(sorted({j, reflect(j)})) for j in range(m)}
            assert len(orbits) == (m + 1) // 2
        for j in range(m):
            for k in range(m):
                zero_same = j == k or j + k == m
                pi_same = j == k or j + k + 1 == m
                assert zero_same == (zero(j) == zero(k) or j == zero(k))
                assert pi_same == (pi(j) == pi(k) or j == pi(k))


if __name__ == "__main__":
    count = check_algebra()
    check_critical_reflections()
    print(f"PASS: {count} exact rational pairs; critical reflections for m=3^0..3^5")
