"""Independent numerical and exhaustive finite checks for the fixed-boundary bridge.

These tests are not Lean proofs. Fourier coefficients are represented exactly;
the endpoint and energy integrals use composite Simpson quadrature.
"""
from collections import deque
from fractions import Fraction
from math import cos, pi, sin
import unittest

COEFF = (
    (Fraction(1, 2), Fraction(-1, 4)),
    (Fraction(-1, 2), Fraction(1, 4)),
    (Fraction(-1, 2), Fraction(-1, 4)),
)


def angle(i, s):
    return sum(float(c) * sin(2 * pi * k * s)
               for k, c in enumerate(COEFF[i], 1))


def curvature(i, s):
    return sum(2 * pi * k * float(c) * cos(2 * pi * k * s)
               for k, c in enumerate(COEFF[i], 1))


def integrate(fn, n=4096):
    if n % 2:
        raise ValueError("Simpson quadrature needs an even number of steps")
    total = fn(0) + fn(1)
    total += 4 * sum(fn(k / n) for k in range(1, n, 2))
    total += 2 * sum(fn(k / n) for k in range(2, n, 2))
    return total / (3 * n)


def transition_monoid(transitions):
    """Enumerate all word transformations, stopping only at closure."""
    n = len(transitions[0])
    identity = tuple(range(n))
    seen = {identity}
    pending = deque([identity])
    while pending:
        current = pending.popleft()
        for transition in transitions:
            nxt = tuple(transition[current[i]] for i in range(n))
            if nxt not in seen:
                seen.add(nxt)
                pending.append(nxt)
    return seen


def partition(observations, transitions):
    monoid = transition_monoid(transitions)
    groups = []
    for x in range(len(observations)):
        for group in groups:
            if all(observations[t[x]] == observations[t[group[0]]]
                   for t in monoid):
                group.append(x)
                break
        else:
            groups.append([x])
    return groups


class FixedBoundaryIndependentChecks(unittest.TestCase):
    def test_endpoint_and_tangent_constraints(self):
        endpoints = []
        for i in range(3):
            self.assertAlmostEqual(angle(i, 0), 0, places=13)
            self.assertAlmostEqual(angle(i, 1), 0, places=13)
            x = integrate(lambda s: cos(angle(i, s)))
            y = integrate(lambda s: sin(angle(i, s)))
            endpoints.append((x, y))
            self.assertAlmostEqual(y, 0, places=12)
        for x, y in endpoints[1:]:
            self.assertAlmostEqual(x, endpoints[0][0], places=12)
            self.assertAlmostEqual(y, endpoints[0][1], places=12)
        self.assertAlmostEqual(endpoints[0][0], 0.9238658952594141, places=12)

    def test_distinct_angles_and_initial_curvatures(self):
        values = [angle(i, 1 / 8) for i in range(3)]
        for i in range(3):
            for j in range(i + 1, 3):
                self.assertGreater(abs(values[i] - values[j]), 1e-4)
        exact_kappa_over_pi = [
            2 * sum(k * c for k, c in enumerate(row, 1)) for row in COEFF
        ]
        self.assertEqual(exact_kappa_over_pi, [0, 0, -2])
        for i, exact in enumerate(exact_kappa_over_pi):
            self.assertAlmostEqual(curvature(i, 0), float(exact) * pi, places=12)

    def test_reconstructed_coordinate_curves_differ(self):
        # Reconstruct each curve at s=1/4, not merely its tangent-angle label.
        points = [
            tuple(integrate(lambda t: fun(angle(i, t / 4))) / 4
                  for fun in (cos, sin))
            for i in range(3)
        ]
        for i in range(3):
            for j in range(i + 1, 3):
                distance_sq = sum((a - b)**2 for a, b in zip(points[i], points[j]))
                self.assertGreater(distance_sq, 1e-6)

    def test_quadratic_bending(self):
        # Exact Fourier orthogonality gives integral(kappa**2) / pi**2.
        exact = [2 * sum((k * c) ** 2 for k, c in enumerate(row, 1))
                 for row in COEFF]
        self.assertEqual(exact, [1, 1, 1])
        for i in range(3):
            coarse = integrate(lambda s: curvature(i, s) ** 2, n=2048)
            fine = integrate(lambda s: curvature(i, s) ** 2, n=4096)
            self.assertAlmostEqual(coarse, fine, places=11)
            self.assertAlmostEqual(fine, pi**2, places=11)

    def test_complete_finite_quotients(self):
        observer_over_pi = (0, 0, -2)
        old = (0, 1, 2)
        fresh = (0, 2, 2)
        self.assertEqual(partition(observer_over_pi, [old]), [[0, 1], [2]])
        self.assertEqual(partition(observer_over_pi, [old, fresh]),
                         [[0], [1], [2]])
        self.assertEqual(partition(observer_over_pi, [old, old]), [[0, 1], [2]])
        self.assertEqual(len(transition_monoid([old, fresh])), 2)

    def test_original_four_direction_example(self):
        observer = (1, 0, -1, 0)
        reflection = (0, 3, 2, 1)
        turn = (1, 2, 3, 0)
        self.assertEqual(partition(observer, [reflection]), [[0], [1, 3], [2]])
        self.assertEqual(partition(observer, [reflection, turn]),
                         [[0], [1], [2], [3]])
        self.assertEqual((observer[turn[1]], observer[turn[3]]), (-1, 1))


if __name__ == "__main__":
    unittest.main(verbosity=2)
