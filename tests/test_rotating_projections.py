"""Numerical regressions for lean/RotatingProjections.lean.

These floating-point checks simulate the projections directly. They complement,
but do not replace, the universal Lean proofs.
"""

import math
import random
import unittest


def project(theta, v):
    c, s = math.cos(theta), math.sin(theta)
    a = v[0] * c + v[1] * s
    return (a * c, a * s)


def run(steps, v, theta0=0.0):
    angle = theta0
    trace = [v]
    for step in steps:
        angle += step
        v = project(angle, v)
        trace.append(v)
    return trace


def half_turn(n):
    return run([math.pi / n] * n, (1.0, 0.0))


class RotatingProjectionTests(unittest.TestCase):
    def assertVec(self, got, want, tol=1e-12):
        self.assertAlmostEqual(got[0], want[0], delta=tol)
        self.assertAlmostEqual(got[1], want[1], delta=tol)

    def test_exact_small_cases(self):
        self.assertVec(half_turn(2)[-1], (0.0, 0.0))
        self.assertVec(half_turn(3)[-1], (-1 / 8, 0.0))
        self.assertVec(half_turn(4)[-1], (-1 / 4, 0.0))

    def test_four_step_trace(self):
        want = [(1, 0), (1 / 2, 1 / 2), (0, 1 / 2), (-1 / 4, 1 / 4), (-1 / 4, 0)]
        for got, w in zip(half_turn(4), want):
            self.assertVec(got, w)

    def test_closed_form_and_hundred(self):
        for n in range(1, 400):
            got = half_turn(n)[-1]
            self.assertVec(got, (-math.cos(math.pi / n) ** n, 0.0), tol=1e-9)
        amplitude = math.cos(math.pi / 100) ** 100
        self.assertAlmostEqual(amplitude, 0.95184, delta=5e-6)
        # Intensity (squared length), as for polarisers, is a different number.
        self.assertAlmostEqual(amplitude ** 2, 0.90600, delta=5e-5)

    def test_bounds(self):
        for n in range(3, 2000):
            a = math.cos(math.pi / n) ** n
            self.assertLessEqual(1 - math.pi ** 2 / (2 * n), a + 1e-15)
            self.assertLessEqual(a, 1.0)

    def test_bending_bound_and_equal_steps(self):
        rng = random.Random(20261109)
        for _ in range(2000):
            n = rng.randint(1, 12)
            steps = [rng.uniform(-1, 1) for _ in range(n)]
            prod = math.prod(math.cos(d) for d in steps)
            self.assertLessEqual(1 - sum(d * d for d in steps) / 2, prod + 1e-15)
            steps = [rng.uniform(-math.pi / 2, math.pi / 2) for _ in range(n)]
            prod = math.prod(math.cos(d) for d in steps)
            self.assertLessEqual(prod, math.cos(sum(steps) / n) ** n + 1e-15)

    def test_absorption_and_failures(self):
        rng = random.Random(7)
        for _ in range(200):
            steps = [rng.uniform(-2, 2) for _ in range(rng.randint(1, 8))]
            v = (rng.uniform(-3, 3), rng.uniform(-3, 3))
            w = project(steps[0], v)
            self.assertVec(run(steps, w)[-1], run(steps, v)[-1], tol=1e-9)
        q = math.pi / 4
        self.assertVec(project(0, project(q, (1, 0))), (1 / 2, 0))
        self.assertVec(project(q, project(0, (1, 0))), (1 / 2, 1 / 2))
        once = half_turn(4)[-1]
        twice = run([q] * 4, once)[-1]
        self.assertVec(twice, (1 / 16, 0))


if __name__ == "__main__":
    unittest.main()
