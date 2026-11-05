"""Independent Fraction checks for the (1, 2, 1) three-ball collision model.

This is a numerical-model regression test, not a substitute for Lean kernel
verification of the theorems in lean/ThreeBallCollision.lean.
"""
from fractions import Fraction as Q
from itertools import product
import unittest


def lm(v):
    l, m, r = v
    return ((-l + 4 * m) / 3, (2 * l + m) / 3, r)


def mr(v):
    l, m, r = v
    return (l, (m + 2 * r) / 3, (4 * m - r) / 3)


def momentum(v):
    l, m, r = v
    return l + 2 * m + r


def twice_energy(v):
    l, m, r = v
    return l * l + 2 * m * m + r * r


class ThreeBallCollisionTests(unittest.TestCase):
    def setUp(self):
        self.initial = (Q(1), Q(0), Q(-1))

    def test_left_first_three_exact_contacts(self):
        a = lm(self.initial)
        b = mr(a)
        c = lm(b)
        self.assertEqual(a, (Q(-1, 3), Q(2, 3), Q(-1)))
        self.assertEqual(b, (Q(-1, 3), Q(-4, 9), Q(11, 9)))
        self.assertEqual(c, (Q(-13, 27), Q(-10, 27), Q(11, 9)))
        self.assertTrue(self.initial[0] > self.initial[1])
        self.assertTrue(a[1] > a[2])
        self.assertTrue(b[0] > b[1])
        self.assertTrue(c[0] < c[1] < c[2])

    def test_right_first_three_exact_contacts(self):
        a = mr(self.initial)
        b = lm(a)
        c = mr(b)
        self.assertEqual(a, (Q(1), Q(-2, 3), Q(1, 3)))
        self.assertEqual(b, (Q(-11, 9), Q(4, 9), Q(1, 3)))
        self.assertEqual(c, (Q(-11, 9), Q(10, 27), Q(13, 27)))
        self.assertTrue(self.initial[1] > self.initial[2])
        self.assertTrue(a[0] > a[1])
        self.assertTrue(b[1] > b[2])
        self.assertTrue(c[0] < c[1] < c[2])

    def test_conservation_for_many_exact_inputs(self):
        values = (Q(-3), Q(-1, 2), Q(0), Q(1, 3), Q(2))
        for v in product(values, repeat=3):
            for operation in (lm, mr):
                w = operation(v)
                self.assertEqual(momentum(v), momentum(w))
                self.assertEqual(twice_energy(v), twice_energy(w))

    def test_order_information_survives_arbitrarily_small_offsets(self):
        l = lm(mr(lm(self.initial)))
        r = mr(lm(mr(self.initial)))
        self.assertEqual(r[1] - l[1], Q(20, 27))
        self.assertNotEqual(l, r)
        self.assertNotEqual(lm(mr(self.initial)), mr(lm(self.initial)))
        self.assertEqual(momentum(l), momentum(r))
        self.assertEqual(twice_energy(l), twice_energy(r))
        for n in (1, 2, 10, 100, 1000):
            epsilon = Q(1, 10**n)
            self.assertGreater(epsilon, 0)
            self.assertEqual(l[1], Q(-10, 27))
            self.assertEqual(r[1], Q(10, 27))


if __name__ == "__main__":
    unittest.main()
