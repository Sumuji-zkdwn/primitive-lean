"""Exact integer check of the normalized A/B curve-letter example.

This implementation uses Python integers and tuple states, independently of
the Lean structure and theorem statements in the companion .inc source.
"""
import itertools
import unittest

# S=(z, alpha, F): z=(Re z, Im z) in xi=2h/(3pi) units,
# alpha in pi/2 turns, and F in c0=pi^2/(8h) units.
A = ((3, 3), 1, 1)
B = ((-1, 1), 3, 9)


def rotate_quarter(turns, z):
    x, y = z
    for _ in range(turns):
        x, y = -y, x
    return x, y


def join(left, right):
    z, alpha, cost = left
    w, beta, other_cost = right
    rw = rotate_quarter(alpha, w)
    return ((z[0] + rw[0], z[1] + rw[1]),
            alpha + beta, cost + other_cost)


def observe(state):
    z, alpha, cost = state
    return z[0], alpha, cost


class CurveLetterContextTest(unittest.TestCase):
    def test_exact_states(self):
        self.assertEqual(join(A, B), ((2, 2), 4, 10))
        self.assertEqual(join(B, A), ((2, -2), 4, 10))
        self.assertEqual(join(A, join(A, B)), ((1, 5), 5, 11))
        self.assertEqual(join(A, join(B, A)), ((5, 5), 5, 11))

    def test_original_readout_collides_but_left_context_separates(self):
        ab = join(A, B)
        ba = join(B, A)
        self.assertEqual(observe(ab), (2, 4, 10))
        self.assertEqual(observe(ba), (2, 4, 10))
        self.assertNotEqual(observe(join(A, ab)), observe(join(A, ba)))
        self.assertEqual(observe(join(A, ab)), (1, 5, 11))
        self.assertEqual(observe(join(A, ba)), (5, 5, 11))

    def test_associativity_on_all_letter_triples(self):
        for a, b, c in itertools.product((A, B), repeat=3):
            self.assertEqual(join(join(a, b), c), join(a, join(b, c)))

    def test_noncommutativity_witness(self):
        self.assertNotEqual(join(A, B), join(B, A))


if __name__ == "__main__":
    unittest.main()

