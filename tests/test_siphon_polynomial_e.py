"""Independent exact-integer checks for the existing polynomial shear map E.

No Lean functions are imported. Unlike the earlier endpoint-only model,
the map retains a nonconstant polynomial invariant while changing state.
"""
import itertools
import unittest


def invariant(u, v):
    return v + u ** 3


def E(u, v):
    r = invariant(u, v)
    x = u + r ** 2
    return x, r - x ** 3


def inverse_E(x, y):
    r = invariant(x, y)
    u = x - r ** 2
    return u, r - u ** 3


def jacobian_det(u, v):
    r = invariant(u, v)
    x = u + r ** 2
    dx_du = 1 + 6 * u ** 2 * r
    dx_dv = 2 * r
    dy_du = 3 * u ** 2 - 3 * x ** 2 * dx_du
    dy_dv = 1 - 3 * x ** 2 * dx_dv
    return dx_du * dy_dv - dx_dv * dy_du


def iterate_E(state, n):
    for _ in range(n):
        state = E(*state)
    return state


def exact_iterate(u, v, n):
    r = invariant(u, v)
    x = u + n * r ** 2
    return x, r - x ** 3


class PolynomialEChecks(unittest.TestCase):
    def test_invariant_and_inverse(self):
        for u, v in itertools.product(range(-3, 4), repeat=2):
            self.assertEqual(invariant(*E(u, v)), invariant(u, v))
            self.assertEqual(inverse_E(*E(u, v)), (u, v))
            self.assertEqual(E(*inverse_E(u, v)), (u, v))

    def test_actual_derivative_determinant(self):
        for u, v in itertools.product(range(-3, 4), repeat=2):
            self.assertEqual(jacobian_det(u, v), 1)

    def test_iterate_closed_form(self):
        for u, v in itertools.product(range(-3, 4), repeat=2):
            for n in range(10):
                self.assertEqual(iterate_E((u, v), n),
                                 exact_iterate(u, v, n))
                self.assertEqual(invariant(*iterate_E((u, v), n)),
                                 invariant(u, v))

    def test_invariant_not_pointwise_stasis(self):
        self.assertEqual(E(1, 0), (2, -7))
        self.assertEqual(invariant(1, 0), invariant(2, -7))
        self.assertNotEqual(E(1, 0), (1, 0))

    def test_other_interaction_may_break_invariant(self):
        # Volume preservation alone does not preserve this particular I:
        # elementary shear R(u,v)=(u,v+1) has det DR = 1.
        self.assertNotEqual(invariant(1, 1), invariant(1, 2))


if __name__ == "__main__":
    unittest.main()
