"""Independent exact-integer tests of the polynomial predictive quotient."""
from itertools import product
import unittest


def invariant(state):
    u, v = state
    return v + u**3


def e_step(state):
    u, _ = state
    r = invariant(state)
    x = u + r**2
    return (x, r - x**3)


def r_step(state):
    u, v = state
    return (u, v + 1)


def mirror(state):
    u, _ = state
    return (u, -invariant(state) - u**3)


def signature(state):
    return (state[0], invariant(state)**2)


def trace(state, steps):
    ans = [state[0]]
    for _ in range(steps):
        state = e_step(state)
        ans.append(state[0])
    return tuple(ans)


def three_probe_readouts(state):
    return (state[0], e_step(state)[0], e_step(r_step(state))[0])


class PolynomialPredictiveQuotientTests(unittest.TestCase):
    def test_invariant_and_semiconjugacy(self):
        for state in product(range(-3, 4), repeat=2):
            r = invariant(state)
            self.assertEqual(invariant(e_step(state)), r)
            self.assertEqual(signature(e_step(state)),
                             (state[0] + r*r, r*r))

    def test_two_samples_predict_every_e_only_readout(self):
        states = list(product(range(-3, 4), repeat=2))
        for a in states:
            for b in states:
                self.assertEqual(signature(a) == signature(b),
                                 trace(a, 8) == trace(b, 8))

    def test_mirror_is_invisible_for_e_only_observations(self):
        for state in product(range(-3, 4), repeat=2):
            alt = mirror(state)
            self.assertEqual(mirror(alt), state)
            self.assertEqual(invariant(alt), -invariant(state))
            self.assertEqual(trace(state, 10), trace(alt, 10))
            if invariant(state):
                self.assertNotEqual(alt, state)

    def test_three_probe_readouts_identify_full_state(self):
        states = list(product(range(-3, 4), repeat=2))
        probes = [three_probe_readouts(s) for s in states]
        self.assertEqual(len(probes), len(set(probes)))
        for s in states:
            u, k_e, k_re = three_probe_readouts(s)
            r = (k_re - k_e - 1) // 2
            self.assertEqual(2*r, k_re - k_e - 1)
            self.assertEqual((u, r - u**3), s)

    def test_minimal_counterexample(self):
        a, b = (0, 1), (0, -1)
        self.assertEqual(signature(a), signature(b))
        self.assertEqual(trace(a, 6), trace(b, 6))
        self.assertEqual(three_probe_readouts(a), (0, 1, 4))
        self.assertEqual(three_probe_readouts(b), (0, 1, 0))


if __name__ == "__main__":
    unittest.main()
