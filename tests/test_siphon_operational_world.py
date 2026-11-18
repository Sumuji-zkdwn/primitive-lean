"""Finite-field checks for the existing SiphonPolynomialE.E and OrbitTrace.linearE.

Each transition is evaluated in the original (u, v) coordinates. We compute
the observational partition from the transitions and the single readout u.
This computation stops at a fixed point, without assuming a depth bound.
"""

from itertools import product
import unittest


def siphon(point, p):
    u, v = point
    r = (v + u**3) % p
    x = (u + r**2) % p
    return (x, (r - x**3) % p)


def linear(point, p):
    u, v = point
    return (v, (v - u) % p)


def repeat(step, point, n, p):
    for _ in range(n):
        point = step(point, p)
    return point


def classify(states, key):
    # Canonical numbering by first occurrence allows exact partition comparison.
    labels = {}
    classes = {}
    for state in states:
        signature = key(state)
        classes[state] = labels.setdefault(signature, len(labels))
    return classes


def prediction_partitions(states, transitions):
    """Classes of agreement on every action word, by increasing depth."""
    classes = classify(states, lambda point: point[0])
    history = [classes]
    while True:
        def refined_key(point):
            after = tuple(classes[step[point]] for step in transitions)
            return (classes[point], after)

        updated = classify(states, refined_key)
        if updated == classes:
            return history
        classes = updated
        history.append(classes)


def rank_mod_prime(rows, p):
    pivots = {}
    for row in rows:
        for i in range(len(row)):
            entry = row[i]
            if entry == 0:
                continue
            if i not in pivots:
                inverse = pow(entry, -1, p)
                pivots[i] = [value * inverse % p for value in row]
                break
            row = [(a - entry * b) % p for a, b in zip(row, pivots[i])]
    return len(pivots)


class TestOperationalObservability(unittest.TestCase):
    primes = (2, 3, 5, 7, 11, 13, 17)

    def test_all_six_linear_powers(self):
        for p in self.primes:
            states = list(product(range(p), repeat=2))
            e = {point: siphon(point, p) for point in states}

            def folded(point):
                u, v = point
                return (u, (v + u**3) ** 2 % p)

            predicted_fold = classify(states, folded)
            predicted_full = classify(states, lambda point: point)
            fold_count = p**2 if p == 2 else p * (p + 1) // 2
            base = prediction_partitions(states, (e,))
            self.assertEqual([len(set(level.values())) for level in base], [p, fold_count])
            self.assertEqual(base[-1], predicted_fold)
            for k in range(6):
                with self.subTest(p=p, k=k):
                    lk = {point: repeat(linear, point, k, p) for point in states}
                    levels = prediction_partitions(states, (e, lk))
                    self.assertEqual(len(levels), 2)
                    if k in (0, 3):
                        self.assertEqual(levels[-1], predicted_fold)
                    else:
                        self.assertEqual(levels[-1], predicted_full)

    def test_reversal_in_original_coordinates(self):
        for p in self.primes:
            with self.subTest(p=p):
                for point in product(range(p), repeat=2):
                    u, v = point
                    half_turn = repeat(linear, point, 3, p)
                    self.assertEqual(half_turn, ((-u) % p, (-v) % p))
                    self.assertEqual(repeat(linear, point, 6, p), point)
                    h_e_h = repeat(linear, siphon(half_turn, p), 3, p)
                    self.assertEqual(siphon(h_e_h, p), point)
                    after_e_h = repeat(linear, siphon(point, p), 3, p)
                    self.assertEqual(repeat(linear, siphon(after_e_h, p), 3, p), point)

    def test_clock_period_in_characteristic_p(self):
        for p in self.primes:
            with self.subTest(p=p):
                for point in product(range(p), repeat=2):
                    u, v = point
                    r = (v + u**3) % p
                    current = point
                    orbit = set()
                    while current not in orbit:
                        orbit.add(current)
                        current = siphon(current, p)
                    self.assertEqual(current, point)
                    self.assertEqual(len(orbit), 1 if r == 0 else p)

    def test_integer_orbit_determines_polynomials_through_degree_five(self):
        # Full rank modulo p certifies a nonzero integer minor and hence full
        # rank over R for the same words applied to the integer seed.
        p = 1009
        degree = 5
        powers = [(i, j) for i in range(degree + 1) for j in range(degree + 1 - i)]
        for seed in ((0, 1), (1, -1), (-2, 3), (0, 0)):
            with self.subTest(seed=seed):
                start = seed
                if (seed[1] + seed[0]**3) % p == 0:
                    start = linear(seed, p)
                rows = []
                for _ in range(degree + 2):
                    point = linear(start, p)
                    for _ in range(3 * degree + 1):
                        u, v = point
                        rows.append([pow(u, i, p) * pow(v, j, p) % p for i, j in powers])
                        point = siphon(point, p)
                    start = siphon(start, p)
                expected = 1 if seed == (0, 0) else len(powers)
                self.assertEqual(rank_mod_prime(rows, p), expected)


if __name__ == "__main__":
    unittest.main()
