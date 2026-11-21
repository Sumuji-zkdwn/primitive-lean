"""Check diffusive-time witnesses, one-step observations and exact 2×2 Bayes risks."""

from collections import defaultdict
from fractions import Fraction
from functools import partial
from itertools import product
from math import comb
import unittest

from clock_avalanche_witness import verify
from square_clock import add_one, burns, instruments, observe


class ClockAvalancheTests(unittest.TestCase):
    def test_diffusive_time_examples(self):
        for m, mass, low, high in [(2, 158, 95, 158), (3, 1938, 1449, 2124)]:
            with self.subTest(m=m):
                row = verify(m)
                self.assertEqual(row['initial_mass_each'], mass)
                self.assertEqual(row['prefix_firings_each'], low)
                self.assertEqual(row['last_left_totals'], [low, high])
                self.assertEqual(row['last_right_totals'], [high, low])

    def test_every_one_step_observation(self):
        for m in (2, 3):
            modulus, adjacent, clock, masks = instruments(m)
            n = modulus - 1
            reading = partial(observe, modulus=modulus, clock=clock, masks=masks)
            gap = n * n - 1
            columns = [2] + [3**k for k in range(1, m)]
            observations = set()
            for selected in product((False, True), repeat=m):
                for j in range(modulus):  # j=0 makes no correction to the angle.
                    with self.subTest(m=m, selected=selected, j=j):
                        base = [3] * (n * n)
                        for column, take in zip(columns, selected):
                            base[column - 1] -= int(take)
                        if j:
                            base[3 * n + j - 1] -= 2
                        a, b = base.copy(), base.copy()
                        a[0] = a[n + n // 2 - 1] = 1
                        b[n - 1] = b[n + n // 2] = 1
                        self.assertTrue(burns(a, adjacent) and burns(b, adjacent))
                        self.assertEqual(sum(a), sum(b))
                        output = reading(a)
                        self.assertEqual(output, reading(b))
                        observations.add(output)
                        for site, expected in [(0, (0, gap)), (n - 1, (gap, 0))]:
                            x, fa = add_one(a, site, adjacent)
                            y, fb = add_one(b, site, adjacent)
                            self.assertEqual(reading(x), reading(y))
                            x, ga = add_one(x, site, adjacent)
                            y, gb = add_one(y, site, adjacent)
                            self.assertEqual(reading(x), reading(y))
                            self.assertEqual((fa + ga, fb + gb), expected)
            self.assertEqual(observations, set(product(range(modulus), range(2**m))))

    def test_uniform_recurrent_bayes_risks(self):
        modulus, adjacent, clock, masks = instruments(1)
        states = [s for s in product(range(4), repeat=4) if burns(s, adjacent)]
        self.assertEqual(len(states), 192)
        mae, mse = Fraction(), Fraction()
        for left in range(10):
            # Abelianity gives the same total for every order with this left count.
            sites = [0] * (2 * left) + [1] * (2 * (9 - left))
            groups = defaultdict(list)
            for start in states:
                state, total = start, 0
                for site in sites:
                    state, fired = add_one(state, site, adjacent)
                    total += fired
                # Known inputs translate the initial clock and bits deterministically.
                groups[sum(start), observe(start, modulus, clock, masks)].append(total)
            self.assertEqual(len(groups), 24)
            weight = Fraction(comb(9, left), 2**9 * len(states))
            for counts in groups.values():
                median = sorted(counts)[len(counts) // 2]
                mean = Fraction(sum(counts), len(counts))
                mae += weight * sum(abs(x - median) for x in counts)
                mse += weight * sum((x - mean)**2 for x in counts)
        self.assertEqual(mae, Fraction(29005, 49152))
        self.assertEqual(mse, Fraction(2828358109, 4428103680))


if __name__ == '__main__':
    unittest.main()
