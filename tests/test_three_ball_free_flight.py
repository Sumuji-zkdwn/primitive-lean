"""Independent checks for lean/ThreeBallFreeFlight.lean.

Python standard library only (fractions). A separate event-driven simulation of
three hard balls on a line (masses 1, 2, 1, initial velocities 1, 0, -1, free
gaps a, b) advances the actual centre positions rather than the gaps, detects
the next contact, applies the binary elastic impact, and stops when the balls
separate. For many rational a != b it checks the closed forms proved in Lean:
contact order LRL / RLR, contact times min(a,b) + {0, 3d/5, 6d}, the other gap
d, 3d/5, 9d at each contact, and the final velocities.
"""
from __future__ import annotations

import itertools
import re
import unittest
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'ThreeBallFreeFlight.lean'
RHO = F(1, 2)
MASS = (1, 2, 1)


def impact(v, i):
    """Elastic impact between balls i and i+1."""
    m1, m2 = MASS[i], MASS[i + 1]
    u1, u2 = v[i], v[i + 1]
    w1 = ((m1 - m2) * u1 + 2 * m2 * u2) / (m1 + m2)
    w2 = ((m2 - m1) * u2 + 2 * m1 * u1) / (m1 + m2)
    out = list(v)
    out[i], out[i + 1] = F(w1), F(w2)
    return out


def simulate(a, b, limit=10):
    x = [-2 * RHO - a, F(0), 2 * RHO + b]
    v = [F(1), F(0), F(-1)]
    t = F(0)
    events = []
    for _ in range(limit):
        candidates = []
        for i in (0, 1):
            gap = x[i + 1] - x[i] - 2 * RHO
            rate = v[i + 1] - v[i]
            if rate < 0:
                candidates.append((gap / -rate, i))
        if not candidates:
            return events, v, t
        candidates.sort()
        if len(candidates) == 2 and candidates[0][0] == candidates[1][0]:
            return events + ['simultaneous'], v, t
        tau, i = candidates[0]
        x = [xi + tau * vi for xi, vi in zip(x, v)]
        t += tau
        other = 1 - i
        other_gap = x[other + 1] - x[other] - 2 * RHO
        events.append(('L' if i == 0 else 'R', t, other_gap))
        v = impact(v, i)
    raise AssertionError('no separation')


class Schedules(unittest.TestCase):
    def test_closed_forms(self):
        values = [F(n, d) for n in range(1, 9) for d in (1, 2, 3, 7)]
        checked = 0
        for a, b in itertools.permutations(sorted(set(values)), 2):
            events, v, t = simulate(a, b)
            lo, d = min(a, b), abs(b - a)
            first, second = ('L', 'R') if a < b else ('R', 'L')
            self.assertEqual([e[0] for e in events], [first, second, first])
            self.assertEqual([e[1] for e in events], [lo, lo + 3 * d / 5, lo + 6 * d])
            self.assertEqual([e[2] for e in events], [d, 3 * d / 5, 9 * d])
            if a < b:
                self.assertEqual(v, [F(-13, 27), F(-10, 27), F(11, 9)])
            else:
                self.assertEqual(v, [F(-11, 9), F(10, 27), F(13, 27)])
            self.assertEqual(sum(m * w for m, w in zip(MASS, v)), 0)
            self.assertEqual(sum(m * w * w for m, w in zip(MASS, v)), 2)
            checked += 1
        self.assertGreater(checked, 500)

    def test_equal_gaps_are_simultaneous(self):
        self.assertEqual(simulate(F(1), F(1))[0], ['simultaneous'])


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('left_first_schedule', 'right_first_schedule', 'flight_gaps_nonneg',
                     'separated_gaps_never_close', 'outcome_separated_iff',
                     'equal_gaps_simultaneous', 'middle_velocity_jump'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
