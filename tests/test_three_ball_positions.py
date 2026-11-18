"""Exact regression checks for positive-gap realizations of #80 collision words."""
from fractions import Fraction as Q
import unittest

from tools.check_three_ball_positions import (
    V0, audit, check_pair, momentum, twice_energy,
    next_event, simulate, symbolic_affine_certificate,
)


class ThreeBallPositionReentryTests(unittest.TestCase):
    def test_symbolic_all_positive_gaps(self):
        self.assertTrue(symbolic_affine_certificate())

    def test_left_first_exact_times_and_gaps(self):
        r = check_pair(Q(2), Q(3))
        self.assertEqual(''.join(e['side'] for e in r['events']), 'LRL')
        self.assertEqual([e['time'] for e in r['events']], [Q(2), Q(13, 5), Q(8)])
        self.assertEqual(r['final_gaps'], (Q(0), Q(9)))

    def test_right_first_exact_times_and_gaps(self):
        r = check_pair(Q(3), Q(2))
        self.assertEqual(''.join(e['side'] for e in r['events']), 'RLR')
        self.assertEqual([e['time'] for e in r['events']], [Q(2), Q(13, 5), Q(8)])
        self.assertEqual(r['final_gaps'], (Q(9), Q(0)))

    def test_collision_accumulation_at_one_sided_offsets(self):
        for n in (1, 2, 3, 6, 12):
            d = Q(1, 10**n)
            left = check_pair(Q(1), Q(1)+d)
            right = check_pair(Q(1)+d, Q(1))
            self.assertEqual(left['events'][-1]['time'], Q(1)+6*d)
            self.assertEqual(right['events'][-1]['time'], Q(1)+6*d)
            self.assertEqual(right['final_velocity'][1] - left['final_velocity'][1], Q(20,27))

    def test_approaching_and_separating_binary_impacts(self):
        for a,b in ((Q(1,4),Q(7,3)),(Q(7,3),Q(1,4))):
            r = check_pair(a,b)
            for e in r['events']:
                v=e['before']
                self.assertGreater(v[0]-v[1] if e['side']=='L' else v[1]-v[2],0)
                self.assertEqual(momentum(e['before']),momentum(e['after']))
                self.assertEqual(twice_energy(e['before']),twice_energy(e['after']))
                self.assertGreater(e['gaps'][0 if e['side']=='R' else 1],0)
            v=r['final_velocity']
            self.assertLess(v[0],v[1])
            self.assertLess(v[1],v[2])
            self.assertIsNone(next_event(r['final_gaps'],v))

    def test_simultaneous_unassigned(self):
        with self.assertRaises(ValueError): simulate(Q(1),Q(1))
        with self.assertRaises(ValueError): simulate(Q(0),Q(1))
        with self.assertRaises(AssertionError): next_event((Q(0),Q(1)),V0)

    def test_independent_finite_grid(self):
        result=audit()
        self.assertTrue(result['passed'])
        self.assertEqual(result['distinct_positive_gap_pairs_tested'],992)


if __name__ == '__main__':
    unittest.main()
