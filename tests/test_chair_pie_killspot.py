"""Independent regression tests for the chair/pie finite gate model.

Run: python -m unittest discover -s tests -p test_chair_pie_killspot.py
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))

from chair_pie_killspot import (  # noqa: E402
    Economy, MODELS, blocking_sets, enabling_sets, revenue_possible,
    shortest_revenue_path, verify, verify_all_monotone_boolean_functions,
)


class ChairPieKillSpotTests(unittest.TestCase):
    def test_known_minimal_sets(self):
        cases = (
            ((('chair', 'demand'),), (('chair',), ('demand',))),
            ((('chairA', 'demandA'), ('chairB', 'demandB')),
             (('chairA', 'chairB'), ('chairA', 'demandB'),
              ('chairB', 'demandA'), ('demandA', 'demandB'))),
            ((('buyer', 'chairA'), ('buyer', 'chairB')),
             (('buyer',), ('chairA', 'chairB'))),
            ((('demand',),), (('demand',),)),
        )
        for economy, (expected_enablers, expected_blockers) in zip(MODELS, cases):
            with self.subTest(economy=economy.label):
                self.assertEqual(
                    set(enabling_sets(economy)),
                    {frozenset(e) for e in expected_enablers},
                )
                self.assertEqual(
                    set(blocking_sets(economy)),
                    {frozenset(b) for b in expected_blockers},
                )
                verify(economy)

    def test_growth_only_does_not_remove_external_gate(self):
        for n in (0, 1, 3, 8, 30):
            model = Economy('threshold', ('chair', 'buyer'),
                            (('chair', 'buyer'),), threshold=n)
            self.assertEqual(enabling_sets(model),
                             (frozenset({'chair', 'buyer'}),))
            self.assertFalse(revenue_possible(model, frozenset()))
            path, _ = shortest_revenue_path(model, frozenset(model.gates))
            self.assertIsNotNone(path)
            self.assertEqual(len(path), n + 3)

    def test_empty_and_unconditional_channels(self):
        empty = Economy('no channels', ('chair',), ())
        unconditional = Economy('free channel', ('chair',), ((),))
        self.assertEqual(enabling_sets(empty), ())
        self.assertEqual(blocking_sets(empty), (frozenset(),))
        self.assertEqual(enabling_sets(unconditional), (frozenset(),))
        self.assertEqual(blocking_sets(unconditional), ())
        verify(empty)
        verify(unconditional)

    def test_self_made_chair_not_self_made_demand(self):
        economy = MODELS[3]
        self.assertFalse(revenue_possible(economy, frozenset()))
        self.assertTrue(revenue_possible(economy, frozenset({'demand'})))
        path, _ = shortest_revenue_path(economy, frozenset({'demand'}))
        self.assertIn('internal:make-chair', path)
        self.assertIn('external:demand', path)

    def test_all_monotone_four_gate_functions(self):
        self.assertEqual(verify_all_monotone_boolean_functions(4), 168)


if __name__ == '__main__':
    unittest.main()
