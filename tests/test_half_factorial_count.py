"""Independent checks for lean/Research/HalfFactorialCount.lean.

Python standard library only. For every n = 4^r 6^s 9^t with r, s, t <= 8, all
factorizations of n into the atoms 4, 6, 9 are found by a separate recursive
search (choosing a non-increasing word of atoms that divides n), and their
number is compared with floor(min(v2(n), v3(n)) / 2) + 1, where the valuations
are computed by repeated division. The examples of the probe note are checked.
"""
from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'HalfFactorialCount.lean'
ATOMS = (9, 6, 4)


def valuation(n, p):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def factorizations(n, largest=9):
    if n == 1:
        return [()]
    out = []
    for atom in ATOMS:
        if atom <= largest and n % atom == 0:
            out += [(atom,) + rest for rest in factorizations(n // atom, atom)]
    return out


class Count(unittest.TestCase):
    def test_closed_form(self):
        checked = set()
        for r in range(9):
            for s in range(9):
                for t in range(9):
                    n = 4 ** r * 6 ** s * 9 ** t
                    if n in checked:
                        continue
                    checked.add(n)
                    words = factorizations(n)
                    a, b = valuation(n, 2), valuation(n, 3)
                    self.assertEqual(len(words), min(a, b) // 2 + 1, n)
                    self.assertEqual(len({len(w) for w in words}), 1, n)  # half-factorial
        self.assertGreater(len(checked), 200)

    def test_examples(self):
        self.assertEqual([len(factorizations(n)) for n in (36, 216, 1296, 46656)], [2, 2, 3, 4])

    def test_outside_g(self):
        self.assertEqual(factorizations(8), [])
        self.assertEqual(factorizations(12 * 5), [])


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('card_counts_eq', 'card_counts_eq_factorization',
                     'card_factorizations_eq', 'card_sol', 'value_eq_iff', 'example_counts'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
