"""Independent exhaustive checks for lean/Research/RadicalSquarefree.lean.

Python standard library only. For every n <= 20000 (trial-division factoring):

* rad(n) = n exactly when n = 0 or n is squarefree;
* rad(n) is squarefree and divides n, and every squarefree divisor of n divides
  rad(n) (checked for n <= 3000 over all divisors);
* rad(a b) = rad(a) rad(b) for coprime a, b <= 300;
* rad(12) = 6, rad(30) = 30, rad(72) = 6.
"""
from __future__ import annotations

import math
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'RadicalSquarefree.lean'
N = 20000


def prime_factors(n):
    out, p = set(), 2
    while p * p <= n:
        while n % p == 0:
            out.add(p)
            n //= p
        p += 1
    if n > 1:
        out.add(n)
    return out


def radical(n):
    return 0 if n == 0 else math.prod(prime_factors(n))


def squarefree(n):
    if n == 0:
        return False
    p = 2
    while p * p <= n:
        if n % (p * p) == 0:
            return False
        p += 1
    return True


class Census(unittest.TestCase):
    def test_fixed_points(self):
        fixed = 0
        for n in range(N + 1):
            r = radical(n)
            self.assertEqual(r == n, n == 0 or squarefree(n), n)
            fixed += r == n
            if n:
                self.assertTrue(squarefree(r))
                self.assertEqual(n % r, 0)
                self.assertEqual(radical(r), r)
        # 0 plus the squarefree numbers up to N (about 6/pi^2 of them)
        self.assertEqual(fixed, 1 + sum(squarefree(n) for n in range(1, N + 1)))

    def test_greatest_squarefree_divisor(self):
        for n in range(1, 3001):
            r = radical(n)
            for d in range(1, n + 1):
                if n % d == 0 and squarefree(d):
                    self.assertEqual(r % d, 0, (n, d))

    def test_multiplicative_on_coprime(self):
        for a in range(1, 301):
            for b in range(1, 301):
                if math.gcd(a, b) == 1:
                    self.assertEqual(radical(a * b), radical(a) * radical(b))

    def test_examples(self):
        self.assertEqual((radical(12), radical(30), radical(72)), (6, 30, 6))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('radical_squarefree', 'radical_eq_self_iff', 'range_radical',
                     'squarefree_dvd_radical', 'radical_mul_of_coprime', 'radical_examples'):
            self.assertIsNotNone(re.search(r'^theorem ' + name + r'\b', source, re.M), name)

    def test_definition_matches_joint_checker(self):
        source = LEAN.read_text(encoding='utf-8')
        joint = (ROOT / 'linear_input' / 'lean_check' / 'RadicalF0Bridge.inc').read_text(
            encoding='utf-8')
        body = 'def radical (n : ℕ) : ℕ :=\n  if n = 0 then 0 else ∏ p ∈ n.primeFactors, p'
        self.assertIn(body, source)
        self.assertIn(body, joint)


if __name__ == '__main__':
    unittest.main()
