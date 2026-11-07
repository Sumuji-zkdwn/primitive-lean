"""Independent finite arithmetic sanity checks; Lean is the proof authority."""

import unittest
from math import prod


def support(n):
    if n == 0:
        return set()
    result = set()
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.add(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.add(n)
    return result


def radical(n):
    return 0 if n == 0 else prod(support(n))


class RadicalF0Tests(unittest.TestCase):
    def test_zero_one_and_idempotence(self):
        self.assertEqual(radical(0), 0)
        self.assertEqual(radical(1), 1)
        for n in range(1, 1025):
            with self.subTest(n=n):
                self.assertEqual(radical(radical(n)), radical(n))

    def test_kernel_is_prime_support(self):
        for x in range(1, 81):
            for y in range(1, 81):
                self.assertEqual(
                    radical(x) == radical(y),
                    support(x) == support(y),
                )

    def test_successor_obstruction(self):
        self.assertEqual(radical(2), radical(4))
        self.assertEqual(radical(3), 3)
        self.assertEqual(radical(5), 5)
        self.assertNotEqual(radical(2 + 1), radical(4 + 1))

    def test_squarefree_fixed_points(self):
        for n in range(1, 513):
            squarefree = all(n % (p * p) != 0 for p in support(n))
            self.assertEqual(radical(n) == n, squarefree)


if __name__ == "__main__":
    unittest.main()
