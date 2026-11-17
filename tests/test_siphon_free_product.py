"""Bounded census of reduced words in L and T = E ∘ L³.

Different modular images certify different integer polynomial maps over ℝ.
The census covers all reduced words through twelve syllables.
"""

import unittest

from test_siphon_operational_world import linear, repeat, siphon


L_POWERS = ("L", "L^2", "L^3", "L^4", "L^5")
# At length 2j (j ≥ 1) there are 2 · 5^j words, and at length 2j+1 there are 6 · 5^j.
COUNTS = (1, 6, 10, 30, 50, 150, 250, 750, 1250, 3750, 6250, 18750, 31250)


def extensions(word, images, p):
    """Append one syllable in execution order and update each seed's image."""
    if not word or word[-1] != "T":
        turned = tuple(siphon(repeat(linear, point, 3, p), p) for point in images)
        yield word + ("T",), turned
    if not word or word[-1] == "T":
        rotated = images
        for power in L_POWERS:
            rotated = tuple(linear(point, p) for point in rotated)
            yield word + (power,), rotated


class TestSiphonFreeProduct(unittest.TestCase):
    def check_census(self, seeds, p):
        start = tuple((u % p, v % p) for u, v in seeds)
        seen = {start: ()}
        frontier = [((), start)]
        counts = [1]
        for _ in range(1, len(COUNTS)):
            next_frontier = []
            for word, images in frontier:
                for extended, result in extensions(word, images, p):
                    if result in seen:
                        self.fail(f"Modulo {p}, {extended} and {seen[result]} both give {result}")
                    seen[result] = extended
                    next_frontier.append((extended, result))
            counts.append(len(next_frontier))
            frontier = next_frontier
        self.assertEqual(tuple(counts), COUNTS)
        self.assertEqual(len(seen), 62_497)

    def test_four_seeds(self):
        seeds = ((0, 1), (1, 0), (1, 1), (2, -1))
        for p in (1009, 10007):
            with self.subTest(p=p):
                self.check_census(seeds, p)

    def test_single_integer_seed(self):
        for p in (1_000_003, 1_000_000_007):
            with self.subTest(p=p):
                self.check_census(((3, 6),), p)


if __name__ == "__main__":
    unittest.main()
