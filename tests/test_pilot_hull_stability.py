"""Finite exhaustive oracle for orbit-hull stability iff all images fit.

This is a set-closure model, not a proof about IUT log-shells or p-adic hulls.
"""
from itertools import product
import unittest


GRID = tuple(product(range(3), repeat=2))


def hull(points):
    if not points:
        return set()
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    return set(product(
        range(min(xs), max(xs) + 1),
        range(min(ys), max(ys) + 1),
    ))


def swap(points):
    return {(y, x) for x, y in points}


class HullStabilityTests(unittest.TestCase):
    def test_exact_iff_on_every_subset_of_3_by_3_grid(self):
        for mask in range(1 << len(GRID)):
            original = {p for n, p in enumerate(GRID) if (mask >> n) & 1}
            images = (original, swap(original))
            union = set().union(*images)
            stable = all(image <= hull(original) for image in images)
            actual = hull(union) == hull(original)
            self.assertEqual(actual, stable, (mask, original))
            self.assertTrue(hull(original) <= hull(union))
            self.assertLessEqual(len(hull(original)), len(hull(union)))

    def test_explicit_escaping_image_obstructs_equality(self):
        original = {(0, 0), (2, 1)}
        self.assertFalse(swap(original) <= hull(original))
        self.assertNotEqual(hull(original | swap(original)), hull(original))
        self.assertGreater(len(hull(original | swap(original))), len(hull(original)))

    def test_stable_image_keeps_hull(self):
        original = {(0, 0), (1, 1)}
        self.assertTrue(swap(original) <= hull(original))
        self.assertEqual(hull(original | swap(original)), hull(original))


if __name__ == "__main__":
    unittest.main()
