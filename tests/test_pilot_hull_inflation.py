"""Finite oracle for the independent hull-inflation control model.

A coordinatewise box hull is only an analogy for possible Ind2 hull growth;
no IUT arithmetic or p-adic measure is tested by this script.
"""
import unittest


def vol(rect):
    return rect[0] * rect[1]


def swap(rect):
    return rect[1], rect[0]


def hull(a, b):
    return max(a[0], b[0]), max(a[1], b[1])


class PilotHullInflationTests(unittest.TestCase):
    def test_swap_preserves_each_individual_area(self):
        for width in range(8):
            for height in range(8):
                r = width, height
                self.assertEqual(vol(swap(r)), vol(r))
                self.assertEqual(swap(swap(r)), r)

    def test_hull_dominates_and_can_strictly_inflate(self):
        for width in range(8):
            for height in range(8):
                r = width, height
                h = hull(r, swap(r))
                self.assertGreaterEqual(vol(h), vol(r))
        example = 2, 1
        self.assertEqual(vol(example), 2)
        self.assertEqual(vol(hull(example, swap(example))), 4)

    def test_square_controls_no_inflation(self):
        for n in range(8):
            sq = n, n
            self.assertEqual(vol(hull(sq, swap(sq))), vol(sq))


if __name__ == "__main__":
    unittest.main()
