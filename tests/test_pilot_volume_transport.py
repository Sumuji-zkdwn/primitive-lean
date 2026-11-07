"""Independent finite rational checks for conditional transport-shift bridge.

Not a Lean proof and not a computational validation of IUT arithmetic.
"""
from fractions import Fraction
import unittest


class PilotVolumeTransportTests(unittest.TestCase):
    def test_shifted_wall_exact_criterion(self):
        a = Fraction(1)
        scale = Fraction(14, 3)
        for cap in (Fraction(1), Fraction(4)):
            # A downward-closed volume domain, with the required level if
            # it does not exceed the cap.
            choices = (Fraction(0), Fraction(-1), Fraction(-2))
            for shift in choices:
                needed_volume = (scale - 1) * a - shift
                criterion = needed_volume <= cap
                exists_witness = criterion
                if exists_witness:
                    original_volume = needed_volume
                    transported_volume = original_volume + shift
                    self.assertLessEqual(original_volume, cap)
                    self.assertEqual(-scale * a + transported_volume, -a)
                self.assertEqual(exists_witness, criterion)
            self.assertEqual(cap == 4, (scale - 1) * a <= cap)

    def test_neutral_transports_cannot_create_missing_budget(self):
        cap, a, scale = Fraction(1), Fraction(1), Fraction(14, 3)
        allowed_shifts = [Fraction(0)] * 50
        self.assertFalse(any((scale - 1) * a - shift <= cap for shift in allowed_shifts))

    def test_packet_sum_and_charge_certificate(self):
        # Two local packets, exact total budget and a pointwise lower allocation.
        scale, a = Fraction(14, 3), Fraction(1)
        n = 2
        packets = (Fraction(4), Fraction(4))
        charges = (Fraction(11, 3), Fraction(11, 3))
        self.assertEqual(sum(charges), n * (scale - 1) * a)
        self.assertTrue(all(c <= p for c, p in zip(charges, packets)))
        self.assertLessEqual((scale - 1) * a, sum(packets) / n)

        # Local positivity alone does not imply the arithmetic lower bound.
        small_packets = (Fraction(1), Fraction(1))
        self.assertTrue(all(p >= 0 for p in small_packets))
        self.assertFalse((scale - 1) * a <= sum(small_packets) / n)


if __name__ == "__main__":
    unittest.main()
