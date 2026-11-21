"""CI entry points for bounded exact forgetting/round-trip certificates.

These run the research enumerations rather than mock or repeat their internals.
The results certify the stated finite examples, not a Lean compilation or a
neural/physical mechanism.
"""

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from forgetting_roundtrips import (
    finite_field_audit,
    graph_audit,
    kernel_audit,
    real_sample_audit,
    relation_audit,
    relay_audit,
)


class ForgettingRoundTripTests(unittest.TestCase):
    def test_relational_conditions_and_converse_counterexample(self):
        report = relation_audit()
        self.assertEqual(report, {
            "surjection_decoder_pairs": 384,
            "fgf_equals_f": 18,
            "gfg_equals_g": 174,
            "both": 18,
            "two_by_two_relations": 16,
            "difunctional_two_by_two_relations": 12,
        })

    def test_exact_kernel_bounds_and_marginal_recovery_counterexample(self):
        report = kernel_audit()
        self.assertEqual(report["rational_kernel_pairs"], 600)
        self.assertEqual(report["marginal_recovery_counterexample_states"], 7)
        self.assertEqual(report["marginal_tv"], "0")
        self.assertEqual(report["individual_success"], "1/7")

    def test_real_initial_conditions_do_not_form_a_closed_state_space(self):
        report = real_sample_audit()
        self.assertEqual(
            (report["initial_states"], report["coarse_classes"],
             report["probe_classes"]),
            (15, 9, 15),
        )
        self.assertEqual(report["fiber_sizes"], {1: 3, 2: 6})
        self.assertEqual(report["E_images_outside_initial_set"], 8)
        self.assertEqual(report["uniform_optimal_recovery"], "3/5")
        self.assertAlmostEqual(report["conditional_bits"], 0.8)
        self.assertEqual(report["representative_decoder_omits"], 6)
        self.assertEqual(report["unconstrained_r_mse"], "2")
        self.assertEqual(report["consistent_r_mse"], "4")

    def test_five_element_field_is_a_closed_finite_system(self):
        report = finite_field_audit()
        self.assertEqual(report["field_prime"], 5)
        self.assertEqual(
            (report["states"], report["coarse_classes"], report["probe_classes"]),
            (25, 15, 25),
        )
        self.assertTrue(report["E_and_R_closed_permutations"])
        self.assertEqual(report["uniform_optimal_recovery"], "3/5")
        self.assertAlmostEqual(report["conditional_bits"], 0.8)

    def test_quotient_graph_shortcut_has_no_original_path_lift(self):
        report = graph_audit()
        self.assertEqual(report["vertices_before_after"], [6, 5])
        self.assertEqual(report["max_degree_before_after"], [2, 4])
        self.assertEqual(report["distance_2_5_before_after"], [3, 2])
        self.assertFalse(report["quotient_shortcut_has_original_lift"])

    def test_relay_keeps_some_history_without_recording_all_history(self):
        report = relay_audit()
        self.assertTrue(report["same_current_input_distinct_mask_states"])
        self.assertFalse(report["all_input_histories_injectively_recorded"])


if __name__ == "__main__":
    unittest.main()
