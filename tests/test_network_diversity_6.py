"""Cross-check six-vertex finite data without relying on Lean proofs."""
import contextlib
import io
import json
import unittest

from tools import network_diversity_6


class NetworkDiversitySixVertexTest(unittest.TestCase):
    def test_full_finite_certificate(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            network_diversity_6.run()
        result = json.loads(output.getvalue())
        self.assertEqual(result["six_vertex_six_edge_enumeration"]["connected_graphs"], 3660)
        self.assertEqual(result["input_graphs"]["A"]["distance_sum"], 27)
        self.assertEqual(result["input_graphs"]["B"]["distance_sum"], 29)
        self.assertEqual(result["status"], "All executable assertions passed; no Lean proof claimed")


if __name__ == "__main__":
    unittest.main()
