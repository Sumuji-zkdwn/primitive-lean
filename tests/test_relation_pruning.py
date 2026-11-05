"""Small regression tests for observable edge pruning; no Lean proof claims."""
import itertools
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from relation_pruning import (
    GraphSpace, analyze_pruning, curve_walk, encode_edges, graph_machine,
    parse_actions, parse_observation,
)
from shortest_cross_trace import shortest_word, verify_certificate


class RelationPruningTests(unittest.TestCase):
    def setUp(self):
        self.s = GraphSpace(("A", "B", "C"))
        self.triangle = self.s.to_mask(self.s.universe)
        self.all_deletes = parse_actions(self.s,
                                        ("delete:A-B", "delete:A-C", "delete:B-C"))

    def run_prune(self, observation="connected", operators=None):
        return analyze_pruning(self.s, self.triangle,
                               parse_observation(self.s, observation),
                               self.all_deletes if operators is None else operators)

    @staticmethod
    def removed(report, names):
        return next(row for row in report["candidates"]
                    if set(row["deleted"]) == set(names))

    def test_triangle_current_only_removes_exactly_one_edge(self):
        report = self.run_prune(operators=parse_actions(self.s, ("stay",)))
        self.assertEqual(report["candidate_count"], 8)
        self.assertEqual(report["minimum_retained_count"], 2)
        self.assertEqual(len(report["minimum_retention"]), 3)
        for deleted in ("A-B", "A-C", "B-C"):
            item = self.removed(report, (deleted,))
            self.assertTrue(item["current_observation_preserved"])
            self.assertTrue(item["all_action_words_preserved"])
            self.assertIsNone(item["shortest_distinguishing_word"])

    def test_triangle_delayed_failure_for_ac_removal(self):
        report = self.run_prune()
        item = self.removed(report, ("A-C",))
        self.assertTrue(item["current_observation_preserved"])
        self.assertFalse(item["all_action_words_preserved"])
        self.assertEqual(item["shortest_distinguishing_word"], ["delete:A-B"])
        self.assertEqual(item["shortest_length"], 1)
        self.assertEqual([x["left_output"] for x in item["witness_trace"]], [True, True])
        self.assertEqual([x["right_output"] for x in item["witness_trace"]], [True, False])
        self.assertTrue(item["certificate_verified"])

    def test_triangle_all_deletes_force_keep_every_edge(self):
        report = self.run_prune()
        self.assertEqual(report["minimum_retention"], [["A-B", "A-C", "B-C"]])
        self.assertEqual(sum(1 for row in report["candidates"]
                             if row["all_action_words_preserved"]), 1)
        for edge in ("A-B", "A-C", "B-C"):
            item = self.removed(report, (edge,))
            self.assertTrue(item["current_observation_preserved"])
            self.assertEqual(item["shortest_length"], 1)

    def test_restrict_operations_can_make_ab_disposable(self):
        only_ab = parse_actions(self.s, ("delete:A-B",))
        report = self.run_prune(operators=only_ab)
        self.assertEqual(report["minimum_retention"], [["A-C", "B-C"]])
        self.assertTrue(self.removed(report, ("A-B",))["all_action_words_preserved"])
        self.assertFalse(self.removed(report, ("A-C",))["all_action_words_preserved"])

    def test_select_direct_edge_observation_removes_two_other_edges(self):
        report = self.run_prune("edge:A-B")
        self.assertEqual(report["minimum_retention"], [["A-B"]])
        item = self.removed(report, ("A-C", "B-C"))
        self.assertTrue(item["all_action_words_preserved"])
        self.assertIsNone(item["curve_walk"])  # C isolated: no single graph-edge walk
        self.assertEqual(item["exact_addition_word"], ["add:A-B"])

    def test_initial_mismatch_has_empty_shortest_word(self):
        report = self.run_prune()
        item = self.removed(report, ("A-B", "A-C"))
        self.assertFalse(item["current_observation_preserved"])
        self.assertEqual(item["shortest_distinguishing_word"], [])
        self.assertEqual(item["shortest_length"], 0)

    def test_four_vertex_failure_requires_two_deletions(self):
        s = GraphSpace(("A", "B", "C", "D"))
        complete = s.to_mask(s.universe)
        trimmed = complete & ~s.bit(s.parse_edge("A-C"))
        operators = parse_actions(s, ("delete:" + "-".join(edge) for edge in s.universe))
        obs = parse_observation(s, "connected")
        m = graph_machine(s, obs, operators)
        names = tuple(a.label for a in operators)
        result = shortest_word(m, m, names, (complete, trimmed))
        self.assertTrue(verify_certificate(m, m, names, (complete, trimmed), result))
        self.assertEqual(result["status"], "counterexample")
        self.assertEqual(result["length"], 2)
        self.assertEqual(set(result["word"]), {"delete:A-B", "delete:A-D"})

    def test_curve_walk_encodes_exact_edges_in_connected_graphs(self):
        self.assertEqual(curve_walk(self.s, self.triangle), ["A", "B", "C", "A"])
        path = self.triangle & ~self.s.bit(self.s.parse_edge("A-C"))
        self.assertEqual(curve_walk(self.s, path), ["A", "B", "C"])
        for mask in range(1 << len(self.s.universe)):
            walk = curve_walk(self.s, mask)
            if walk is None:
                self.assertGreater(len(self.s.partition(mask)), 1)
                continue
            walked = {self.s.parse_edge(u + "-" + v)
                      for u, v in zip(walk, walk[1:])}
            self.assertEqual(walked, set(self.s.edges(mask)))
            self.assertLessEqual(len(walk) - 1, 2 * len(self.s.edges(mask)))

    def test_operator_word_is_exact_on_all_subgraphs(self):
        for mask in range(1 << len(self.s.universe)):
            word = encode_edges(self.s, mask)
            actions = parse_actions(self.s, word) if word else ()
            current = 0
            for action in actions:
                current = action.apply(self.s, current)
            self.assertEqual(current, mask)

    def test_no_spurious_edge_from_non_eulerian_curve(self):
        s = GraphSpace(("A", "B", "C", "D"))
        star = s.to_mask((s.parse_edge("A-B"), s.parse_edge("A-C"),
                          s.parse_edge("A-D")))
        walk = curve_walk(s, star)
        self.assertEqual(walk, ["A", "B", "A", "C", "A", "D", "A"])
        self.assertEqual({s.parse_edge(u + "-" + v)
                          for u, v in zip(walk, walk[1:])}, set(s.edges(star)))

    def test_invalid_edges_and_operations_are_rejected(self):
        with self.assertRaises(ValueError):
            self.s.parse_edge("A-A")
        with self.assertRaises(ValueError):
            self.s.parse_edge("A-D")
        with self.assertRaises(ValueError):
            parse_actions(self.s, ("delete:A-B", "delete:B-A"))
        with self.assertRaises(ValueError):
            parse_observation(self.s, "unknown")


if __name__ == "__main__":
    unittest.main()
