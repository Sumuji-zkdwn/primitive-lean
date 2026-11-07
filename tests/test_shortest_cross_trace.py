"""Regression and exhaustive checks for finite cross-system certificates."""
import itertools
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from shortest_cross_trace import (
    Machine, analyze_mapping, demo, read_machine, shortest_word,
    verify_certificate,
)


def run_case(data):
    actions = tuple(data["actions"])
    a, b = read_machine(data["left"], actions), read_machine(data["right"], actions)
    start = tuple(data["initial"])
    result = shortest_word(a, b, actions, start)
    assert verify_certificate(a, b, actions, start, result)
    return actions, a, b, start, result


class ShortestCrossTraceTests(unittest.TestCase):
    def test_two_action_delayed_failure(self):
        acts, a, b, start, result = run_case(demo("delayed_failure"))
        self.assertEqual(result["word"], ["toggle_hidden", "reveal_hidden"])
        self.assertEqual(result["length"], 2)
        self.assertEqual([row["left_output"] for row in result["trace"]], [0, 0, 1])
        report = analyze_mapping(a, b, acts, (0, 0, 1, 1))
        self.assertFalse(report["strict_state_bridge"])
        self.assertFalse(report["observationally_sound_for_every_source_state"])
        self.assertEqual(report["shortest_failure_over_all_sources"]["source_state"], 1)
        self.assertEqual(report["shortest_failure_over_all_sources"]["word"], ["reveal_hidden"])

    def test_safe_forgetting_has_reachable_bisimulation(self):
        acts, a, b, start, result = run_case(demo("valid_forgetting"))
        self.assertEqual(result["status"], "equivalent")
        self.assertEqual(result["reachable_pairs"], [[0, 0], [2, 1]])
        self.assertTrue(analyze_mapping(a, b, acts, (0, 0, 1, 1))["strict_state_bridge"])

    def test_noncommuting_raw_states_can_be_observationally_equal(self):
        a = Machine((0, 0), ((1, 1),))
        b = Machine((0, 0), ((1, 1),))
        result = analyze_mapping(a, b, ("tick",), (1, 0))
        self.assertFalse(result["strict_state_bridge"])
        self.assertTrue(result["observationally_sound_for_every_source_state"])

    def test_empty_word_witness(self):
        a = Machine((0,), ((0,),))
        b = Machine((1,), ((0,),))
        self.assertEqual(shortest_word(a, b, ("stay",), (0, 0))["word"], [])

    def test_incomplete_machine_rejected(self):
        a = Machine((0, 1), ((0, 1),))
        b = Machine((0, 1), ())
        with self.assertRaises(ValueError):
            shortest_word(a, b, ("x",), (0, 0))

    def test_duplicate_action_rejected(self):
        a = Machine((0,), ((0,), (0,)))
        with self.assertRaises(ValueError):
            shortest_word(a, a, ("x", "x"), (0, 0))

    def test_forged_certificates_rejected(self):
        acts, a, b, start, r = run_case(demo("delayed_failure"))
        self.assertFalse(verify_certificate(a, b, acts, start,
                         {**r, "word": ["reveal_hidden"], "length": 1}))
        acts, a, b, start, r = run_case(demo("valid_forgetting"))
        self.assertFalse(verify_certificate(a, b, acts, start,
                         {**r, "reachable_pairs": [[0, 0]]}))

    def test_exhaustive_two_states_two_actions_vs_all_short_words(self):
        actions = ("a", "b")
        moves = tuple(itertools.product((0, 1), repeat=2))
        for la in itertools.product((0, 1), repeat=2):
            for lb in itertools.product((0, 1), repeat=2):
                for sa in itertools.product(moves, repeat=2):
                    a = Machine(la, sa)
                    for sb in itertools.product(moves, repeat=2):
                        b = Machine(lb, sb)
                        for initial in itertools.product((0, 1), repeat=2):
                            answer = shortest_word(a, b, actions, initial)
                            self.assertTrue(verify_certificate(a, b, actions, initial, answer))
                            brute = None
                            for depth in range(4):
                                for word in itertools.product(range(2), repeat=depth):
                                    x, y = initial
                                    for k in word:
                                        x, y = a.steps[k][x], b.steps[k][y]
                                    if a.outputs[x] != b.outputs[y]:
                                        brute = depth
                                        break
                                if brute is not None:
                                    break
                            if brute is None:
                                self.assertEqual(answer["status"], "equivalent")
                            else:
                                self.assertEqual(answer["length"], brute)


if __name__ == "__main__":
    unittest.main()
