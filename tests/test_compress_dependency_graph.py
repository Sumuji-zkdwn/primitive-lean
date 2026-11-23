"""Synthetic regression tests for lossless source reachability compression."""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "tools/compress_dependency_graph.py"
spec = importlib.util.spec_from_file_location("compress_dependency_graph", SCRIPT)
tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)


def fixture(names, links):
    graph = {
        "main_commit": "snapshot-sha",
        "pr_snapshot": "snapshot-date",
        "nodes": [{"id": n} for n in names],
        "edges": [
            {"from": a, "to": b, "kind": kind, "symbols": []}
            for a, b, kind in links
        ],
    }
    raw = json.dumps(graph, sort_keys=True).encode()
    return tool.compress_graph(graph, raw)


class SourceReachabilityTests(unittest.TestCase):
    def test_diamond_and_shortcut_reduce_but_preserve_two_routes(self):
        view = fixture(["A", "B", "C", "D"], [
            ("A", "B", "exact_import"), ("A", "C", "qualified_reference"),
            ("B", "D", "qualified_reference"),
            ("C", "D", "qualified_reference"),
            ("A", "D", "qualified_reference"),
        ])
        self.assertEqual(view["edges"], [
            ["A", "B"], ["A", "C"], ["B", "D"], ["C", "D"]])
        self.assertEqual(view["counts"]["transitive_pairs_removed"], 1)
        self.assertEqual(view["counts"]["retained_pairs"], 4)

    def test_weak_candidate_does_not_create_an_alternative_path(self):
        view = fixture(["A", "B", "C"], [
            ("A", "B", "exact_import"),
            ("B", "C", "unique_identifier_candidate"),
            ("A", "C", "qualified_reference"),
        ])
        self.assertEqual(view["edges"], [["A", "B"], ["A", "C"]])
        self.assertEqual(view["counts"]["weak_edges_excluded"], 1)

    def test_multiple_kinds_of_one_pair_count_once(self):
        view = fixture(["A", "B"], [
            ("A", "B", "exact_import"),
            ("A", "B", "qualified_reference"),
        ])
        self.assertEqual(view["edges"], [["A", "B"]])
        self.assertEqual(view["counts"]["eligible_direct_edges"], 2)
        self.assertEqual(view["counts"]["unique_eligible_pairs"], 1)

    def test_cycle_rejected_instead_of_false_reduction(self):
        with self.assertRaisesRegex(ValueError, "cycle"):
            fixture(["A", "B"], [
                ("A", "B", "exact_import"),
                ("B", "A", "qualified_reference"),
            ])

    def test_unknown_endpoint_and_self_link_rejected(self):
        with self.assertRaisesRegex(ValueError, "unknown endpoint"):
            fixture(["A"], [("A", "B", "exact_import")])
        with self.assertRaisesRegex(ValueError, "self-edge"):
            fixture(["A"], [("A", "A", "exact_import")])

    def test_empty_and_disconnected_graph(self):
        view = fixture(["B", "A"], [])
        self.assertEqual(view["nodes"], ["A", "B"])
        self.assertEqual(view["edges"], [])
        self.assertEqual(view["counts"]["transitive_pairs_removed"], 0)

    def test_output_is_deterministic_under_edge_order(self):
        links = [("A", "B", "exact_import"),
                 ("B", "C", "qualified_reference"),
                 ("A", "C", "qualified_reference")]
        first = fixture(["A", "B", "C"], links)
        second = fixture(["C", "B", "A"], list(reversed(links)))
        # The digest intentionally changes when the raw source JSON changes.
        self.assertEqual(first["edges"], second["edges"])
        self.assertEqual(first["nodes"], second["nodes"])
        self.assertEqual(first["counts"], second["counts"])

    def test_generated_snapshot_matches_its_pinned_input(self):
        raw = tool.GRAPH.read_bytes()
        graph = json.loads(raw)
        actual = json.loads(tool.OUTPUT.read_text(encoding="utf-8"))
        # Check the provenance independently of the compressor that writes it.
        self.assertEqual(actual["source"]["graph_sha256"], hashlib.sha256(raw).hexdigest())
        self.assertEqual(actual["source"]["main_commit"], graph["main_commit"])
        self.assertEqual(actual["source"]["pr_snapshot"], graph["pr_snapshot"])
        self.assertEqual(tool.compress_graph(graph, raw), actual)


if __name__ == "__main__":
    unittest.main()
