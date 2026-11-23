"""Offline regression: adaptive finite mutation search, never a Lean proof."""
import copy
from pathlib import Path
import tempfile
import unittest

from tools.autonomy import finite_discovery as fd
from tools.autonomy import primitive_open as opened
from tools.autonomy import primitive_v2 as v2

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "tests/fixtures/primitive_open_v2_seed.json"
HEAD = "a" * 40
DAY = "2026-11-24"


class OpenSearchTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name)
        self.state = self.path / "empty.json"
        opened.save(self.state, opened.empty_state())
        self.upstream = opened.load(UPSTREAM)

    def test_real_verified_v2_seed_only(self):
        v2.validate_state(ROOT, self.upstream)
        self.assertGreater(len(self.upstream["cycles"]), 0)
        parents = opened.parent_models(self.upstream, [])
        self.assertEqual(len(parents), 1)
        self.assertTrue(parents[0][0].startswith("v2:"))
        fd.validate_model(parents[0][1])

    def test_parameterized_candidates_not_static_catalog(self):
        parent = opened.parent_models(self.upstream, [])[0][1]
        changes = list(opened.proposals(parent))
        self.assertGreater(len(changes), 10)
        self.assertTrue(any(rule == "redirect_edge" for rule, _ in changes))
        self.assertTrue(any(rule == "choose_pair" for rule, _ in changes))
        self.assertTrue(any(rule == "append_state" for rule, _ in changes))
        balanced = [rule for rule, _ in list(opened.balanced_proposals(parent))[:6]]
        self.assertEqual(set(balanced), set(opened.RULES))
        targets = set()
        for rule, args in changes:
            try:
                model = opened.evolve(parent, rule, args)
            except ValueError as exc:
                self.assertEqual(str(exc),
                                 "identity / redundant transformation is not a new candidate")
                continue
            targets.add(fd.model_fingerprint(model))
            fd.validate_model(model)
        self.assertGreater(len(targets), 10)

    def test_operators_work_across_successive_generations(self):
        parent = opened.parent_models(self.upstream, [])[0][1]
        # First a *new generated observation operator*, then a further
        # operator, not a member of any pre-listed 123-case catalog.
        model1 = opened.evolve(parent, "append_state", {"label": 0})
        model2 = opened.evolve(model1, "add_single_probe",
                              {"state": 3, "dest": 2})
        model3 = opened.evolve(model2, "redirect_edge",
                              {"action": 1, "state": 0, "dest": 1})
        for model in (model1, model2, model3):
            fd.validate_model(model)
        self.assertEqual(len(model2["observations"]), 4)
        self.assertEqual(len(model3["transitions"]), 3)
        self.assertEqual(len({fd.model_fingerprint(m)
                              for m in (parent, model1, model2, model3)}), 4)

    def test_v2_input_anchors_are_append_only(self):
        head = opened.upstream_head(self.upstream)
        subset = opened.upstream_at(self.upstream, head)
        self.assertEqual(len(subset["cycles"]), len(self.upstream["cycles"]))
        v2.validate_state(ROOT, subset)
        with self.assertRaises(ValueError):
            opened.upstream_at(self.upstream, "0" * 64)

    def test_typed_parameters_refuse_unreviewed_code(self):
        parent = opened.parent_models(self.upstream, [])[0][1]
        bad = [
            ("redirect_edge", {"action": 0, "state": 2, "dest": 99}),
            ("redirect_edge", {"action": 0, "state": 2, "dest": False}),
            ("change_readout", {"state": 0, "label": 99}),
            ("add_single_probe", {"state": -1, "dest": 0}),
            ("choose_pair", {"left": 1, "right": 1}),
            ("shell_command", {"x": 0}),
            ("redirect_edge", {"action": 0, "state": 0,
                               "dest": 1, "extra": "eval"}),
        ]
        for rule, args in bad:
            with self.subTest(rule=rule, args=args), self.assertRaises(ValueError):
                opened.evolve(parent, rule, args)

    def test_prepare_selects_from_verified_history_without_certificate_claim(self):
        result = opened.prepare(
            ROOT, UPSTREAM, self.state, DAY, HEAD, self.path / "cycle")
        self.assertTrue(result["candidate"])
        self.assertEqual(result["proposal"]["root_model"]["name"][:3], "fd_")
        self.assertEqual(len(list((self.path/"cycle/requests").glob("*.json"))), 2)
        manifest = opened.load(self.path / "cycle/proof/manifest.json")
        self.assertFalse(manifest["passed"])
        for m in manifest["models"]:
            proof = opened.load(self.path / "cycle/proof" / (m+".json"))
            self.assertEqual(proof["status"], "PENDING_KERNEL_VERIFICATION")
        with self.assertRaises(ValueError):
            opened.receipt(ROOT, UPSTREAM, self.state, HEAD,
                           self.path/"cycle", self.path/"result.json")

    def test_bad_historical_state_fails_closed(self):
        opened.validate_state(ROOT, self.upstream, opened.empty_state())
        tampered = opened.empty_state()
        tampered["last_utc_day"] = DAY
        tampered["receipts"].append({"status": opened.STATUS})
        with self.assertRaises(ValueError):
            opened.validate_state(ROOT, self.upstream, tampered)

    def test_no_same_day_duplicate_and_source_hash_checks(self):
        a = opened.plan(ROOT, self.upstream, opened.empty_state(), DAY, HEAD)
        b = opened.plan(ROOT, self.upstream, opened.empty_state(), DAY, HEAD)
        self.assertEqual(a, b)
        tampered = copy.deepcopy(self.upstream)
        tampered["cycles"][0]["word"] = [0, 0]
        with self.assertRaises((ValueError, TypeError, KeyError)):
            opened.plan(ROOT, tampered, opened.empty_state(), DAY, HEAD)

    def test_expanding_parent_frontier_is_feedback_not_static_list(self):
        parent = opened.parent_models(self.upstream, [])[0][1]
        child = opened.evolve(parent, "append_state", {"label": 0})
        record = {"id": "po_fake", "model": child}
        expanded = opened.parent_models(self.upstream, [record])
        self.assertIn("v3:po_fake", [name for name, _ in expanded])
        # Such a fabricated receipt would not, however, pass trust checks.
        tampered = opened.empty_state()
        tampered["receipts"] = [record]
        with self.assertRaises(ValueError):
            opened.validate_state(ROOT, self.upstream, tampered)

    def test_reject_invalid_utc_day_and_commit(self):
        for day, sha in [("2026-02-30", HEAD), (DAY, "short")]:
            with self.assertRaises(ValueError):
                opened.plan(ROOT, self.upstream, opened.empty_state(), day, sha)


if __name__ == "__main__":
    unittest.main()
