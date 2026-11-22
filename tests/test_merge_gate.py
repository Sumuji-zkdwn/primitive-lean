"""Offline regression and adversarial tests for read-only Merge Gate."""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from tools import merge_gate as gate
from tools import merge_gate_collect as collector

FIXTURE = Path(__file__).resolve().parent / "fixtures/merge_gate_pair.json"


def sample():
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


class MergeGateTests(unittest.TestCase):
    def test_confirmed_live_observation_inheritance(self):
        data = sample()
        result = gate.analyze(data)
        self.assertEqual(result["ancestry_edges"], [[196, 198]])
        self.assertEqual(result["review_order_only"], [196, 198])
        self.assertFalse(result["approval_granted"])
        self.assertEqual(result["automated_merges"], 0)
        self.assertEqual(result["relationships"][0]["relation"], "PROVED_ANCESTRY")
        self.assertEqual(result["relationships"][0]["shared_count"], 7)
        rows = {r["number"]: r for r in result["pull_requests"]}
        self.assertIn("HAS_CHILD_PR_198", rows[196]["blockers"])
        self.assertIn("INHERITS_PR_196", rows[198]["blockers"])
        self.assertIn("DRAFT", rows[198]["blockers"])
        self.assertIn("OPEN_PR_UNIVERSE_PARTIAL", rows[196]["blockers"])
        self.assertEqual(rows[198]["next_action"],
                         "REVIEW_PARENT_FIRST_THEN_REBASE_CHILD")

    def test_overlap_without_comparison_is_not_called_conflict(self):
        data = sample()
        data["comparisons"] = []
        result = gate.analyze(data)
        self.assertEqual(result["ancestry_edges"], [])
        self.assertEqual(result["relationships"][0]["relation"], "OVERLAP_UNVERIFIED")
        self.assertNotIn("PROVED", result["relationships"][0]["relation"])
        self.assertIn("SHARED_FILES_PR_198", result["pull_requests"][0]["blockers"])

    def test_diverged_files_not_automatically_a_merge_conflict(self):
        data = sample()
        data["comparisons"][0].update(
            status="diverged", ahead_by=5, behind_by=3,
            merge_base_sha="a" * 40)
        result = gate.analyze(data)
        self.assertEqual(result["ancestry_edges"], [])
        self.assertEqual(result["relationships"][0]["relation"],
                         "OVERLAP_DIVERGED_NEEDS_REVIEW")
        self.assertFalse(result["approval_granted"])

    def test_disjoint_files_do_not_prove_semantic_independence(self):
        data = sample()
        data["comparisons"] = []
        data["prs"][1]["files"] = ["research/somewhere_else.lean"]
        result = gate.analyze(data)
        self.assertEqual(result["relationships"], [])
        self.assertFalse(result["approval_granted"])
        self.assertIn("OPEN_PR_UNIVERSE_PARTIAL",
                      result["pull_requests"][1]["blockers"])

    def test_duplicate_head_is_separate_from_ancestry(self):
        data = sample()
        data["prs"][1]["head_sha"] = data["prs"][0]["head_sha"]
        data["comparisons"] = []
        result = gate.analyze(data)
        self.assertEqual(result["ancestry_edges"], [])
        self.assertEqual(result["relationships"][0]["relation"], "DUPLICATE_HEAD")
        self.assertIn("DUPLICATE_HEAD_PR_196",
                      result["pull_requests"][1]["blockers"])

    def test_compare_evidence_must_be_exact_ancestor_sha(self):
        data = sample()
        data["comparisons"][0]["merge_base_sha"] = "f" * 40
        result = gate.analyze(data)
        self.assertEqual(result["ancestry_edges"], [])
        self.assertEqual(result["relationships"][0]["relation"], "OVERLAP_UNVERIFIED")

    def test_stale_ci_and_partial_files_fail_closed(self):
        data = sample()
        data["prs"][0]["checks_complete"] = True
        data["prs"][0]["checks"] = [
            {"head_sha": data["prs"][0]["head_sha"],
             "name": "Lean", "status": "completed", "conclusion": "failure"}]
        data["prs"][1]["files_complete"] = False
        data["prs"][1]["base_sha"] = "e" * 40
        result = gate.analyze(data)
        self.assertIn("CI_FAILURE", result["pull_requests"][0]["blockers"])
        self.assertIn("FILES_INCOMPLETE", result["pull_requests"][1]["blockers"])
        self.assertIn("TARGET_SHA_STALE", result["pull_requests"][1]["blockers"])
        data["prs"][0]["checks"][0]["head_sha"] = "a" * 40
        with self.assertRaisesRegex(ValueError, "check not from exact head"):
            gate.analyze(data)

    def test_cycle_or_duplicate_pair_is_rejected(self):
        data = sample()
        third = deepcopy(data["prs"][1])
        third["number"], third["head_sha"] = 199, "c" * 40
        third["files"] = ["another.lean"]
        data["prs"].append(third)
        data["comparisons"] = [
            {"a":196, "b":198, "status":"ahead", "ahead_by":2,
             "behind_by":0, "merge_base_sha":data["prs"][0]["head_sha"]},
            {"a":198, "b":199, "status":"ahead", "ahead_by":2,
             "behind_by":0, "merge_base_sha":data["prs"][1]["head_sha"]},
            {"a":196, "b":199, "status":"behind", "ahead_by":0,
             "behind_by":2, "merge_base_sha":third["head_sha"]},
        ]
        with self.assertRaisesRegex(ValueError, "cycle"):
            gate.analyze(data)
        data["comparisons"].append(deepcopy(data["comparisons"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate comparison"):
            gate.analyze(data)

    def test_large_renamed_file_list_remains_partial_not_green(self):
        data = sample()
        data["prs"][1]["files"] = ["src/module_%03d.lean" % i
                                   for i in range(600)]
        data["prs"][1]["files_complete"] = False
        data["comparisons"] = []
        result = gate.analyze(data)
        row = result["pull_requests"][1]
        self.assertEqual(row["changed_file_count"], 600)
        self.assertIn("FILES_INCOMPLETE", row["blockers"])
        self.assertFalse(row["merge_approval"])

    def test_same_metadata_does_not_claim_merge_approval(self):
        data = sample()
        data["selected_prs_complete"] = True
        data["open_inventory_complete"] = True
        for p in data["prs"]:
            p["draft"] = False
            p["checks_complete"] = True
            p["checks"] = [{"head_sha": p["head_sha"], "name": "Lean",
                            "status": "completed", "conclusion": "success"}]
        result = gate.analyze(data)
        self.assertFalse(result["approval_granted"])
        self.assertFalse(any(p["merge_approval"] for p in result["pull_requests"]))
        self.assertTrue(all(p["ci_observation"] == "CI_SUCCESS_OBSERVED_ONLY"
                            for p in result["pull_requests"]))

    def test_cli_replays_source_pinned_fixture(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            report, md = directory / "report.json", directory / "report.md"
            self.assertEqual(gate.main([
                "--snapshot", str(FIXTURE),
                "--report", str(report), "--markdown", str(md)]), 0)
            parsed = json.loads(report.read_text("utf-8"))
            self.assertEqual(parsed["ancestry_edges"], [[196, 198]])
            self.assertIn("Read-only triage", md.read_text("utf-8"))


class FakeAPI:
    repository = "Sumuji-zkdwn/primitive-lean"
    prefix = "/repos/" + repository

    def __init__(self):
        self.fixture = sample()
        self.calls = []

    def get(self, endpoint):
        self.calls.append(endpoint)
        if endpoint.endswith("/branches/main"):
            return {"commit":{"sha":self.fixture["main_sha"]}}
        if "/pulls?state=open" in endpoint:
            return [self.raw(p) for p in self.fixture["prs"]]
        if "/files?" in endpoint:
            n = int(endpoint.split("/pulls/")[1].split("/files")[0])
            p = next(p for p in self.fixture["prs"] if p["number"] == n)
            return [{"filename":path} for path in p["files"]]
        if "/check-runs?" in endpoint:
            sha = endpoint.split("/commits/")[1].split("/check-runs")[0]
            return {"total_count": 1, "check_runs": [
                {"head_sha":sha, "name":"Lean","status":"completed",
                 "conclusion":"success"}]}
        if "/compare/" in endpoint:
            return {"status":"ahead", "ahead_by":21, "behind_by":0,
                    "merge_base_commit":{"sha":self.fixture["prs"][0]["head_sha"]}}
        raise AssertionError("unrecognized API endpoint: " + endpoint)

    def raw(self, p):
        return {"number":p["number"], "title":p["title"], "state":"open",
                "draft":p["draft"],
                "head":{"sha":p["head_sha"], "ref":p["head_ref"],
                        "repo":{"full_name":self.repository}},
                "base":{"sha":p["base_sha"], "ref":"main"}}


class LiveCollectorTests(unittest.TestCase):
    def test_retrieval_is_read_only_and_exact_sha_pinned(self):
        api = FakeAPI()
        s = collector.collect(api, limit=2, focus=[196,198],
                              controller_sha="d" * 40)
        self.assertEqual(s["kind"], "GITHUB_LIVE_READ_ONLY_SNAPSHOT")
        self.assertEqual(s["controller_sha"], "d" * 40)
        self.assertTrue(s["selected_prs_complete"])
        self.assertEqual(s["comparisons"][0]["status"], "ahead")
        self.assertTrue(all(x["checks_complete"] for x in s["prs"]))
        plan = gate.analyze(s)
        self.assertEqual(plan["ancestry_edges"], [[196,198]])
        self.assertEqual(plan["automated_merges"], 0)
        self.assertTrue(all("/repos/" in url for url in api.calls))

    def test_missing_token_and_bound_inputs_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "GITHUB_TOKEN"):
            collector.API("Sumuji-zkdwn/primitive-lean", "")
        with self.assertRaisesRegex(ValueError, "invalid repository"):
            collector.API("bad/../repo", "example")
        with self.assertRaisesRegex(ValueError, "limit"):
            collector.collect(FakeAPI(), limit=0)
        with self.assertRaisesRegex(ValueError, "focus"):
            collector.collect(FakeAPI(), focus=[0])


if __name__ == "__main__":
    unittest.main()
