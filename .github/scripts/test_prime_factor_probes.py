import unittest
from unittest.mock import patch

from prime_factor_probes import PROBES, select


class ProbeSelectionTest(unittest.TestCase):
    def test_each_source_selects_only_its_original_push_and_pr_branch(self):
        for event in ("push", "pull_request"):
            for probe in PROBES.values():
                branch = probe.push_branch if event == "push" else probe.pr_base
                payload = {"ref": f"refs/heads/{branch}", "pull_request": {"base": {"ref": branch}}}
                for key, changed in PROBES.items():
                    path = f"linear_input/lean_check/{changed.stem}.inc"
                    expected_branch = changed.push_branch if event == "push" else changed.pr_base
                    with self.subTest(event=event, branch=branch, path=path):
                        with patch("prime_factor_probes.changed_paths", return_value={path}):
                            self.assertEqual(select(event, payload), [key] if branch == expected_branch else [])

    def test_shared_base_runs_both_changed_siblings(self):
        payload = {"pull_request": {"base": {"ref": "chatgpt/prime-factor-f0-adaptive-20261103"}}}
        paths = {"linear_input/lean_check/PrimeFactorGeneralF0.inc", "linear_input/lean_check/PrimeFactorFiniteLength.inc"}
        with patch("prime_factor_probes.changed_paths", return_value=paths):
            self.assertEqual(select("pull_request", payload), ["general-f0", "general-length"])

    def test_main_pr_only_checks_changes_to_the_shared_runner(self):
        payload = {"pull_request": {"base": {"ref": "main"}}}
        with patch("prime_factor_probes.changed_paths", return_value={"linear_input/lean_check/PrimeFactorOrbits.inc"}):
            self.assertEqual(select("pull_request", payload), [])
        with patch("prime_factor_probes.changed_paths", return_value={".github/scripts/prime_factor_probes.py"}):
            self.assertEqual(select("pull_request", payload), list(PROBES))

    def test_dispatch_selects_one_or_all(self):
        for key in PROBES:
            self.assertEqual(select("workflow_dispatch", {"inputs": {"probe": key}}), [key])
        self.assertEqual(select("workflow_dispatch", {"inputs": {"probe": "all"}}), list(PROBES))
        with self.assertRaises(ValueError):
            select("workflow_dispatch", {"inputs": {"probe": "unknown"}})


if __name__ == "__main__":
    unittest.main()
