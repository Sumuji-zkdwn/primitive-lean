"""Check that every Gravity PR delegated to integration selects its owner."""

import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
import unittest

import yaml


WORKFLOWS = Path(__file__).resolve().parents[1] / "workflows"


def workflow(name):
    return yaml.load((WORKFLOWS / name).read_text(encoding="utf-8"), Loader=yaml.BaseLoader)


GRAVITY = workflow("gravity-observation-proof.yml")
INTEGRATION = workflow("primitive-lean-ci.yml")
SELECT = next(step for step in GRAVITY["jobs"]["proof"]["steps"] if step.get("id") == "integration")


class GravityRoutingTest(unittest.TestCase):
    def test_shared_trigger_covers_every_gravity_path(self):
        gravity = GRAVITY["on"]["pull_request"]
        integration = INTEGRATION["on"]["pull_request"]
        self.assertEqual(set(gravity), {"paths"})
        self.assertEqual(set(integration), {"branches", "paths"})
        self.assertEqual(set(SELECT["env"]["SHARED_PR_BASES"].splitlines()), set(integration["branches"]))
        for branch in integration["branches"]:
            self.assertNotRegex(branch, r"[^a-zA-Z0-9/_.-]")
        for pattern in integration["paths"]:
            self.assertFalse(pattern.startswith("!"), f"Review negative filter {pattern}")
        for path in gravity["paths"]:
            self.assertNotRegex(path, r"[^a-zA-Z0-9/_.-]")
            self.assertTrue(any(
                path == pattern or (pattern.endswith("/**") and path.startswith(pattern[:-2]))
                for pattern in integration["paths"]
            ), path)

    def test_workflow_selects_one_owner(self):
        bases = INTEGRATION["on"]["pull_request"]["branches"]
        cases = [("pull_request", base, True) for base in bases]
        cases += [("pull_request", "MAIN", False), ("pull_request", "topic", False),
                  ("push", "", False), ("workflow_dispatch", "", False)]
        for event, base, shared in cases:
            with self.subTest(event=event, base=base), TemporaryDirectory() as work:
                env = dict(os.environ, GITHUB_EVENT_NAME=event, GITHUB_BASE_REF=base,
                           GITHUB_REPOSITORY="example/lean", GITHUB_API_URL="https://api.github.com",
                           GITHUB_SERVER_URL="https://github.com", PR_NUMBER="154", HEAD_SHA="abc123",
                           SHARED_PR_BASES=SELECT["env"]["SHARED_PR_BASES"],
                           GITHUB_OUTPUT="output", GITHUB_STEP_SUMMARY="summary")
                subprocess.run(["bash", "-eu", "-o", "pipefail", "-c", SELECT["run"]],
                               env=env, cwd=work, check=True)
                self.assertEqual((Path(work) / "output").read_text().strip(), f"shared={str(shared).lower()}")
                reference = Path(work) / "gravity-integration.md"
                self.assertEqual(reference.exists(), shared)
                if shared:
                    self.assertIn("/pull/154/checks?sha=abc123", reference.read_text())


if __name__ == "__main__":
    unittest.main()
