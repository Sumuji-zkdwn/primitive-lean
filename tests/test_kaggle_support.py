from pathlib import Path
import importlib.util
import os
import tempfile
import time
import unittest
from unittest.mock import patch
import zipfile

SPEC = importlib.util.spec_from_file_location("kaggle_support", Path(__file__).parents[1] / "notebooks/kaggle_support.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SnapshotAndFailureLogs(unittest.TestCase):
    def test_changed_source_is_rejected_before_any_lean_command(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "proof.lean").write_bytes(b"changed")
            with patch.object(MODULE, "run_logged") as run:
                with self.assertRaisesRegex(ValueError, "snapshot changed"):
                    MODULE.run_proofs(root, root, {"proof.lean": MODULE.sha_bytes(b"original")})
                run.assert_not_called()

    def test_failed_run_exports_fresh_diagnostic_but_not_old_success(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / "project"
            reports = Path(d) / "reports"
            reports.mkdir()
            (root / "verification").mkdir(parents=True)
            old = root / "verification/main-result.json"
            old.write_text('{"passed":true}')
            since = time.time_ns()
            fresh = root / "verification/proof-only-joint.log"
            fresh.write_text("actual failure diagnostic")
            os.utime(fresh, ns=(since + 1_000_000, since + 1_000_000))
            state = {"proofs": {"status": "failed"}, "proof_attempt_started_ns": since}
            result = MODULE.export_results(root, reports, state)
            with zipfile.ZipFile(result) as archive:
                self.assertIn("proofs/verification/proof-only-joint.log", archive.namelist())
                self.assertNotIn("proofs/verification/main-result.json", archive.namelist())


if __name__ == "__main__":
    unittest.main()
