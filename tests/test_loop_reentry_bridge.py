"""Original autonomy generator and extracted finite interpreter must agree."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from tools.autonomy import grow
from tools.autonomy.check_extracted_loop import verify


class ReentryBridgeTests(unittest.TestCase):
    def test_replay_one_verified_and_one_candidate(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            rows = []
            models = list(grow.candidates())[:2]
            for i, model in enumerate(models, 1):
                source = grow.proof_source(i, model).encode("utf-8")
                path = f"linear_input/lean_check/AutonomyCycle{i:05d}.inc"
                p = root / path
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(source)
                rows.append({
                    "cycle": i, "model": model, "source": path,
                    "sha256": hashlib.sha256(source).hexdigest(),
                    "status": "verified" if i == 1 else "candidate",
                })
            ledger = root / grow.LEDGER_PATH
            ledger.parent.mkdir(parents=True, exist_ok=True)
            ledger.write_text(json.dumps({"schema_version": 1, "cycles": rows}))
            self.assertEqual(verify(root)["candidate_cycles"], 1)
            with self.assertRaisesRegex(ValueError, "unverified"):
                verify(root, require_sealed=True)
            rows[-1]["status"] = "verified"
            ledger.write_text(json.dumps({"schema_version": 1, "cycles": rows}))
            self.assertEqual(verify(root, require_sealed=True)["verified_cycles"], 2)

    def test_edit_original_proof_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            model = next(grow.candidates())
            content = grow.proof_source(1, model).encode()
            p = root / "linear_input/lean_check/AutonomyCycle00001.inc"
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(content + b"\n-- tampered")
            ledger = root / grow.LEDGER_PATH
            ledger.parent.mkdir(parents=True, exist_ok=True)
            ledger.write_text(json.dumps({"schema_version": 1, "cycles": [{
                "cycle": 1, "model": model,
                "source": "linear_input/lean_check/AutonomyCycle00001.inc",
                "sha256": hashlib.sha256(content).hexdigest(), "status": "verified"
            }]}))
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                verify(root)


if __name__ == "__main__":
    unittest.main()
