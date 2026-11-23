"""Offline independent audit of observed Forge results and recovery safeguards."""
from datetime import datetime, timedelta, timezone
from pathlib import Path
from tempfile import TemporaryDirectory
import copy
import json
import unittest

from tools.autonomy import forge_audit as audit

ROOT = Path(__file__).resolve().parents[1]
GSTATE = ROOT / "tests/fixtures/forge_audit_generic.json"
MSTATE = ROOT / "tests/fixtures/forge_audit_meta.json"
T = datetime(2026, 11, 23, 11, 40, tzinfo=timezone.utc)


def run(id, event="push", time="2026-11-23T08:01:00Z",
        status="completed", conclusion="success"):
    return {"id": id, "created_at": time, "event": event,
            "status": status, "conclusion": conclusion}


class ForgeAuditTests(unittest.TestCase):
    def setUp(self):
        self.folder = TemporaryDirectory()
        self.addCleanup(self.folder.cleanup)
        self.path = Path(self.folder.name)
        self.gs = audit.read_json(GSTATE)
        self.ms = audit.read_json(MSTATE)
        audit.gf.validate_state(self.gs)
        audit.mf.validate_state(self.ms)
        self.runs = {"generic": [], "meta": []}

    def dump(self, name, value):
        dest = self.path / name
        dest.write_text(json.dumps(value) + "\n", encoding="utf-8")
        return dest

    def test_real_two_generations_still_not_new_primitive_semantics(self):
        metrics = audit.capability(self.gs, self.ms)
        self.assertEqual(metrics["generic"]["grid3"]["verified_operators"], 1)
        self.assertEqual(metrics["generic"]["signal4"]["verified_operators"], 1)
        self.assertEqual(metrics["generic"]["grid3"]["outside_primitive_depth_two_baseline"], 0)
        self.assertEqual(metrics["generic"]["signal4"]["outside_primitive_depth_two_baseline"], 0)
        self.assertEqual(metrics["generic"]["grid3"]["verified_macro_reuse"], 0)
        self.assertEqual(metrics["generic"]["signal4"]["verified_macro_reuse"], 0)
        self.assertEqual(metrics["meta"]["verified_rule_count"], 2)
        self.assertEqual(metrics["meta"]["maximum_certified_rule_lineage"], 2)
        self.assertEqual(metrics["meta"]["descendants_reusing_verified_rules"], 1)
        self.assertFalse(metrics["expressive_power_beyond_trusted_primitive_closure"])

    def test_missing_scheduled_events_are_not_mistaken_for_success(self):
        result = audit.report(self.gs, self.ms, self.runs, T)
        for kind in ("generic", "meta"):
            status = result["scheduler"][kind]
            self.assertTrue(status["no_scheduled_runs_observed"])
            self.assertEqual(status["observed_schedule_events"], 0)
            self.assertGreater(status["nominal_matured_schedule_slots"], 10)
            self.assertEqual(result["recovery_gate"][kind]["reason"],
                             "BOUNDED_CATCHUP_ALLOWED")

    def test_schedule_observation_and_manual_dispatch_are_distinct(self):
        self.runs["generic"].extend([
            audit_row(run(44, "schedule", "2026-11-23T10:00:00Z")),
            audit_row(run(45, "workflow_dispatch", "2026-11-23T10:20:00Z")),
        ])
        report = audit.report(self.gs, self.ms, self.runs, T)
        self.assertEqual(report["scheduler"]["generic"]["observed_schedule_events"], 1)
        self.assertEqual(report["scheduler"]["generic"]["observed_manual_or_relay_dispatches"], 1)
        self.assertFalse(report["scheduler"]["generic"]["no_scheduled_runs_observed"])

    def test_cooldown_and_running_job_block_repair(self):
        recent = [audit_row(run(3, "workflow_dispatch", "2026-11-23T11:35:00Z"))]
        result = audit.dispatch_gate("generic", self.gs, recent, T)
        self.assertFalse(result["allowed"])
        self.assertEqual(result["reason"], "LAST_LAUNCH_INSIDE_COOLDOWN")
        active = [audit_row(run(4, "schedule", "2026-11-23T08:03:00Z",
                                status="in_progress", conclusion=None))]
        self.assertEqual(audit.dispatch_gate("generic", self.gs, active, T)["reason"],
                         "WORKFLOW_STILL_ACTIVE")

    def test_state_cap_and_time_window_enforced(self):
        done = copy.deepcopy(self.gs)
        done["receipts"].extend([{} for _ in range(3)])
        # Gate uses only count, while report validates the complete history.
        self.assertEqual(audit.dispatch_gate("generic", done, [], T)["reason"],
                         "TRIAL_CAP_REACHED")
        past = datetime(2026, 11, 23, 13, 0, tzinfo=timezone.utc)
        future = datetime(2026, 11, 23, 7, 59, tzinfo=timezone.utc)
        for timestamp in (past, future):
            with self.subTest(timestamp=timestamp):
                self.assertEqual(audit.dispatch_gate("meta", self.ms, [], timestamp)["reason"],
                                 "TRIAL_WINDOW_CLOSED")

    def test_reject_untrusted_run_records_and_tampered_states(self):
        a = self.dump("generic-runs.json", {"workflow_runs": [
            run(1), run(1)
        ]})
        b = self.dump("meta-runs.json", {"workflow_runs": []})
        with self.assertRaises(ValueError):
            audit.validated_inputs(GSTATE, MSTATE, a, b)
        broken = copy.deepcopy(self.ms)
        broken["rules"][0]["coverage"]["fingerprint"] = "0" * 64
        a = self.dump("generic-runs.json", {"workflow_runs": []})
        c = self.dump("bad-meta.json", broken)
        with self.assertRaises(ValueError):
            audit.validated_inputs(GSTATE, c, a, b)

    def test_end_to_end_report_file(self):
        ga = self.dump("gen.json", {"workflow_runs": [run(12)]})
        ma = self.dump("meta.json", {"workflow_runs": [run(13)]})
        report_file = self.path / "audit.json"
        result = audit.main([
            "--generic-state", str(GSTATE), "--meta-state", str(MSTATE),
            "--generic-runs", str(ga), "--meta-runs", str(ma),
            "--now", "2026-11-23T11:40:00Z", "--output", str(report_file)
        ])
        self.assertEqual(result, 0)
        self.assertEqual(audit.read_json(report_file)["state"]["meta_verified"], 2)

    def test_utc_and_future_slot_validation(self):
        with self.assertRaises(ValueError):
            audit.parse_time("2026-11-23T11:40:00+09:00")
        with self.assertRaises(ValueError):
            audit.parse_time("11:40")
        shifted = copy.deepcopy(self.gs)
        shifted["last_utc_day"] = "2026-11-23T11:40Z"
        self.assertEqual(audit.dispatch_gate("generic", shifted, [], T)["reason"],
                         "CURRENT_SLOT_ALREADY_SAVED")


def audit_row(item):
    """Mirror validated REST subset in the smallest possible fake."""
    item = dict(item)
    item["created_at"] = audit.parse_time(item["created_at"])
    return item


if __name__ == "__main__":
    unittest.main()
