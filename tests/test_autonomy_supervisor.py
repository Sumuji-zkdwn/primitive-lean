"""Offline tests for the GitHub-only, at-most-one-recovery supervisor."""
from datetime import date
import unittest

from tools.autonomy.supervisor import (
    GitHub, TRACKS, decide, evaluate, iso_day, markdown, summarize_ledger,
)


DAY = date(2026, 11, 23)


def run_event(day="2026-11-23", status="completed", conclusion="success",
              event="schedule", branch="main", clock="06:00:00"):
    return {"id": 1, "created_at": day + "T" + clock + "Z",
            "status": status, "conclusion": conclusion,
            "event": event, "head_branch": branch,
            "html_url": "https://github.com/test/actions/runs/1"}


def rows(statuses):
    return [
        {"name": track.name, "workflow": track.workflow,
         "run": {"status": status, "latest": None},
         "ledger": {"records": 0, "last_day": None}}
        for track, status in zip(TRACKS, statuses)
    ]


class SupervisorTests(unittest.TestCase):
    def test_iso_day_requires_offset(self):
        self.assertEqual(iso_day("2026-11-22T23:59:59-01:00"), DAY)
        with self.assertRaises(ValueError):
            iso_day("2026-11-23T01:00:00")

    def test_same_day_success_no_recovery(self):
        value = evaluate([run_event()], DAY)
        self.assertEqual(value["status"], "RUN_SUCCESS")

    def test_same_day_failure_never_blindly_retried(self):
        value = evaluate([run_event(conclusion="failure")], DAY)
        self.assertEqual(value["status"], "FAILED_TODAY")

    def test_queued_from_yesterday_prevents_recovery(self):
        value = evaluate([
            run_event(day="2026-11-22", status="queued", conclusion=None)
        ], DAY)
        self.assertEqual(value["status"], "IN_PROGRESS")

    def test_old_success_is_missing_today(self):
        value = evaluate([run_event(day="2026-11-22")], DAY)
        self.assertEqual(value["status"], "MISSING_TODAY")

    def test_ignore_pr_and_other_branch(self):
        value = evaluate([
            run_event(event="pull_request"),
            run_event(branch="untrusted"),
        ], DAY)
        self.assertEqual(value["status"], "MISSING_TODAY")

    def test_newer_failure_overrides_older_success(self):
        value = evaluate([
            run_event(clock="05:00:00", conclusion="success"),
            run_event(clock="07:00:00", conclusion="failure"),
        ], DAY)
        self.assertEqual(value["status"], "FAILED_TODAY")

    def test_first_missing_track_only(self):
        states = rows(["RUN_SUCCESS", "MISSING_TODAY", "MISSING_TODAY",
                       "RUN_SUCCESS", "MISSING_TODAY"])
        choice = decide(states)
        self.assertEqual(choice["track"], TRACKS[1].name)
        self.assertEqual(choice["candidate_count"], 3)
        self.assertEqual(choice["action"], "DISPATCH_ONE_MISSING_WORKFLOW")

    def test_no_action_when_all_healthy_or_failed(self):
        choice = decide(rows(["RUN_SUCCESS", "FAILED_TODAY", "IN_PROGRESS",
                              "RUN_SUCCESS", "FAILED_TODAY"]))
        self.assertFalse(choice["selected"])
        self.assertIsNone(choice["track"])

    def test_reject_unknown_or_incomplete_tracks(self):
        with self.assertRaises(ValueError):
            decide(rows(["MISSING_TODAY"]))
        state = rows(["RUN_SUCCESS"] * len(TRACKS))
        state[0]["name"] = "attacker-workflow"
        with self.assertRaises(ValueError):
            decide(state)

    def test_ledger_counts_and_untrusted_source_not_executed(self):
        for track in TRACKS:
            if track.name == "research-scout":
                data = {"schema_version": 1, "queue": [{}, {}],
                        "last_ai_day": None}
            elif track.name == "research-conveyor":
                data = {"schema_version": 1, "results": [{}],
                        "last_utc_day": "2026-11-22"}
            else:
                data = {"schema_version": 1, "receipts": [{}],
                        "last_utc_day": "2026-11-22"}
            self.assertGreaterEqual(summarize_ledger(data, track)["records"], 1)
            data["schema_version"] = 2
            with self.assertRaises(ValueError):
                summarize_ledger(data, track)

    def test_repository_scope_validation(self):
        with self.assertRaises(ValueError):
            GitHub("../escape", "token")
        api = GitHub("Sumuji-zkdwn/primitive-lean", "test-token")
        with self.assertRaises(ValueError):
            api.request("GET", "/repos/other/repo/issues")

    def test_report_distinguishes_run_from_math_proof(self):
        result = markdown(DAY, rows(["RUN_SUCCESS"] * 5),
                          {"action": "NO_ACTION", "track": None}, False)
        self.assertIn("not proof of new mathematics", result)
        self.assertIn("Recovery dispatched: **false**", result)


if __name__ == "__main__":
    unittest.main()
