import unittest
from datetime import datetime, timezone, timedelta

from tools.autonomy.forge_recovery import (
    TRACKS, choose_slot, marker_of, recover, utc_slot, format_slot,
)


NOW = datetime(2026, 11, 24, 7, 19, tzinfo=timezone.utc)


class FakeAPI:
    def __init__(self, marker="2026-11-24T04:30Z", outcome="success", advances=True):
        self.markers = {t.name: marker for t in TRACKS}
        self.runs = {t.name: [] for t in TRACKS}
        self.calls = []
        self.outcome = outcome
        self.advances = advances

    def state(self, track):
        marker = self.markers[track.name]
        return {"schema_version": 1, "last_utc_day": marker,
                "rules": [{"day": marker}] if marker else []}

    def operational_runs(self, track):
        return self.runs[track.name]

    def trigger(self, track, nonce):
        self.calls.append((track.name, nonce))
        self.runs[track.name].insert(0, {
            "id": len(self.calls), "event": "workflow_dispatch",
            "display_title": "Forge recovery " + nonce,
            "status": "completed", "conclusion": self.outcome})
        if self.advances and self.outcome == "success":
            self.markers[track.name] = choose_slot(self.markers[track.name], NOW)


class RecoveryTests(unittest.TestCase):
    def execute(self, api):
        return recover(api, "42", "1", now=lambda: NOW, emit=lambda _: None)

    def test_slots(self):
        self.assertEqual(choose_slot(None, NOW), "2026-11-24T07:00Z")
        self.assertEqual(choose_slot("2026-11-23", NOW), "2026-11-24T05:30Z")
        self.assertEqual(choose_slot("2026-11-24T05:30Z", NOW), "2026-11-24T06:00Z")
        self.assertEqual(choose_slot("2026-11-24T06:40Z", NOW), "2026-11-24T07:00Z")
        self.assertEqual(choose_slot("2026-11-24T07:00Z", NOW), "2026-11-24T07:00Z")
        self.assertEqual(choose_slot("2026-11-24T07:10Z", NOW), "2026-11-24T07:10Z")
        self.assertEqual(choose_slot("2026-11-23T23:30Z",
            datetime(2026, 11, 24, 0, 9, tzinfo=timezone.utc)), "2026-11-24T00:00Z")

    def test_invalid_marker(self):
        with self.assertRaises(ValueError):
            choose_slot("2026-11-24T07:13Z", NOW)
        with self.assertRaises(ValueError):
            marker_of({"schema_version": 1, "last_utc_day": "2026-11-24",
                       "rules": []})

    def test_bounded_catchup(self):
        api = FakeAPI()
        self.execute(api)
        self.assertEqual(len(api.calls), 8)
        self.assertEqual([x[0] for x in api.calls], ["meta", "generic"] * 4)
        self.assertEqual(set(api.markers.values()), {"2026-11-24T07:00Z"})
        self.execute(api)
        self.assertEqual(len(api.calls), 8)

    def test_no_progress_stops(self):
        api = FakeAPI(advances=False)
        self.execute(api)
        self.assertEqual(len(api.calls), 2)

    def test_failure_stops(self):
        api = FakeAPI(outcome="failure")
        records = self.execute(api)
        self.assertEqual(len(api.calls), 1)
        self.assertEqual(records[-1]["result"], "CHILD_NOT_SUCCESSFUL")

    def test_active_defers(self):
        api = FakeAPI()
        api.runs["generic"].append({"status": "queued"})
        self.execute(api)
        self.assertEqual(api.calls, [])

    def test_missing_correlated_run_stops(self):
        api = FakeAPI()
        def no_run(track, nonce):
            api.calls.append((track.name, nonce))
        api.trigger = no_run
        clock = [0]
        def sleep(seconds):
            clock[0] += seconds
        rows = recover(api, "42", "1", now=lambda: NOW,
                       monotonic=lambda: clock[0], sleep=sleep, emit=lambda _: None)
        self.assertEqual(len(api.calls), 1)
        self.assertEqual(rows[-1]["result"], "CHILD_NOT_SUCCESSFUL")


if __name__ == "__main__":
    unittest.main()
