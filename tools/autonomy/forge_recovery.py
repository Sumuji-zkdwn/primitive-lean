"""Bounded, ledger-driven recovery for the two existing Forge workflows.

No ledger writes, arbitrary dispatch targets, remote code, or retries on failure.
The actual generators retain independent certification and their own concurrency.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timedelta, timezone
import json
import os
from pathlib import Path
import re
import time

from tools.autonomy.supervisor import GitHub, Track, ACTIVE

HALF_HOUR = timedelta(minutes=30)
MAX_ROUNDS = 4
MAX_WAIT_SECONDS = 180
TOTAL_SECONDS = 900
TRACKS = (
    Track("meta", "meta-forge.yml", "autonomy/meta-forge-state",
          "docs/autonomy/meta-forge-state.json"),
    Track("generic", "generic-forge.yml", "autonomy/generic-forge-state",
          "docs/autonomy/generic-forge-state.json"),
)
OPERATIONAL = frozenset({"schedule", "workflow_dispatch", "push"})


def utc_slot(now):
    if now.tzinfo is None:
        raise ValueError("timezone required")
    now = now.astimezone(timezone.utc)
    return now.replace(minute=now.minute // 30 * 30, second=0, microsecond=0)


def format_slot(now):
    return now.strftime("%Y-%m-%dT%H:%MZ")


def parse_marker(marker):
    if marker is None:
        return None
    if not isinstance(marker, str):
        raise ValueError("invalid ledger marker")
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", marker):
        parsed = datetime.strptime(marker, "%Y-%m-%d")
    elif re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}Z", marker):
        parsed = datetime.strptime(marker, "%Y-%m-%dT%H:%MZ")
        if parsed.minute % 10:
            raise ValueError("invalid historical slot")
    else:
        raise ValueError("invalid ledger marker")
    return parsed.replace(tzinfo=timezone.utc)


def choose_slot(marker, now):
    """Oldest still-recoverable half-hour slot after last certified receipt.

    Never fabricate old receipts, fill gaps behind existing receipts, or move
    backwards. An empty ledger starts at current time. A current/future legacy
    marker is returned unchanged: the generator's existing guard makes it a no-op.
    """
    current = utc_slot(now)
    last = parse_marker(marker)
    if last is None:
        return format_slot(current)
    if last >= current:
        return marker
    for offset in range(MAX_ROUNDS - 1, -1, -1):
        slot = current - offset * HALF_HOUR
        if slot > last:
            return format_slot(slot)
    raise AssertionError("current slot is later than marker")


def marker_of(data):
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        raise ValueError("unknown state schema")
    key = "receipts" if "receipts" in data else "rules"
    rows = data.get(key)
    if not isinstance(rows, list) or len(rows) > 100000:
        raise ValueError("invalid ledger history")
    marker = data["last_utc_day"]
    parse_marker(marker)
    if marker != (rows[-1]["day"] if rows else None):
        raise ValueError("inconsistent ledger marker")
    return marker


def due(marker, now):
    last = parse_marker(marker)
    return last is None or last < utc_slot(now)


class RecoveryAPI(GitHub):
    def operational_runs(self, track):
        if track not in TRACKS:
            raise ValueError("unknown workflow")
        response = self.request("GET", f"/repos/{self.repo}/actions/workflows/"
                                f"{track.workflow}/runs?branch=main&per_page=30")
        return [r for r in response["workflow_runs"]
                if r.get("head_branch") == "main" and r.get("event") in OPERATIONAL]

    def trigger(self, track, nonce):
        if track not in TRACKS or not re.fullmatch(r"[0-9]+-[0-9]+-(meta|generic)-[0-3]", nonce):
            raise ValueError("invalid fixed dispatch target or identifier")
        self.request("POST", f"/repos/{self.repo}/actions/workflows/{track.workflow}/dispatches",
                     {"ref": "main", "inputs": {"recovery_id": nonce}})


def recover(api, run_id, attempt, now=lambda: datetime.now(timezone.utc),
            monotonic=time.monotonic, sleep=time.sleep, emit=print):
    """At most four dispatches per track, sequential, with exact run correlation.

    A native run already queued/running is left alone. A failed or timed-out
    child halts this recovery (no blind retries). A successful no-progress child
    disables that track for this invocation (e.g. exhausted search frontier).
    """
    if not re.fullmatch(r"[0-9]+", run_id) or not re.fullmatch(r"[0-9]+", attempt):
        raise ValueError("invalid controller identity")
    start = monotonic()
    records = []
    blocked = set()

    def note(**record):
        records.append(record)
        emit(json.dumps(record, sort_keys=True))

    for index in range(MAX_ROUNDS):
        progress = False
        for track in TRACKS:
            if track.name in blocked:
                continue
            if monotonic() - start >= TOTAL_SECONDS:
                note(result="BUDGET_EXPIRED")
                return records
            before = marker_of(api.state(track))
            if not due(before, now()):
                continue
            # Cross-forge state changes can invalidate a replay, so do not
            # deliberately overlap with a live producer (native runs may race).
            if any(r.get("status") in ACTIVE for t in TRACKS
                   for r in api.operational_runs(t)):
                note(track=track.name, result="ACTIVE_PRODUCER_DEFERRED")
                return records
            nonce = f"{run_id}-{attempt}-{track.name}-{index}"
            title = f"Forge recovery {nonce}"
            api.trigger(track, nonce)
            note(track=track.name, result="DISPATCHED", nonce=nonce, before=before)
            deadline = min(start + TOTAL_SECONDS, monotonic() + MAX_WAIT_SECONDS)
            matched = None
            while monotonic() < deadline:
                matches = [r for r in api.operational_runs(track)
                           if r.get("event") == "workflow_dispatch"
                           and r.get("display_title") == title]
                if len(matches) > 1:
                    raise ValueError("ambiguous recovery run")
                if matches and matches[0].get("status") == "completed":
                    matched = matches[0]
                    break
                sleep(5)
            if matched is None or matched.get("conclusion") != "success":
                note(track=track.name, result="CHILD_NOT_SUCCESSFUL",
                     run_id=matched.get("id") if matched else None)
                return records
            after = marker_of(api.state(track))
            advanced = after is not None and (
                before is None or parse_marker(after) > parse_marker(before))
            note(track=track.name, result="ADVANCED" if advanced else "NO_PROGRESS",
                 before=before, after=after, run_id=matched.get("id"))
            if not advanced:
                blocked.add(track.name)
            else:
                progress = True
        if not progress:
            break
    note(result="FINISHED_BOUNDED_RECOVERY")
    return records


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    slot = sub.add_parser("slot")
    slot.add_argument("--state", type=Path, required=True)
    relay = sub.add_parser("recover")
    relay.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "slot":
        marker = marker_of(json.loads(args.state.read_text(encoding="utf-8")))
        print(choose_slot(marker, datetime.now(timezone.utc)))
    else:
        api = RecoveryAPI(os.environ["GITHUB_REPOSITORY"], os.environ["GITHUB_TOKEN"])
        # Keep partial evidence in the job log even if an API request fails.
        rows = recover(api, os.environ["GITHUB_RUN_ID"], os.environ["GITHUB_RUN_ATTEMPT"])
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(rows, indent=2) + "\n", encoding="utf-8")
        if any(row["result"] == "CHILD_NOT_SUCCESSFUL" for row in rows):
            raise SystemExit(1)


if __name__ == "__main__":
    main()
