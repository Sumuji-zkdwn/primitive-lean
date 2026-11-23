#!/usr/bin/env python3
"""Read-only Forge reliability/capability audit and fail-closed dispatch gate.

Run provenance comes from GitHub's workflow-specific REST API, state from
read-only checked-out data branches. This tool NEVER dispatches anything: a
separate, narrowly permissioned Actions job consumes its explicit verdict.

No invented scheduler guarantees, no LLM inference, no trusted data-branch code.
"""
from __future__ import annotations

from datetime import datetime, timedelta, timezone
from pathlib import Path
import argparse
import json
import sys

from tools.autonomy import generic_forge as gf
from tools.autonomy import meta_forge as mf

SCHEMA = 1
WINDOW_BEGIN = datetime(2026, 11, 23, 8, 0, tzinfo=timezone.utc)
WINDOW_END = datetime(2026, 11, 23, 12, 59, 59, tzinfo=timezone.utc)
COOLDOWN_SECONDS = 600
MATURITY_DELAY_MINUTES = 20
EXPECTED_CAP = 5
KNOWN_WORKFLOWS = ("generic", "meta")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def parse_time(text):
    require(type(text) is str, "timestamp must be a string")
    try:
        result = datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError as exc:
        raise ValueError("invalid timestamp") from exc
    require(result.tzinfo is not None and result.utcoffset() == timedelta(0),
            "timestamp must be UTC")
    return result.astimezone(timezone.utc)


def read_json(path, max_bytes=8_000_000):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), "missing ordinary JSON file")
    require(path.stat().st_size <= max_bytes, "JSON input exceeds bound")
    return json.loads(path.read_text(encoding="utf-8"),
                      object_pairs_hook=gf.unique_json)


def validated_inputs(generic_state, meta_state, generic_runs, meta_runs):
    gs = read_json(generic_state, 500_000)
    ms = read_json(meta_state, 500_000)
    gf.validate_state(gs)
    mf.validate_state(ms)
    runs = {}
    for key, location in (("generic", generic_runs), ("meta", meta_runs)):
        obj = read_json(location)
        require(type(obj) is dict and type(obj.get("workflow_runs")) is list,
                "missing workflow_runs response")
        require(len(obj["workflow_runs"]) <= 100,
                "workflow API page unexpectedly large")
        seen = set()
        items = []
        for row in obj["workflow_runs"]:
            require(type(row) is dict and type(row.get("id")) is int
                    and row["id"] not in seen, "invalid/duplicate workflow run id")
            seen.add(row["id"])
            created = parse_time(row.get("created_at"))
            event = row.get("event")
            status = row.get("status")
            conclusion = row.get("conclusion")
            require(event in {"schedule", "push", "workflow_dispatch",
                              "repository_dispatch", "workflow_run"},
                    "unexpected workflow event")
            require(status in {"queued", "requested", "waiting", "pending",
                               "in_progress", "completed"}, "unexpected status")
            if status == "completed":
                require(conclusion in {"success", "failure", "cancelled",
                                       "skipped", "timed_out", "action_required",
                                       "neutral", "stale"},
                        "unexpected completed conclusion")
            items.append({"id": row["id"], "created_at": created,
                          "event": event, "status": status,
                          "conclusion": conclusion})
        runs[key] = items
    return gs, ms, runs


def exhaustive_baseline(domain):
    """All one- and two-step primitive words, not the entire primitive closure."""
    primitive = gf.DOMAINS[domain]
    known = set()
    for first in primitive:
        known.add(gf.audit(domain, (first,))["fingerprint"])
        for second in primitive:
            known.add(gf.audit(domain, (first, second))["fingerprint"])
    return known


def capability(gs, ms):
    """Separate proven finite behavior from unproven 'intelligence growth'."""
    group = {}
    for domain in gf.DOMAINS:
        rows = [row for row in gs["receipts"] if row["domain"] == domain]
        baseline = exhaustive_baseline(domain)
        group[domain] = {
            "verified_operators": len(rows),
            "new_distinct_behaviors_recorded": len({
                row["behavior"]["fingerprint"] for row in rows}),
            "outside_primitive_depth_two_baseline": sum(
                row["behavior"]["fingerprint"] not in baseline for row in rows),
            "longest_flattened_program": max(
                (len(row["program"]) for row in rows), default=0),
            "verified_macro_reuse": sum(
                row["left"].startswith("m:") or row["right"].startswith("m:")
                for row in rows),
            "primitive_depth_two_baseline_size": len(baseline),
        }
    depths = {}
    for row in ms["rules"]:
        depths[row["id"]] = 1 + (
            depths[row["parent"]] if row["parent"] is not None else 0)
    return {
        "generic": group,
        "meta": {
            "verified_rule_count": len(ms["rules"]),
            "distinct_probe_signatures": len({
                row["fingerprint"] for row in ms["rules"]}),
            "descendants_reusing_verified_rules": sum(
                row["parent"] is not None for row in ms["rules"]),
            "maximum_certified_rule_lineage": max(depths.values(), default=0),
            "longest_rule_steps": max(
                (len(row["steps"]) for row in ms["rules"]), default=0),
        },
        "expressive_power_beyond_trusted_primitive_closure": False,
        "expressivity_interpretation":
            "All stored Generic and Meta programs expand to the original "
            "trusted primitive names. New fingerprints or longer words prove "
            "additional explored examples, NOT an extension of the "
            "primitive-composition closure.",
    }


def scheduler_metrics(kind, runs, now):
    offset = 0 if kind == "generic" else 2
    first = WINDOW_BEGIN + timedelta(minutes=offset)
    mature = min(WINDOW_END, now - timedelta(minutes=MATURITY_DELAY_MINUTES))
    expected = 0
    cursor = first
    while cursor <= mature:
        expected += 1
        cursor += timedelta(minutes=10)
    observed_schedule = [r for r in runs if r["event"] == "schedule"
                         and WINDOW_BEGIN <= r["created_at"] <= WINDOW_END +
                         timedelta(minutes=MATURITY_DELAY_MINUTES)]
    observed_dispatch = [r for r in runs if r["event"] == "workflow_dispatch"]
    activity = sorted(runs, key=lambda x: x["created_at"])
    return {
        "nominal_matured_schedule_slots": expected,
        "observed_schedule_events": len(observed_schedule),
        "observed_manual_or_relay_dispatches": len(observed_dispatch),
        "last_observed_run_created_at":
            activity[-1]["created_at"].isoformat() if activity else None,
        "last_observed_run_conclusion":
            activity[-1]["conclusion"] if activity else None,
        "no_scheduled_runs_observed": bool(expected and not observed_schedule),
        "interpretation":
            "Nominal elapsed cron slots are not guaranteed executions; "
            "GitHub may delay or drop scheduled events.",
    }


def dispatch_gate(kind, state, runs, now):
    """One workflow dispatch at most per cooldown, with hard trial cap."""
    if not (WINDOW_BEGIN <= now <= WINDOW_END):
        return {"allowed": False, "reason": "TRIAL_WINDOW_CLOSED"}
    count = len(state["receipts"] if kind == "generic" else state["rules"])
    if count >= EXPECTED_CAP:
        return {"allowed": False, "reason": "TRIAL_CAP_REACHED"}
    current_slot = now.replace(minute=now.minute // 10 * 10, second=0,
                               microsecond=0)
    latest_saved = state["last_utc_day"]
    if latest_saved is not None and "T" in latest_saved:
        if parse_time(latest_saved) >= current_slot:
            return {"allowed": False, "reason": "CURRENT_SLOT_ALREADY_SAVED"}
    if any(row["status"] in {"queued", "requested", "waiting", "pending",
                             "in_progress"} for row in runs):
        return {"allowed": False, "reason": "WORKFLOW_STILL_ACTIVE"}
    recent = [row["created_at"] for row in runs
              if row["created_at"] <= now]
    if recent and (now - max(recent)).total_seconds() < COOLDOWN_SECONDS:
        return {"allowed": False, "reason": "LAST_LAUNCH_INSIDE_COOLDOWN"}
    return {"allowed": True, "reason": "BOUNDED_CATCHUP_ALLOWED"}


def report(gs, ms, runs, now):
    require(now.tzinfo is not None, "missing timezone")
    return {
        "schema_version": SCHEMA,
        "utc_observed_at": now.isoformat(),
        "state": {
            "generic_verified": len(gs["receipts"]),
            "meta_verified": len(ms["rules"]),
            "generic_last_saved": gs["last_utc_day"],
            "meta_last_saved": ms["last_utc_day"],
        },
        "scheduler": {
            key: scheduler_metrics(key, runs[key], now) for key in KNOWN_WORKFLOWS
        },
        "recovery_gate": {
            "generic": dispatch_gate("generic", gs, runs["generic"], now),
            "meta": dispatch_gate("meta", ms, runs["meta"], now),
        },
        "capability": capability(gs, ms),
        "safety": {
            "trial_receipt_limit_each": EXPECTED_CAP,
            "cooldown_seconds": COOLDOWN_SECONDS,
            "trial_ends_utc": WINDOW_END.isoformat(),
            "only_trusted_default_branch_may_dispatch": True,
            "no_untrusted_code_execution": True,
        },
    }


def main(argv=None):
    cli = argparse.ArgumentParser()
    cli.add_argument("--generic-state", type=Path, required=True)
    cli.add_argument("--meta-state", type=Path, required=True)
    cli.add_argument("--generic-runs", type=Path, required=True)
    cli.add_argument("--meta-runs", type=Path, required=True)
    cli.add_argument("--now", required=True)
    cli.add_argument("--output", type=Path, required=True)
    args = cli.parse_args(argv)
    try:
        gs, ms, runs = validated_inputs(
            args.generic_state, args.meta_state,
            args.generic_runs, args.meta_runs)
        result = report(gs, ms, runs, parse_time(args.now))
        gf.save(args.output, result)
        print(json.dumps({
            "generic_saved": result["state"]["generic_verified"],
            "meta_saved": result["state"]["meta_verified"],
            "generic_schedule_events": result["scheduler"]["generic"]["observed_schedule_events"],
            "meta_schedule_events": result["scheduler"]["meta"]["observed_schedule_events"],
            "generic_dispatch": result["recovery_gate"]["generic"],
            "meta_dispatch": result["recovery_gate"]["meta"],
            "meta_rule_reuse":
                result["capability"]["meta"]["descendants_reusing_verified_rules"],
            "primitive_closure_expanded": False,
        }, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError, TypeError, IndexError,
            json.JSONDecodeError) as exc:
        print("FORGE_AUDIT_ERROR: " + str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
