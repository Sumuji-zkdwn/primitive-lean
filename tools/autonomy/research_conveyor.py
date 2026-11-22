#!/usr/bin/env python3
"""Research Conveyor: source-bound finite tasks -> Proof Forge -> audited receipt.

The route is deliberately small and explicit. Existing research text supplies
leads, but does NOT supply executable code or proof. One reviewed adapter
maps a Siphon E observation question onto a finite Z/3Z model. A successful
finite proof is NEVER promoted to the original real/continuous statement.
The previous result selects the next model; all outcomes remain bounded.

Commands:
  prepare --root DIR --state FILE --head SHA --day YYYY-MM-DD --output DIR
  receipt --root DIR --state FILE --head SHA --evidence DIR --output FILE

No GitHub API, subprocess, external inference, network access, branch writes,
or code execution from a research document occurs in this script.
"""
from __future__ import annotations

import argparse
from datetime import date
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

from tools.autonomy import proof_forge, research_scout

SCHEMA = 1
MAX_RECORDS = 6
SOURCE = "docs/research/2026-11-17-siphon-predictive-quotient.md"
REQUIRED_FRAGMENTS = (
    "I(u,v)=v+u^3",
    "E(u,v)=",
    "R(u,v)=(u,v+1)",
    "未検証",
)
ROUTE = "siphon-z3-polynomial-operator-v1"
CLAIM_BOUNDARY = (
    "A finite mod-3 algebraic reduction of the documented polynomial E "
    "and fresh operation R; NOT a theorem about R^2, measured fluids, "
    "the original continuous proof, or an unresolved general statement."
)
LEAD_WORDS = ("未検証", "未形式化", "未証明", "要検証")


def ensure(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data: bytes) -> str:
    return sha256(data).hexdigest()


def json_write(path: Path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False,
                               sort_keys=True) + "\n", encoding="utf-8")


def file_json(path: Path):
    ensure(path.is_file() and not path.is_symlink(), "missing regular JSON file: " + str(path))
    ensure(path.stat().st_size <= 300_000, "overlarge JSON file")
    return json.loads(path.read_text(encoding="utf-8"),
                      object_pairs_hook=proof_forge.object_no_duplicates)


def empty_state():
    return {"schema_version": SCHEMA, "last_utc_day": None,
            "results": [], "last_source_sha": None}


def validate_day(value: str):
    ensure(isinstance(value, str) and bool(re.fullmatch(r"\d{4}-\d{2}-\d{2}", value)),
           "invalid UTC day")
    ensure(date.fromisoformat(value).isoformat() == value, "not a calendar day")


def validate_state(obj):
    ensure(type(obj) is dict and set(obj) == {
        "schema_version", "last_utc_day", "results", "last_source_sha"
    }, "state schema fields invalid")
    ensure(type(obj["schema_version"]) is int and obj["schema_version"] == SCHEMA,
           "state schema version invalid")
    ensure(obj["last_utc_day"] is None or isinstance(obj["last_utc_day"], str),
           "last day type invalid")
    if obj["last_utc_day"] is not None:
        validate_day(obj["last_utc_day"])
    ensure(type(obj["results"]) is list and len(obj["results"]) <= MAX_RECORDS,
           "state history out of bounds")
    ensure(obj["last_source_sha"] is None or
           (type(obj["last_source_sha"]) is str and
            bool(re.fullmatch(r"[0-9a-f]{64}", obj["last_source_sha"]))),
           "source SHA invalid")
    unique, last_day = set(), None
    for record in obj["results"]:
        ensure(type(record) is dict, "nonobject result in state")
        name, day = record.get("task_id"), record.get("utc_day")
        ensure(type(name) is str and bool(re.fullmatch(
            r"siphon_z3_u[012]_(old|fresh)", name)), "invalid result id")
        ensure(name not in unique, "duplicate completed research task")
        unique.add(name)
        validate_day(day)
        ensure(last_day is None or day > last_day, "history days not increasing")
        last_day = day
        for field in ("main_sha", "source_sha256", "model_sha256",
                      "generated_lean_sha256"):
            val = record.get(field)
            length = 40 if field == "main_sha" else 64
            ensure(type(val) is str and bool(re.fullmatch(
                "[0-9a-f]{" + str(length) + "}", val)), "invalid recorded " + field)
        ensure(record.get("status") == "LEAN_VERIFIED_FINITE_ONLY",
               "state contains unverified proof assertion")
        ensure(record.get("kind") in ("EQUIVALENT", "DISTINGUISHABLE"),
               "invalid finite outcome")
    if obj["results"]:
        ensure(obj["last_utc_day"] == last_day,
               "state last day differs from final receipt")
        ensure(obj["last_source_sha"] == obj["results"][-1]["source_sha256"],
               "state last source SHA inconsistent")
    else:
        ensure(obj["last_utc_day"] is None and obj["last_source_sha"] is None,
               "empty state must not have a completed date")
    return obj


def state_load(path: Path):
    return validate_state(file_json(path)) if path.is_file() else empty_state()


def discover_lead(root: Path):
    """Only already-discoverable scout leads may seed this reviewed adapter."""
    path = root / SOURCE
    ensure(path.is_file() and not path.is_symlink(), "Siphon source missing")
    data = path.read_bytes()
    ensure(len(data) <= research_scout.MAX_FILE_BYTES, "source too large")
    text = data.decode("utf-8")
    ensure(all(token in text for token in REQUIRED_FRAGMENTS),
           "reviewed Siphon model semantics changed; adapter must be reviewed")
    leads = [lead for lead in research_scout.collect(root)
             if lead["path"] == SOURCE
             and any(marker in lead["evidence"] for marker in LEAD_WORDS)]
    ensure(bool(leads), "no explicit research-scout lead for reviewed source")
    current_hash = sha(data)
    ensure(all(item["source_sha256"] == current_hash for item in leads),
           "research lead source hash mismatch")
    return sorted(leads, key=lambda x: (-x["priority"], x["line"], x["id"]))[0]


def task_sequence(state):
    """One next task per previous *kernel-certified* outcome."""
    completed = {row["task_id"]: row for row in state["results"]}
    for u in range(3):
        base = f"siphon_z3_u{u}_old"
        fresh = f"siphon_z3_u{u}_fresh"
        if base not in completed:
            return u, "old"
        if completed[base]["kind"] == "EQUIVALENT" and fresh not in completed:
            return u, "fresh"
    return None


def model(u, kind):
    """Exact modular reductions of the fixed polynomial formulas in SOURCE."""
    ensure(type(u) is int and u in (0, 1, 2), "u must be in F3")
    ensure(kind in ("old", "fresh"), "unknown finite operation vocabulary")
    def index(x, y):
        return (x % 3) + 3 * (y % 3)
    def step_E(x, y):
        r = (y + x**3) % 3
        xx = (x + r*r) % 3
        return index(xx, r - xx**3)
    def step_R(x, y):
        return index(x, y + 1)
    rows = [
        [step_E(s % 3, s // 3) for s in range(9)],
    ]
    if kind == "fresh":
        rows.append([step_R(s % 3, s // 3) for s in range(9)])
    left = index(u, 1 - u**3)
    right = index(u, 2 - u**3)
    return {
        "schema_version": 1,
        "name": f"siphon_z3_u{u}_{kind}",
        "observations": [s % 3 for s in range(9)],
        "transitions": rows,
        "pair": [left, right],
    }


def plan(root: Path, state: dict, head: str, day: str):
    ensure(proof_forge.HEAD.fullmatch(head) is not None, "invalid exact commit head")
    validate_day(day)
    validate_state(state)
    if state["last_utc_day"] is not None:
        ensure(day >= state["last_utc_day"], "UTC day moves backwards")
    lead = discover_lead(root)
    if state["last_utc_day"] == day:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "ALREADY_VERIFIED_TODAY",
                "main_sha": head, "day": day}
    next_task = task_sequence(state)
    if next_task is None:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "FINITE_ROUTE_EXHAUSTED_NEEDS_NEW_REVIEWED_ADAPTER",
                "main_sha": head, "day": day}
    u, kind = next_task
    spec = model(u, kind)
    previous = next((r for r in reversed(state["results"])
                     if r["task_id"] == f"siphon_z3_u{u}_old"), None)
    return {
        "schema_version": SCHEMA,
        "candidate": True,
        "task_id": spec["name"],
        "scope": CLAIM_BOUNDARY,
        "route": ROUTE,
        "source": SOURCE,
        "source_sha256": lead["source_sha256"],
        "lead_id": lead["id"],
        "lead_line": lead["line"],
        "lead_evidence": lead["evidence"],
        "main_sha": head, "day": day,
        "previous_result": previous["kind"] if previous else None,
        "hypothesis": "EQUIVALENT" if kind == "old" else "DISTINGUISHABLE",
        "u": u, "vocabulary": kind,
        "model": spec,
    }


def prepare(root: Path, state_path: Path, head: str, day: str, output: Path):
    state = state_load(state_path)
    ensure(not output.exists() or not any(output.iterdir()),
           "output must be initially empty")
    obj = plan(root, state, head, day)
    output.mkdir(parents=True, exist_ok=True)
    if obj["candidate"]:
        path = output / "requests" / (obj["task_id"] + ".json")
        json_write(path, obj["model"])
        ensure(proof_forge.read_request(path) == obj["model"],
               "generated request fails Proof Forge schema")
        proof_forge.generate(output / "requests", output / "proof", head)
        record = file_json(output / "proof" / (obj["task_id"] + ".json"))
        ensure(record["python_result"]["kind"] in ("EQUIVALENT", "DISTINGUISHABLE"),
               "invalid finite observer result")
        obj["python_observation"] = {
            "kind": record["python_result"]["kind"],
            "word": record["python_result"].get("word"),
            "proof_status": "PENDING_KERNEL_VERIFICATION",
        }
    json_write(output / "plan.json", obj)
    print(json.dumps({"candidate": bool(obj["candidate"]),
                      "task_id": obj.get("task_id"),
                      "status": "UNVERIFIED_CANDIDATE" if obj["candidate"]
                      else obj["reason"]}, ensure_ascii=False))
    return obj


def receipt(root: Path, state_path: Path, head: str, evidence: Path, output: Path):
    state = state_load(state_path)
    obj = file_json(evidence / "plan.json")
    ensure(obj.get("candidate") is True, "no candidate to persist")
    ensure(obj.get("main_sha") == head and proof_forge.HEAD.fullmatch(head),
           "unmatched exact source SHA")
    ensure(obj.get("route") == ROUTE and obj.get("source") == SOURCE,
           "unknown task route")
    validate_day(obj["day"])
    ensure(obj["day"] != state["last_utc_day"], "UTC day already recorded")
    ensure(plan(root, state, head, obj["day"])["task_id"] == obj["task_id"],
           "stale or altered plan")
    lead = discover_lead(root)
    ensure(obj["source_sha256"] == lead["source_sha256"],
           "source version changed")
    ensure(obj["lead_id"] == lead["id"] and obj["lead_evidence"] == lead["evidence"],
           "research lead changed")
    spec = model(obj["u"], obj["vocabulary"])
    ensure(obj["model"] == spec, "model was modified after review")
    name = obj["task_id"]
    request = evidence / "requests" / (name + ".json")
    ensure(proof_forge.read_request(request) == spec,
           "request bytes do not match reviewed generator")
    manifest = file_json(evidence / "proof" / "manifest.json")
    record = file_json(evidence / "proof" / (name + ".json"))
    ensure(manifest.get("passed") is True
           and manifest.get("models") == [name]
           and manifest.get("checkout_sha") == head,
           "kernel proof manifest not fully verified")
    ensure(record.get("model") == name
           and record.get("checkout_sha") == head
           and record.get("kernel_verified") is True
           and record.get("status") == "LEAN_VERIFIED"
           and record.get("axiom_audit", {}).get("passed") is True,
           "kernel verification and axiom audit required")
    ensure(record["request_sha256"] == sha(request.read_bytes()),
           "input model sha mismatch")
    source = evidence / "proof" / (name + ".lean")
    ensure(record["generated_lean_sha256"] == sha(source.read_bytes()),
           "Lean source sha mismatch")
    ensure((evidence / "proof" / (name + ".exit")).read_text("utf-8").strip() == "0",
           "Lean kernel did not exit successfully")
    outcome = record["python_result"]
    ensure(outcome["kind"] in ("EQUIVALENT", "DISTINGUISHABLE"),
           "unsupported finite outcome")
    ensure(outcome["kind"] == proof_forge.solve(spec)["kind"],
           "record does not describe the reviewed model")
    if outcome["kind"] == "DISTINGUISHABLE":
        ensure(outcome["word"] == proof_forge.solve(spec)["word"],
               "shortest word mismatch")
    result = {
        "task_id": name, "utc_day": obj["day"],
        "main_sha": head, "source_sha256": lead["source_sha256"],
        "lead_id": lead["id"],
        "model_sha256": record["request_sha256"],
        "generated_lean_sha256": record["generated_lean_sha256"],
        "kind": outcome["kind"],
        "shortest_word": outcome.get("word"),
        "scope": "FINITE_Z3_MODEL_ONLY",
        "status": "LEAN_VERIFIED_FINITE_ONLY",
    }
    state["results"].append(result)
    state["last_utc_day"] = obj["day"]
    state["last_source_sha"] = lead["source_sha256"]
    validate_state(state)
    json_write(output, state)
    print(json.dumps({"accepted": name, "kind": outcome["kind"],
                      "state_entries": len(state["results"]),
                      "next": task_sequence(state)}, ensure_ascii=False))
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    for mode in ("prepare", "receipt"):
        p = sub.add_parser(mode)
        p.add_argument("--root", type=Path, required=True)
        p.add_argument("--state", type=Path, required=True)
        p.add_argument("--head", required=True)
        p.add_argument("--output", type=Path, required=True)
        if mode == "prepare":
            p.add_argument("--day", required=True)
        else:
            p.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        if args.mode == "prepare":
            prepare(args.root.resolve(), args.state, args.head,
                    args.day, args.output)
        else:
            receipt(args.root.resolve(), args.state, args.head,
                    args.evidence, args.output)
    except (ValueError, TypeError, KeyError, OSError,
            UnicodeError, json.JSONDecodeError) as exc:
        print("RESEARCH_CONVEYOR_FAIL_CLOSED:", str(exc), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
