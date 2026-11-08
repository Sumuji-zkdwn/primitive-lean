#!/usr/bin/env python3
"""Offline, fail-closed research lead queue for mainline primitive-lean.

Only mines explicitly unresolved claims in retained research notes. It does NOT
prove, disprove or turn a candidate into a theorem. No network or paid APIs.
State belongs to the isolated autonomy/research-scout-state branch.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

SCHEMA = 1
MAX_QUEUE = 32
MAX_SEEN = 4096
MAX_LINE = 360
MAX_FILE_BYTES = 300_000
SOURCE_DIRS = ("docs/research", "docs/integration")
MARKERS = (
    ("未証明", 9), ("未解決", 9), ("未検証", 8), ("要検証", 8),
    ("未形式化", 8), ("反例探索", 8), ("証明待ち", 9),
    ("open problem", 9), ("not yet proved", 9), ("unproved", 9),
    ("not yet", 7), ("counterexample", 6), ("todo", 5),
)
VALID_ID = re.compile(r"^[a-f0-9]{20}$")
VALID_SHA = re.compile(r"^[0-9a-f]{40}$")
VALID_SOURCE_SHA = re.compile(r"^[0-9a-f]{64}$")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def empty_state() -> dict:
    return {"schema_version": SCHEMA, "last_scanned_head": None,
            "queue": [], "seen": [], "last_ai_day": None,
            "attempts": []}


def load_state(path: Path) -> dict:
    if not path.exists():
        return empty_state()
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict) or obj.get("schema_version") != SCHEMA:
        raise ValueError("invalid scout state schema")
    if not isinstance(obj.get("seen"), list) or not isinstance(obj.get("queue"), list):
        raise ValueError("invalid scout queue or seen list")
    if len(obj["queue"]) > MAX_QUEUE or len(obj["seen"]) > MAX_SEEN:
        raise ValueError("scout state exceeds bounds")
    if any(not isinstance(s, str) or not VALID_ID.fullmatch(s) for s in obj["seen"]):
        raise ValueError("invalid seen ids")
    if len(set(obj["seen"])) != len(obj["seen"]):
        raise ValueError("duplicate seen ids")
    if any(not isinstance(r, dict) or not VALID_ID.fullmatch(str(r.get("id", "")))
           for r in obj["queue"]):
        raise ValueError("invalid queued candidate")
    if len({r["id"] for r in obj["queue"]}) != len(obj["queue"]):
        raise ValueError("duplicate queued candidate")
    for lead in obj["queue"]:
        path = lead.get("path")
        evidence = lead.get("evidence")
        if (not isinstance(path, str) or
                not any(path.startswith(d + "/") for d in SOURCE_DIRS) or
                not path.endswith(".md") or ".." in Path(path).parts or
                not isinstance(evidence, str) or len(evidence) > MAX_LINE or
                not isinstance(lead.get("line"), int) or lead["line"] < 1 or
                not VALID_SOURCE_SHA.fullmatch(str(lead.get("source_sha256", "")))):
            raise ValueError("invalid queued evidence")
        expected = digest((path + "\0" + evidence).encode("utf-8"))[:20]
        if lead["id"] != expected:
            raise ValueError("queued candidate fingerprint mismatch")
    if not isinstance(obj.get("attempts"), list) or len(obj["attempts"]) > 366:
        raise ValueError("invalid attempt ledger")
    return obj


def save(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, sort_keys=True,
                               indent=2) + "\n", encoding="utf-8")


def collect(root: Path) -> list[dict]:
    """Generate ranked *leads* from finite, explicit documentation markers."""
    found: list[dict] = []
    unique: set[str] = set()
    for directory in SOURCE_DIRS:
        base = root / directory
        if not base.is_dir():
            continue
        for path in sorted(base.glob("*.md")):
            if path.is_symlink() or not path.is_file() or path.stat().st_size > MAX_FILE_BYTES:
                continue
            data = path.read_bytes()
            try:
                lines = data.decode("utf-8").splitlines()
            except UnicodeDecodeError:
                continue
            relative = path.relative_to(root).as_posix()
            file_hash = digest(data)
            for no, line in enumerate(lines, 1):
                stripped = " ".join(line.split()).strip()
                if not stripped or len(stripped) > MAX_LINE or stripped.startswith("http"):
                    continue
                weights = [weight for word, weight in MARKERS if word in stripped.lower()]
                if not weights:
                    continue
                key = digest((relative + "\0" + stripped).encode("utf-8"))[:20]
                if key in unique:
                    continue
                unique.add(key)
                found.append({"id": key, "path": relative, "line": no,
                              "source_sha256": file_hash, "evidence": stripped,
                              "priority": max(weights), "status": "UNVERIFIED_LEAD"})
    found.sort(key=lambda r: (-r["priority"], r["path"], r["line"], r["id"]))
    # Prevent one large research file from filling the entire queue.
    by_file: dict[str, int] = {}
    selected: list[dict] = []
    for lead in found:
        if by_file.get(lead["path"], 0) < 3:
            selected.append(lead)
            by_file[lead["path"]] = by_file.get(lead["path"], 0) + 1
    return selected


def scan(root: Path, state: dict, head: str) -> tuple[dict, dict]:
    if not VALID_SHA.fullmatch(head):
        raise ValueError("head must be a complete commit SHA")
    if state["last_scanned_head"] == head:
        return state, {"scanned": False, "added": 0}
    leads = collect(root)
    by_id = {row["id"]: row for row in leads}
    old_queue = [by_id[row["id"]] for row in state["queue"] if row["id"] in by_id]
    occupied = {r["id"] for r in old_queue} | set(state["seen"])
    incoming = [r for r in leads if r["id"] not in occupied]
    remaining = max(0, MAX_QUEUE - len(old_queue))
    state["queue"] = old_queue + incoming[:remaining]
    state["last_scanned_head"] = head
    return state, {"scanned": True, "added": min(len(incoming), remaining),
                   "leads_found": len(leads), "unindexed": max(0, len(incoming)-remaining)}


def reserve(state: dict, day: str, candidate_id: str) -> tuple[dict, dict]:
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", day):
        raise ValueError("day must be UTC YYYY-MM-DD")
    if state.get("last_ai_day") == day:
        raise ValueError("AI reservation already consumed for this UTC day")
    if not state["queue"] or state["queue"][0]["id"] != candidate_id:
        raise ValueError("candidate must be next in persisted queue")
    if candidate_id in state["seen"]:
        raise ValueError("candidate already processed")
    candidate = state["queue"].pop(0)
    state["last_ai_day"] = day
    state["seen"] = (state["seen"] + [candidate_id])[-MAX_SEEN:]
    state["attempts"] = (state["attempts"] + [{"utc_day": day,
                          "candidate_id": candidate_id, "status": "reserved_no_retry"}])[-366:]
    return state, {"schema_version": SCHEMA, "utc_day": day,
                   "main_head": state["last_scanned_head"], "candidate": candidate,
                   "status": "PAID_CALL_RESERVED_NOT_A_PROOF"}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    run = sub.add_parser("scan")
    run.add_argument("--root", type=Path, required=True)
    run.add_argument("--state", type=Path, required=True)
    run.add_argument("--head", required=True)
    run.add_argument("--report", type=Path, required=True)
    booking = sub.add_parser("reserve")
    booking.add_argument("--state", type=Path, required=True)
    booking.add_argument("--day", required=True)
    booking.add_argument("--candidate-id", required=True)
    booking.add_argument("--reservation", type=Path, required=True)
    args = parser.parse_args(argv)
    state = load_state(args.state)
    if args.command == "scan":
        state, info = scan(args.root.resolve(), state, args.head)
        report = {"schema_version": SCHEMA, "main_head": args.head,
                  "queue_count": len(state["queue"]), "next_candidate":
                  state["queue"][0] if state["queue"] else None,
                  "last_ai_day": state.get("last_ai_day"), **info,
                  "proof_status": "NOT_PROVED", "api_called": False}
        save(args.state, state)
        save(args.report, report)
        print(json.dumps(report, ensure_ascii=False))
    else:
        state, reservation = reserve(state, args.day, args.candidate_id)
        save(args.state, state)
        save(args.reservation, reservation)
        print(json.dumps({"reserved": reservation["candidate"]["id"],
                          "day": args.day}))


if __name__ == "__main__":
    main()
