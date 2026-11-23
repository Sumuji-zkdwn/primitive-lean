#!/usr/bin/env python3
"""GitHub-only watchdog for the existing bounded autonomous research loops.

No Chat, Codex, hosted language-model call, automatic merge or arbitrary
execution of state-branch content. It retries at most one MISSING daily
workflow by workflow_dispatch, never a failed or already running one.
"""
from __future__ import annotations

import argparse
import base64
from dataclasses import dataclass
from datetime import date, datetime, timezone
import json
import os
from pathlib import Path
import re
import urllib.parse
import urllib.request


@dataclass(frozen=True)
class Track:
    name: str
    workflow: str
    branch: str
    state_file: str


# This fixed list is a capability boundary: state files and API responses
# cannot choose a different workflow, ref or GitHub API endpoint to invoke.
TRACKS = (
    Track("research-conveyor", "research-conveyor.yml",
          "autonomy/research-conveyor-state", "docs/autonomy/conveyor-state.json"),
    Track("finite-discovery", "finite-discovery.yml",
          "autonomy/finite-discovery-state", "docs/autonomy/finite-discovery-state.json"),
    Track("strategy-evolution", "strategy-evolution.yml",
          "autonomy/strategy-evolution-state", "docs/autonomy/strategy-evolution-state.json"),
    Track("definition-foundry", "definition-foundry.yml",
          "autonomy/definition-foundry-state", "docs/autonomy/definition-foundry-state.json"),
    Track("research-scout", "research-scout.yml",
          "autonomy/research-scout-state", "docs/autonomy/scout-state.json"),
)
RUN_EVENTS = frozenset({"schedule", "workflow_dispatch"})
ACTIVE = frozenset({"queued", "in_progress", "waiting", "pending", "requested"})
MAX_RESPONSE_BYTES = 2_000_000


def iso_day(value: str) -> date:
    """Fail closed on malformed or timezone-free API timestamps."""
    stamp = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if stamp.tzinfo is None:
        raise ValueError("timestamp has no timezone")
    return stamp.astimezone(timezone.utc).date()


def evaluate(runs: list[dict], day: date) -> dict:
    """Decide whether a track needs a missing-run recovery, never a retry."""
    relevant = [r for r in runs if r.get("event") in RUN_EVENTS
                and r.get("head_branch") == "main"]
    relevant.sort(key=lambda r: r.get("created_at", ""), reverse=True)
    today = [r for r in relevant if iso_day(r["created_at"]) == day]
    latest = relevant[0] if relevant else None
    if any(r.get("status") in ACTIVE for r in relevant):
        result = "IN_PROGRESS"
    elif today:
        # A failing latest attempt must be fixed, not blindly restarted.
        newest = today[0]
        result = ("RUN_SUCCESS" if newest.get("conclusion") == "success"
                  else "FAILED_TODAY")
    else:
        result = "MISSING_TODAY"
    return {
        "status": result,
        "latest": ({"created_at": latest["created_at"],
                    "event": latest.get("event"),
                    "conclusion": latest.get("conclusion"),
                    "url": latest.get("html_url")} if latest else None),
    }


def summarize_ledger(data: dict, track: Track) -> dict:
    """Read a ledger as *data*. Never import or execute it."""
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        raise ValueError("unknown or malformed state schema: " + track.name)
    if track.name == "research-scout":
        queue = data.get("queue")
        if not isinstance(queue, list) or len(queue) > 100_000:
            raise ValueError("bad research-scout queue")
        return {"records": len(queue), "last_day": data.get("last_ai_day"),
                "meaning": "unverified research leads"}
    field = "results" if track.name == "research-conveyor" else "receipts"
    records = data.get(field)
    if not isinstance(records, list) or len(records) > 100_000:
        raise ValueError("bad state receipts: " + track.name)
    return {"records": len(records),
            "last_day": data.get("last_utc_day"),
            "meaning": "verified finite receipts"}


def decide(snapshot: list[dict]) -> dict:
    """Deterministic priority; at most ONE recovered workflow per invocation."""
    if len(snapshot) != len(TRACKS):
        raise ValueError("incomplete watchdog snapshot")
    expected = [t.name for t in TRACKS]
    if [row.get("name") for row in snapshot] != expected:
        raise ValueError("unknown or reordered watchdog tracks")
    targets = [row for row in snapshot if row["run"]["status"] == "MISSING_TODAY"]
    chosen = targets[0]["name"] if targets else None
    return {"action": "DISPATCH_ONE_MISSING_WORKFLOW" if chosen else "NO_ACTION",
            "track": chosen, "selected": chosen is not None,
            "candidate_count": len(targets)}


class GitHub:
    def __init__(self, repository: str, token: str):
        if (not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository)
                or any(part in (".", "..") or ".." in part
                       for part in repository.split("/"))):
            raise ValueError("invalid fixed repository identifier")
        if not token:
            raise ValueError("GITHUB_TOKEN is required")
        self.repo = repository
        self.token = token

    def request(self, method: str, path: str, payload: dict | None = None):
        if not path.startswith("/repos/" + self.repo + "/"):
            raise ValueError("API path must remain within the selected repository")
        raw = None if payload is None else json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            "https://api.github.com" + path,
            data=raw, method=method,
            headers={
                "Authorization": "Bearer " + self.token,
                "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28",
                **({"Content-Type": "application/json"} if raw is not None else {}),
            })
        with urllib.request.urlopen(req, timeout=25) as response:
            text = response.read(MAX_RESPONSE_BYTES + 1)
            if len(text) > MAX_RESPONSE_BYTES:
                raise ValueError("API response unexpectedly large")
            return json.loads(text) if text.strip() else None

    def state(self, track: Track) -> dict:
        path = urllib.parse.quote(track.state_file, safe="/")
        ref = urllib.parse.quote(track.branch, safe="")
        body = self.request("GET", f"/repos/{self.repo}/contents/{path}?ref={ref}")
        if body.get("encoding") != "base64" or not isinstance(body.get("content"), str):
            raise ValueError("state file is not GitHub Contents base64: " + track.name)
        decoded = base64.b64decode(body["content"], validate=False)
        if len(decoded) > MAX_RESPONSE_BYTES:
            raise ValueError("state data unexpectedly large")
        return json.loads(decoded.decode("utf-8"))

    def runs(self, track: Track) -> list[dict]:
        # Query both types separately so a flood of PR runs cannot hide the
        # daily schedule or a prior watchdog dispatch in a short API page.
        combined = {}
        for event in ("schedule", "workflow_dispatch"):
            path = (f"/repos/{self.repo}/actions/workflows/{track.workflow}/runs"
                    f"?branch=main&event={event}&per_page=10")
            response = self.request("GET", path)
            if not isinstance(response, dict) or not isinstance(response.get("workflow_runs"), list):
                raise ValueError("unexpected GitHub workflow-run response")
            for run in response["workflow_runs"]:
                combined[run["id"]] = run
        return list(combined.values())

    def dispatch(self, track: Track):
        # GitHub deliberately permits GITHUB_TOKEN workflow_dispatch to
        # start a new run; never use push or pull_request for recursion.
        self.request(
            "POST", f"/repos/{self.repo}/actions/workflows/{track.workflow}/dispatches",
            {"ref": "main"})


def collect(api: GitHub, day: date) -> list[dict]:
    rows = []
    for track in TRACKS:
        rows.append({"name": track.name, "workflow": track.workflow,
                     "ledger": summarize_ledger(api.state(track), track),
                     "run": evaluate(api.runs(track), day)})
    return rows


def markdown(day: date, rows: list[dict], decision: dict, dispatched: bool) -> str:
    lines = [f"## GitHub-only research supervisor — {day.isoformat()} (UTC)", "",
             "All tracks run without Chat/Codex. This supervisor never merges code.",
             "", "| Track | Last scheduled/dispatch run | Verified records / leads |",
             "|---|---|---:|"]
    for row in rows:
        info = row["run"]
        lines.append(f"| {row['name']} | {info['status']} | {row['ledger']['records']} |")
    lines += ["", "Decision: **" + decision["action"] + "**",
              "Selected: " + str(decision["track"] or "none"),
              "Recovery dispatched: **" + str(dispatched).lower() + "**",
              "", "A missing run may be recovered once; a failed run is not retried.",
              "A successful run is not proof of new mathematics or physics."]
    return "\n".join(lines) + "\n"


def run(argv: list[str] | None = None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--day", required=True, help="ISO UTC date")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--dispatch", action="store_true",
                        help="Allow one recovery dispatch on the trusted main job")
    args = parser.parse_args(argv)
    day = date.fromisoformat(args.day)
    if day != datetime.now(timezone.utc).date():
        # Does not allow a caller to replay old days into a fresh dispatch.
        if args.dispatch:
            raise ValueError("dispatch date must be the current UTC day")
    api = GitHub(args.repository, os.environ.get("GH_TOKEN", ""))
    rows = collect(api, day)
    decision = decide(rows)
    dispatched = False
    if args.dispatch and decision["selected"]:
        track = next(t for t in TRACKS if t.name == decision["track"])
        api.dispatch(track)
        dispatched = True
    result = {"schema_version": 1, "day": day.isoformat(),
              "tracks": rows, "decision": decision, "dispatched": dispatched,
              "scope": "EXISTING_FINITE_WORKFLOWS_ONLY"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2)
                           + "\n", encoding="utf-8")
    report = markdown(day, rows, decision, dispatched)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as file:
            file.write(report)
    print(report, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(run())
