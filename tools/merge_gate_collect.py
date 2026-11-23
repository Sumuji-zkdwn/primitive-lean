#!/usr/bin/env python3
"""Bounded GitHub REST snapshot collector for the read-only Merge Gate.

This script may run only from a trusted main checkout in Actions, with a
read-only GITHUB_TOKEN. PR source bodies are never executed or checked out.
The resulting JSON is a time-bound observation, not merge authorization.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import sys
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

from tools import merge_gate as gate

PAGE_SIZE = 100
MAX_PR_PAGES = 3
MAX_FILE_PAGES = 3
MAX_COMPARE = 45


class API:
    def __init__(self, repository, token):
        gate.insist(isinstance(repository, str) and gate.REPO.fullmatch(repository),
                    "invalid repository")
        gate.insist(isinstance(token, str) and bool(token),
                    "read-only GITHUB_TOKEN is required")
        self.repository = repository
        self.prefix = "/repos/" + repository
        self.token = token

    def get(self, endpoint):
        gate.insist(endpoint.startswith(self.prefix + "/"), "API endpoint out of scope")
        request = Request("https://api.github.com" + endpoint, headers={
            "Accept": "application/vnd.github+json",
            "Authorization": "Bearer " + self.token,
            "User-Agent": "primitive-lean-merge-gate/1",
            "X-GitHub-Api-Version": "2022-11-28",
        })
        with urlopen(request, timeout=20) as response:
            data = response.read(3_000_001)
        gate.insist(len(data) <= 3_000_000, "API response too large")
        return json.loads(data.decode("utf-8"))


def pages(api, endpoint, max_pages):
    rows = []
    for page in range(1, max_pages + 1):
        sep = "&" if "?" in endpoint else "?"
        data = api.get(endpoint + sep + "per_page=100&page=" + str(page))
        gate.insist(type(data) is list and len(data) <= PAGE_SIZE,
                    "malformed API pagination")
        rows.extend(data)
        if len(data) < PAGE_SIZE:
            return rows, True
    return rows, False


def normalize(raw):
    n = raw.get("number")
    head, base = raw.get("head"), raw.get("base")
    gate.insist(gate.pr_number(n) and isinstance(head, dict)
                and isinstance(base, dict), "invalid PR metadata")
    gate.insist(gate.sha_ok(head.get("sha")) and gate.sha_ok(base.get("sha")),
                "unpinned PR SHA")
    return {
        "number": n, "state": raw.get("state"), "draft": raw.get("draft"),
        "head_sha": head["sha"], "base_sha": base["sha"],
        "head_ref": head.get("ref"), "base_ref": base.get("ref"),
        "head_repo": (head.get("repo") or {}).get("full_name"),
        "title": str(raw.get("title") or "")[:160],
        "files": [], "files_complete": False,
        "checks": [], "checks_complete": False, "collection_errors": [],
    }


def gather_files(api, row):
    try:
        data, complete = pages(api, api.prefix + "/pulls/"
                               + str(row["number"]) + "/files", MAX_FILE_PAGES)
        names = set()
        for item in data:
            gate.insist(type(item) is dict, "malformed PR changed file")
            for field in ("filename", "previous_filename"):
                if item.get(field) is not None:
                    name = item[field]
                    gate.insist(type(name) is str and 0 < len(name) <= 1024,
                                "invalid changed filename")
                    names.add(name)
        row["files"] = sorted(names)
        row["files_complete"] = complete and len(names) <= 500
        if not complete:
            row["collection_errors"].append("FILES_PAGE_LIMIT")
    except (HTTPError, URLError, OSError, ValueError) as e:
        row["collection_errors"].append("FILES_UNAVAILABLE:" + type(e).__name__)


def gather_checks(api, row):
    sha = row["head_sha"]
    try:
        data = api.get(api.prefix + "/commits/" + sha + "/check-runs?per_page=100")
        gate.insist(type(data) is dict and type(data.get("check_runs")) is list,
                    "invalid check-run payload")
        count = data.get("total_count")
        gate.insist(type(count) is int and count >= len(data["check_runs"]),
                    "invalid check count")
        for item in data["check_runs"]:
            gate.insist(type(item) is dict and item.get("head_sha") == sha,
                        "check from a different SHA")
            row["checks"].append({
                "head_sha": sha,
                "name": str(item.get("name") or "")[:120],
                "status": item.get("status"),
                "conclusion": item.get("conclusion"),
            })
        row["checks_complete"] = count == len(row["checks"])
        if not row["checks_complete"]:
            row["collection_errors"].append("CHECKS_PAGE_LIMIT")
    except (HTTPError, URLError, OSError, ValueError) as e:
        row["checks"] = []
        row["checks_complete"] = False
        row["collection_errors"].append("CHECKS_UNAVAILABLE:" + type(e).__name__)


def candidate_pairs(prs):
    found = []
    for i, a in enumerate(prs):
        for b in prs[i + 1:]:
            common = set(a["files"]) & set(b["files"])
            base_link = (a.get("head_repo") == b.get("head_repo")
                         and (a.get("base_ref") == b.get("head_ref")
                              or b.get("base_ref") == a.get("head_ref")))
            if common or base_link or a["head_sha"] == b["head_sha"]:
                first, second = sorted((a["number"], b["number"]))
                found.append((-len(common), first, second))
    return sorted(set(found))


def collect(api, limit=24, focus=(), controller_sha=None):
    gate.insist(type(limit) is int and 1 <= limit <= 40, "limit must be 1..40")
    gate.insist(type(focus) in (list, tuple) and len(focus) <= 6
                and all(gate.pr_number(i) for i in focus), "invalid focus numbers")
    gate.insist(controller_sha is None or gate.sha_ok(controller_sha),
                "invalid controller SHA")
    main = api.get(api.prefix + "/branches/main")
    main_sha = (main.get("commit") or {}).get("sha")
    gate.insist(gate.sha_ok(main_sha), "unable to pin main")
    data, complete = pages(
        api, api.prefix + "/pulls?state=open&sort=updated&direction=desc",
        MAX_PR_PAGES)
    items = {}
    for raw in data:
        row = normalize(raw)
        gate.insist(row["state"] == "open" and type(row["draft"]) is bool,
                    "non-open or incomplete PR metadata")
        items[row["number"]] = row
    selected = list(items.values())[:limit]
    seen = {row["number"] for row in selected}
    errors = []
    for n in sorted(set(focus)):
        if n in seen:
            continue
        target = items.get(n)
        if target is None and not complete:
            try:
                raw = api.get(api.prefix + "/pulls/" + str(n))
                if raw.get("state") == "open":
                    target = normalize(raw)
            except (HTTPError, URLError, OSError, ValueError) as e:
                errors.append("FOCUS_FETCH_FAILED:" + str(n) + ":" + type(e).__name__)
        if target is not None:
            selected.append(target)
            seen.add(n)
        else:
            errors.append("FOCUS_NOT_OPEN_OR_UNAVAILABLE:" + str(n))
    selected.sort(key=lambda row: row["number"])
    for row in selected:
        gather_files(api, row)
        gather_checks(api, row)
    lookup = {r["number"]: r for r in selected}
    comparisons = []
    for index, (_, a, b) in enumerate(candidate_pairs(selected)):
        if index >= MAX_COMPARE:
            comparisons.append({"a": a, "b": b, "status": "BUDGET_EXHAUSTED"})
            continue
        if lookup[a]["head_sha"] == lookup[b]["head_sha"]:
            comparisons.append({"a": a, "b": b, "status": "identical",
                                "ahead_by": 0, "behind_by": 0,
                                "merge_base_sha": lookup[a]["head_sha"]})
            continue
        try:
            data = api.get(api.prefix + "/compare/"
                           + lookup[a]["head_sha"] + "..." + lookup[b]["head_sha"])
            gate.insist(type(data) is dict, "invalid compare response")
            comparisons.append({
                "a": a, "b": b, "status": data.get("status"),
                "ahead_by": data.get("ahead_by"), "behind_by": data.get("behind_by"),
                "merge_base_sha": (data.get("merge_base_commit") or {}).get("sha"),
            })
        except (HTTPError, URLError, OSError, ValueError) as e:
            comparisons.append({"a": a, "b": b,
                                "status": "COMPARE_UNAVAILABLE:" + type(e).__name__})
    return {
        "schema_version": 1, "kind": "GITHUB_LIVE_READ_ONLY_SNAPSHOT",
        "repository": api.repository, "main_sha": main_sha,
        "controller_sha": controller_sha,
        "observed_at_utc": datetime.now(timezone.utc).isoformat(),
        "observed_open_prs": len(items),
        "open_inventory_complete": complete,
        "selected_prs_complete": complete and len(selected) == len(items),
        "selection_limit": limit, "focus": sorted(set(focus)),
        "prs": selected, "comparisons": comparisons, "collection_errors": errors,
    }


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", required=True)
    p.add_argument("--limit", type=int, default=24)
    p.add_argument("--focus", default="")
    p.add_argument("--controller-sha")
    p.add_argument("--snapshot", type=Path, required=True)
    p.add_argument("--report", type=Path, required=True)
    p.add_argument("--markdown", type=Path, required=True)
    args = p.parse_args(argv)
    try:
        focus = [] if not args.focus else [int(n) for n in args.focus.split(",")]
        api = API(args.repo, os.environ.get("GH_TOKEN"))
        snapshot = collect(api, args.limit, focus, args.controller_sha)
        gate.write_json(args.snapshot, snapshot)
        report = gate.analyze(snapshot)
        gate.write_json(args.report, report)
        args.markdown.parent.mkdir(parents=True, exist_ok=True)
        args.markdown.write_text(gate.render(report), encoding="utf-8")
        print(json.dumps({"selected": report["selected_prs"],
                          "ancestors": report["ancestry_edges"],
                          "read_only": True,
                          "auto_merges": 0, "approval_granted": False}))
    except (ValueError, OSError, HTTPError, URLError, KeyError, TypeError,
            json.JSONDecodeError) as e:
        print("MERGE_GATE_COLLECTION_FAILED_CLOSED:", type(e).__name__, str(e),
              file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
