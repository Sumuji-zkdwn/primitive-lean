#!/usr/bin/env python3
"""Read-only pull-request integration planner.

Inputs are bounded, source-pinned JSON observations. No command in this
module merges, edits, comments on, or closes a pull request. File overlap
is not a claim of an actual three-way textual merge conflict. The output
is NEVER an approval to merge.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re
import sys

SHA = re.compile(r"[a-f0-9]{40}\Z")
REPO = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\Z")
MAX_PRS = 46


def insist(ok, why):
    if not ok:
        raise ValueError(why)


def sha_ok(x):
    return type(x) is str and bool(SHA.fullmatch(x))


def pr_number(x):
    return type(x) is int and 0 < x < 1_000_000_000


def read_json(path):
    insist(path.is_file() and not path.is_symlink(), "snapshot must be a regular file")
    insist(path.stat().st_size < 6_000_000, "snapshot exceeds size cap")
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
                    encoding="utf-8")


def validate(s):
    insist(type(s) is dict and s.get("schema_version") == 1, "invalid schema")
    insist(type(s.get("repository")) is str and REPO.fullmatch(s["repository"]),
           "invalid repository")
    insist(sha_ok(s.get("main_sha")), "untrusted main revision")
    prs, comparisons = s.get("prs"), s.get("comparisons")
    insist(type(prs) is list and len(prs) <= MAX_PRS, "PR collection too large")
    insist(type(comparisons) is list and len(comparisons) <= 1000,
           "comparison collection too large")
    seen = set()
    for row in prs:
        insist(type(row) is dict and pr_number(row.get("number")),
               "invalid PR number")
        n = row["number"]
        insist(n not in seen, "duplicate PR")
        seen.add(n)
        insist(sha_ok(row.get("head_sha")) and sha_ok(row.get("base_sha")),
               "unpinned source/target SHA")
        insist(row.get("state") == "open" and type(row.get("draft")) is bool,
               "missing current PR state")
        insist(type(row.get("files")) is list
               and len(row["files"]) <= 500
               and all(type(p) is str and 0 < len(p) <= 1024 for p in row["files"]),
               "invalid file inventory")
        insist(type(row.get("files_complete")) is bool, "unknown file completeness")
        insist(type(row.get("checks_complete")) is bool, "unknown check completeness")
        insist(type(row.get("checks")) is list and len(row["checks"]) <= 100,
               "invalid check inventory")
        for check in row["checks"]:
            insist(type(check) is dict and check.get("head_sha") == row["head_sha"],
                   "check not from exact head SHA")
    pairs = set()
    for comp in comparisons:
        insist(type(comp) is dict and pr_number(comp.get("a"))
               and pr_number(comp.get("b")), "invalid comparison")
        pair = (comp["a"], comp["b"])
        insist(pair[0] < pair[1] and pair[0] in seen and pair[1] in seen,
               "untracked comparison pair")
        insist(pair not in pairs, "duplicate comparison")
        pairs.add(pair)


def check_state(pr):
    if not pr["checks_complete"]:
        return "CHECK_INVENTORY_INCOMPLETE"
    if not pr["checks"]:
        return "NO_EXACT_HEAD_CHECKS"
    if any(x.get("status") != "completed" for x in pr["checks"]):
        return "CI_PENDING"
    if any(x.get("conclusion") in
           ("failure", "timed_out", "cancelled", "action_required", "startup_failure")
           for x in pr["checks"]):
        return "CI_FAILURE"
    if all(x.get("conclusion") == "success" for x in pr["checks"]):
        return "CI_SUCCESS_OBSERVED_ONLY"
    return "CI_NOT_ALL_SUCCESS"


def pair_relation(a, b, comparison):
    overlap = sorted(set(a["files"]) & set(b["files"]))
    if a["head_sha"] == b["head_sha"]:
        return "DUPLICATE_HEAD", None, overlap
    if not comparison:
        return ("OVERLAP_UNVERIFIED" if overlap else "DISJOINT_NOT_SEMANTICALLY_CLEARED"), None, overlap
    state, base = comparison.get("status"), comparison.get("merge_base_sha")
    ahead, behind = comparison.get("ahead_by"), comparison.get("behind_by")
    if (state == "ahead" and type(ahead) is int and ahead > 0
            and behind == 0 and base == a["head_sha"]):
        return "PROVED_ANCESTRY", (a["number"], b["number"]), overlap
    if (state == "behind" and type(behind) is int and behind > 0
            and ahead == 0 and base == b["head_sha"]):
        return "PROVED_ANCESTRY", (b["number"], a["number"]), overlap
    if overlap and state == "diverged":
        return "OVERLAP_DIVERGED_NEEDS_REVIEW", None, overlap
    return ("OVERLAP_UNVERIFIED" if overlap else "DISJOINT_NOT_SEMANTICALLY_CLEARED"), None, overlap


def order_by_ancestry(numbers, edges):
    children = defaultdict(set)
    degree = {n: 0 for n in numbers}
    for parent, child in edges:
        insist(parent in degree and child in degree and parent != child,
               "invalid ancestry edge")
        if child not in children[parent]:
            children[parent].add(child)
            degree[child] += 1
    queue = sorted(n for n in numbers if degree[n] == 0)
    ordered = []
    while queue:
        head = queue.pop(0)
        ordered.append(head)
        for child in sorted(children[head]):
            degree[child] -= 1
            if degree[child] == 0:
                queue.append(child)
                queue.sort()
    insist(len(ordered) == len(degree), "contradictory ancestry cycle")
    return ordered


def analyze(s):
    validate(s)
    prs = sorted(s["prs"], key=lambda r: r["number"])
    comps = {(r["a"], r["b"]): r for r in s["comparisons"]}
    blockers = {}
    for pr in prs:
        n = pr["number"]
        b = []
        if pr["draft"]:
            b.append("DRAFT")
        if pr.get("base_ref") != "main":
            b.append("TARGET_NOT_MAIN")
        elif pr["base_sha"] != s["main_sha"]:
            b.append("TARGET_SHA_STALE")
        if not pr["files_complete"]:
            b.append("FILES_INCOMPLETE")
        c = check_state(pr)
        if c != "CI_SUCCESS_OBSERVED_ONLY":
            b.append(c)
        if not s.get("selected_prs_complete", False):
            b.append("OPEN_PR_UNIVERSE_PARTIAL")
        blockers[n] = b
    relationships, edges = [], set()
    for i, a in enumerate(prs):
        for b in prs[i + 1:]:
            pair = (a["number"], b["number"])
            kind, edge, overlap = pair_relation(a, b, comps.get(pair))
            if edge is not None:
                edges.add(edge)
                blockers[edge[1]].append("INHERITS_PR_" + str(edge[0]))
                blockers[edge[0]].append("HAS_CHILD_PR_" + str(edge[1]))
            elif kind == "DUPLICATE_HEAD":
                blockers[pair[0]].append("DUPLICATE_HEAD_PR_" + str(pair[1]))
                blockers[pair[1]].append("DUPLICATE_HEAD_PR_" + str(pair[0]))
            elif kind.startswith("OVERLAP_"):
                blockers[pair[0]].append("SHARED_FILES_PR_" + str(pair[1]))
                blockers[pair[1]].append("SHARED_FILES_PR_" + str(pair[0]))
            if (not a["files_complete"] or not b["files_complete"]) and not overlap:
                kind = "UNKNOWN_POSSIBLE_OVERLAP"
            if overlap or edge or kind == "DUPLICATE_HEAD":
                relationships.append({
                    "a": pair[0], "b": pair[1], "relation": kind,
                    "ancestor_edge": list(edge) if edge else None,
                    "shared_count": len(overlap), "shared_files": overlap[:40],
                    "compare_status": comps[pair].get("status") if pair in comps else None,
                })
    order = order_by_ancestry([r["number"] for r in prs], sorted(edges))
    rows = []
    for pr in prs:
        n = pr["number"]
        reasons = sorted(set(blockers[n]))
        if any(x.startswith("SHARED_FILES_") for x in reasons):
            action = "REVIEW_OVERLAP_AND_THREE_WAY_MERGE"
        elif any(x.startswith("INHERITS_PR_") for x in reasons):
            action = "REVIEW_PARENT_FIRST_THEN_REBASE_CHILD"
        elif "OPEN_PR_UNIVERSE_PARTIAL" in reasons or "FILES_INCOMPLETE" in reasons:
            action = "REFRESH_COMPLETE_INVENTORY"
        elif "CI_FAILURE" in reasons:
            action = "REPAIR_AND_RECHECK_EXACT_HEAD"
        elif "DRAFT" in reasons:
            action = "REVIEW_DRAFT"
        else:
            action = "HUMAN_REVIEW_OF_REQUIRED_CHECKS"
        rows.append({
            "number": n, "title": str(pr.get("title") or "")[:160],
            "head_sha": pr["head_sha"], "base_sha": pr["base_sha"],
            "ci_observation": check_state(pr), "draft": pr["draft"],
            "changed_file_count": len(pr["files"]),
            "blockers": reasons, "next_action": action,
            "merge_approval": False,
        })
    return {
        "schema_version": 1, "repository": s["repository"], "main_sha": s["main_sha"],
        "controller_sha": s.get("controller_sha"),
        "observed_at_utc": s.get("observed_at_utc"),
        "source_kind": s.get("kind", "OFFLINE_SAMPLE"),
        "selected_prs": len(prs),
        "observed_open_prs": s.get("observed_open_prs"),
        "selected_prs_complete": bool(s.get("selected_prs_complete", False)),
        "ancestry_edges": [list(x) for x in sorted(edges)],
        "review_order_only": order,
        "relationships": relationships, "pull_requests": rows,
        "collection_errors": s.get("collection_errors", []),
        "approval_granted": False, "automated_merges": 0,
        "outcome": "TRIAGE_ONLY_NO_MERGE_AUTHORIZATION",
    }


def render(report):
    def safe(x):
        return re.sub(r"[\r\n|<>]", " ", str(x)).strip()[:120]
    lines = ["# Merge Gate: PR integration audit", "",
             "Read-only triage, not permission to merge.",
             "Repository: " + safe(report["repository"]),
             "Main SHA: " + report["main_sha"],
             "Selected PRs: " + str(report["selected_prs"]),
             "Full inventory: " + str(report["selected_prs_complete"]), "",
             "## Confirmed ancestry", ""]
    if report["ancestry_edges"]:
        for a, b in report["ancestry_edges"]:
            lines.append("- Parent PR #" + str(a) + " before child PR #" + str(b))
    else:
        lines.append("None established from this snapshot.")
    lines.extend(["", "## Review queue", "",
                  "| PR | Exact-head checks | Blockers | Next action |",
                  "| --- | --- | --- | --- |"])
    for p in report["pull_requests"]:
        n = p["number"]
        label = "[#" + str(n) + "](https://github.com/" + report["repository"] + "/pull/" + str(n) + ")"
        lines.append("| " + label + " | " + safe(p["ci_observation"]) + " | "
                     + safe(", ".join(p["blockers"])) + " | "
                     + safe(p["next_action"]) + " |")
    lines.extend(["", "## Shared files", ""])
    for rel in report["relationships"]:
        lines.append("- #" + str(rel["a"]) + "/#" + str(rel["b"]) + ": "
                     + rel["relation"] + "; " + str(rel["shared_count"]) + " shared paths")
    lines.extend(["", "Overlapping files do not prove a textual conflict. "
                  "A successful check is not a review or required-check audit. "
                  "Disjoint files do not establish semantic independence. "
                  "Incomplete snapshots may omit other PRs.", ""])
    return "\n".join(lines)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--snapshot", type=Path, required=True)
    p.add_argument("--report", type=Path, required=True)
    p.add_argument("--markdown", type=Path, required=True)
    args = p.parse_args(argv)
    result = analyze(read_json(args.snapshot))
    write_json(args.report, result)
    args.markdown.parent.mkdir(parents=True, exist_ok=True)
    args.markdown.write_text(render(result), encoding="utf-8")
    print(json.dumps({"selected_prs": result["selected_prs"],
                      "ancestry_edges": result["ancestry_edges"],
                      "approval_granted": False, "automated_merges": 0}))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print("MERGE_GATE_FAIL_CLOSED:", type(exc).__name__, str(exc), file=sys.stderr)
        sys.exit(2)
