#!/usr/bin/env python3
"""Attribute kernel-level new declarations to each open PR and summarise them.

Inputs: main's deps.json, the structural inventory, CI runs per head, and the
kernel deps.json of each compiled tip. A PR's content is the set of new
declarations (names absent from main) whose source file is one of the PR's
own units. Closures are computed over all edge kinds inside the tip graph.

Every number here is about occurrences in accepted terms. "Does not reach
main" never means "cannot be derived from main".
"""
from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path


def closure(adj, start):
    seen, stack = set(), [start]
    while stack:
        x = stack.pop()
        for y in adj.get(x, ()):
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return seen


def sources_of(node):
    s = node.get("source") or ""
    return set(s.split("+"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--main-deps", required=True)
    ap.add_argument("--structure", required=True)
    ap.add_argument("--ci", required=True)
    ap.add_argument("--kernel-dir", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    M = json.loads(Path(a.main_deps).read_text())["nodes"]
    S = json.loads(Path(a.structure).read_text())
    CI = json.loads(Path(a.ci).read_text())
    P = {p["number"]: p for p in S["prs"]}
    main_names = set(M)

    tips = {}
    for d in sorted(Path(a.kernel_dir).iterdir()):
        st = d / "status.json"
        dep = d / "deps.json"
        status = json.loads(st.read_text()) if st.exists() else None
        tips[int(d.name)] = dict(status=status, nodes=json.loads(dep.read_text())["nodes"] if dep.exists() else None)

    def tip_for(n):
        units = {(u["path"], u["blob"]) for u in P[n]["units"]}
        best = None
        for t, info in tips.items():
            if info["nodes"] is None:
                continue
            tu = {(u["path"], u["blob"]) for u in P[t]["units"]}
            if units <= tu and (best is None or len(tu) < len({(u["path"], u["blob"]) for u in P[best]["units"]})):
                best = t
        return best

    rows = {}
    new_name_owner = collections.defaultdict(set)
    for n, p in sorted(P.items()):
        own_paths = {u["path"] for u in p["own_units"]}
        t = tip_for(n) if own_paths else None
        r = dict(number=n, title=p["title"], parent_pr=p["parent_pr"], head=p["head"],
                 behind_main=p["behind_main"], own_files=sorted(own_paths),
                 lexical_theorems=p["own_theorem_count"], non_lean_changes=p["non_lean_changes"],
                 ci=[dict(name=x["name"], conclusion=x["conclusion"]) for x in CI.get(str(n), [])],
                 kernel_tip=t)
        if own_paths and t is None:
            st = tips.get(n, {}).get("status") if n in tips else None
            r["kernel"] = dict(status="not_compiled" if st is None else "failed",
                               failed_steps={k: v["exit"] for k, v in (st or {}).get("steps", {}).items() if v["exit"] != 0})
            rows[n] = r
            continue
        if not own_paths:
            r["kernel"] = dict(status="no_lean_content")
            rows[n] = r
            continue
        N = tips[t]["nodes"]
        adj = {k: set(v["direct"]["proof"]) | set(v["direct"]["statement"]) | set(v["direct"]["definition"])
               for k, v in N.items()}
        proof_adj = {k: set(v["direct"]["proof"]) for k, v in N.items()}
        new = {k: v for k, v in N.items() if k not in main_names and sources_of(v) & own_paths}
        thms = {k: v for k, v in new.items() if v["kind"] == "theorem"}
        uses_main = uses_main_proof = reaches_initial = 0
        main_targets = collections.Counter()
        for k in thms:
            c = closure(adj, k)
            cm = c & main_names
            if cm:
                uses_main += 1
            if any(N.get(x, {}).get("layer") == "initial" for x in c):
                reaches_initial += 1
            pc = closure(proof_adj, k)
            pm = {x for x in pc & main_names if M[x]["kind"] == "theorem"}
            if pm:
                uses_main_proof += 1
                main_targets.update(pm)
        shapes = collections.Counter(v["proof_shape"] for v in thms.values())
        depth = [v["proof_depth"] for v in thms.values() if v["proof_depth"] is not None]
        for k in new:
            new_name_owner[k].add(n)
        r["kernel"] = dict(
            status="ok", new_theorems=len(thms), new_definitions=len(new) - len(thms),
            theorems_using_main_any_edge=uses_main, theorems_using_main_theorem_in_proof=uses_main_proof,
            theorems_reaching_initial=reaches_initial, shapes=dict(shapes),
            max_proof_depth=max(depth) if depth else None,
            most_used_main_theorems=main_targets.most_common(5),
            new_names=sorted(new))
        rows[n] = r

    # Kernel-level duplicate names across PRs (same declaration name introduced by several PRs).
    dup = {k: sorted(v) for k, v in new_name_owner.items() if len(v) > 1}
    for r in rows.values():
        names = r.get("kernel", {}).get("new_names", [])
        r["kernel"]["names_shared_with_other_prs"] = sorted({o for k in names for o in dup.get(k, []) if o != r["number"]}) if names else []
    out = dict(main_nodes=len(M), prs=rows, duplicate_names=len(dup),
               scope=("Kernel occurrences only. Not reaching main is not a non-derivability claim; "
                      "a single-theorem application is a term-shape heuristic, not a novelty verdict."))
    Path(a.out).write_text(json.dumps(out, ensure_ascii=False, indent=1))
    print(json.dumps(dict(prs=len(rows), kernel_ok=sum(r["kernel"]["status"] == "ok" for r in rows.values()),
                          duplicate_names=len(dup)), ensure_ascii=False))


if __name__ == "__main__":
    main()
