#!/usr/bin/env python3
"""Structural inventory of open PR branches relative to main (git only, no Lean).

Content unit = (path, blob SHA) of a Lean source that a PR head adds or changes
relative to its merge base with main. Stacked PRs contain their parents' units,
so a PR's *own* units are those not present in the head of its base PR.

Outputs per PR: own units, inherited units, lexical declaration names in own
units, registration in the head's supplement registry, and cross-PR relations
(identical units, same path with different bytes, declaration-name clashes).
Lexical names are only an index; kernel-level checks are a separate stage.
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
from pathlib import Path

DECL = re.compile(r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+([^\s({:\[]+)")
NS = re.compile(r"(?m)^namespace\s+([\w.]+)")


def git(*args, cwd):
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True, text=True).stdout


def is_lean_source(path: str) -> bool:
    return path.endswith((".inc", ".lean")) and not path.startswith("lean/.lake/")


def strip_comments(code: str) -> str:
    code = re.sub(r"/-.*?-/", "", code, flags=re.S)
    return re.sub(r"--[^\n]*", "", code)


def declarations(code: str):
    code = strip_comments(code)
    ns = NS.findall(code)
    prefix = ns[0] + "." if len(ns) == 1 else ""
    return sorted({(k, (prefix + n) if not n.startswith(prefix) else n) for k, n in DECL.findall(code)
                   if not (k == "instance" and n.startswith(":"))})


def registry(repo, ref):
    try:
        text = git("show", f"{ref}:tools/verify_main_result.py", cwd=repo)
    except subprocess.CalledProcessError:
        return set()
    return set(re.findall(r"'(linear_input/lean_check/[^']+\.inc)'", text))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--prs", required=True, help="TSV: number, head, base, title")
    ap.add_argument("--main", default="origin/main")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    repo = a.repo
    prs = []
    for line in Path(a.prs).read_text(encoding="utf-8").splitlines():
        num, head, base, title = line.split("\t")
        prs.append(dict(number=int(num), head=head, base=base, title=title))
    by_head = {p["head"]: p for p in prs}
    main_sha = git("rev-parse", a.main, cwd=repo).strip()
    main_reg = registry(repo, a.main)

    units_of = {}
    for p in prs:
        ref = "origin/" + p["head"]
        p["head_sha"] = git("rev-parse", ref, cwd=repo).strip()
        mb = git("merge-base", a.main, ref, cwd=repo).strip()
        p["merge_base"] = mb
        p["behind_main"] = int(git("rev-list", "--count", f"{ref}..{a.main}", cwd=repo))
        changed = git("diff", "--name-status", "--no-renames", mb, ref, cwd=repo).splitlines()
        units, other, vs_main = {}, collections.Counter(), {}
        for row in changed:
            status, path = row.split("\t", 1)
            if status == "D":
                other["deleted"] += 1
                continue
            if is_lean_source(path):
                blob = git("rev-parse", f"{ref}:{path}", cwd=repo).strip()
                try:
                    main_blob = git("rev-parse", f"{a.main}:{path}", cwd=repo).strip()
                except subprocess.CalledProcessError:
                    main_blob = None
                if main_blob == blob:
                    vs_main[path] = "already_in_main"
                    continue  # integrated later through another PR; not this PR's content
                vs_main[path] = "diverges_from_main" if main_blob else "absent_from_main"
                units[path] = blob
            else:
                top = path.split("/")[0] if "/" in path else "(root)"
                other[top] += 1
        p["registered"] = sorted(registry(repo, ref) - main_reg)
        p["non_lean_changes"] = dict(other)
        p["vs_main"] = vs_main
        units_of[p["number"]] = units

    # Own units: not present in the base PR head (when the base is another open PR).
    for p in prs:
        units = units_of[p["number"]]
        parent = by_head.get(p["base"])
        inherited = units_of[parent["number"]] if parent else {}
        own = {k: v for k, v in units.items() if inherited.get(k) != v}
        p["parent_pr"] = parent["number"] if parent else None
        p["units_total"] = len(units)
        p["units"] = [dict(path=k, blob=v) for k, v in sorted(units.items())]
        p["own_units"] = [dict(path=k, blob=v, vs_main=p["vs_main"][k]) for k, v in sorted(own.items())]
        p["already_in_main"] = sorted(k for k, v in p["vs_main"].items() if v == "already_in_main")
        decls = []
        for path, blob in sorted(own.items()):
            code = git("cat-file", "-p", blob, cwd=repo)
            for kind, name in declarations(code):
                decls.append(dict(kind=kind, name=name, path=path))
        p["own_declarations"] = decls
        p["own_theorem_count"] = sum(d["kind"] in ("theorem", "lemma") for d in decls)

    # Cross-PR relations over own units.
    blob_owners = collections.defaultdict(set)
    path_versions = collections.defaultdict(lambda: collections.defaultdict(set))
    name_versions = collections.defaultdict(lambda: collections.defaultdict(set))
    for p in prs:
        for u in p["own_units"]:
            blob_owners[u["blob"]].add(p["number"])
            path_versions[u["path"]][u["blob"]].add(p["number"])
        for d in p["own_declarations"]:
            blob = next(u["blob"] for u in p["own_units"] if u["path"] == d["path"])
            name_versions[d["name"]][blob].add(p["number"])
    identical = [dict(blob=b, prs=sorted(o)) for b, o in blob_owners.items() if len(o) > 1]
    conflicting_paths = [dict(path=k, versions={b: sorted(o) for b, o in v.items()})
                         for k, v in path_versions.items() if len(v) > 1]
    name_clashes = [dict(name=k, versions={b: sorted(o) for b, o in v.items()})
                    for k, v in name_versions.items() if len(v) > 1]

    # Containment between PR heads (all Lean units).
    contains = []
    for p in prs:
        up = set(units_of[p["number"]].items())
        for q in prs:
            if p is q:
                continue
            uq = set(units_of[q["number"]].items())
            if uq and uq < up:
                contains.append([p["number"], q["number"]])

    out = dict(main=main_sha, prs=prs, identical_units=identical,
               same_path_different_bytes=conflicting_paths, declaration_name_clashes=name_clashes,
               strict_containment=contains)
    Path(a.out).write_text(json.dumps(out, ensure_ascii=False, indent=1))
    print(json.dumps(dict(prs=len(prs), identical_units=len(identical),
                          conflicting_paths=len(conflicting_paths), name_clashes=len(name_clashes),
                          containments=len(contains)), ensure_ascii=False))


if __name__ == "__main__":
    main()
