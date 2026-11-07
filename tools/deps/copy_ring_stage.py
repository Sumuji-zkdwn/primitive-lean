#!/usr/bin/env python3
"""Second stage of the copy check: equal up to algebra, not only up to unfolding.

For every pair whose types are definitionally equal but whose constants were
not identified by `isDefEq`, emit
    theorem cp_k : C = I := by
      repeat' (apply funext; intro)
      simp only [C, I]
      ring
into one Lean file per environment, compile it, and read which theorems failed.
A success proves C = I. A failure only means this tactic script did not prove it.
Private names cannot be referenced from another file and are reported as skipped.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pairs", required=True, help="CopyCheck output JSON")
    ap.add_argument("--imports", nargs="+", required=True)
    ap.add_argument("--lean-path", required=True, help="extra LEAN_PATH entries, ':'-separated")
    ap.add_argument("--lean-dir", required=True, help="the project's lean/ directory (for lake env)")
    ap.add_argument("--work", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    rows = json.loads(Path(a.pairs).read_text())["rows"]
    todo, skipped = [], []
    for r in rows:
        if r["value"] == "definitionally_equal":
            continue
        if r["candidate"].startswith("_private") or r["initial"].startswith("_private"):
            skipped.append(r)
            continue
        todo.append(r)
    work = Path(a.work)
    work.mkdir(parents=True, exist_ok=True)
    lines = [f"import {m}" for m in a.imports] + ["", "set_option maxHeartbeats 200000", ""]
    starts = {}
    for k, r in enumerate(todo):
        starts[k] = len(lines) + 1
        lines += [f"theorem cp_{k} : {r['candidate']} = {r['initial']} := by",
                  "  repeat' (apply funext; intro)",
                  f"  simp only [{r['candidate']}, {r['initial']}]",
                  "  ring", ""]
    src = work / "RingStage.lean"
    src.write_text("\n".join(lines) + "\n")
    p = subprocess.run(["lake", "env", "sh", "-c", f"LEAN_PATH=$LEAN_PATH:{a.lean_path} lean {src}"],
                       cwd=a.lean_dir, capture_output=True, text=True)
    log = p.stdout + p.stderr
    (work / "ring_stage.log").write_text(log)
    err_lines = {int(m.group(1)) for m in re.finditer(r"RingStage\.lean:(\d+):\d+: error", log)}
    bounds = sorted(starts.items(), key=lambda kv: kv[1])
    failed = set()
    for ln in err_lines:
        owner = max((k for k, s in bounds if s <= ln), default=None)
        if owner is not None:
            failed.add(owner)
    result = []
    for k, r in enumerate(todo):
        result.append(dict(candidate=r["candidate"], initial=r["initial"],
                           ring_stage="proved_equal" if k not in failed else "not_proved"))
    out = dict(proved_equal=sum(x["ring_stage"] == "proved_equal" for x in result),
               attempted=len(result), skipped_private=len(skipped),
               compile_exit=p.returncode, rows=result,
               skipped=[dict(candidate=r["candidate"], initial=r["initial"]) for r in skipped])
    Path(a.out).write_text(json.dumps(out, ensure_ascii=False, indent=1))
    print(json.dumps({k: v for k, v in out.items() if k not in ("rows", "skipped")}))


if __name__ == "__main__":
    main()
