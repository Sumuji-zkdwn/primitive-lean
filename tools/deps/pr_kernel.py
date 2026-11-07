#!/usr/bin/env python3
"""Kernel-level extraction for one PR head (used by the PR inventory).

Steps, all inside a git worktree of the PR head:
  1. Run the head's own `tools/verify.py --proof-only` (builds Elastica, the joint
     check and the registered supplements, writing MainResult.lean).
  2. Compile MainResult.lean to PrimitiveMain.olean.
  3. Compile the PR's own unregistered `.inc` probes on top of it (ExtraProbe), and
     its own `lean/**/*.lean` modules in import order.
  4. Run ExtractDeps over all of them and analyze.py with the module map.
Failures are recorded per step; nothing is retried or patched.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path

TOOLS = Path(__file__).resolve().parent


def run(cmd, cwd, log, env=None):
    t = time.monotonic()
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, env=env)
    Path(log).write_text(p.stdout + p.stderr)
    return dict(cmd=cmd if isinstance(cmd, str) else " ".join(cmd), exit=p.returncode,
                seconds=round(time.monotonic() - t, 1), log=str(log))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--worktree", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--own", nargs="*", default=[], help="own Lean source paths (relative)")
    a = ap.parse_args()
    wt, work = Path(a.worktree).resolve(), Path(a.work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    lean = wt / "lean"
    env = dict(os.environ)
    status = dict(steps={})
    S = status["steps"]

    S["proof_only"] = run(["python3", "-B", "-X", "utf8", "tools/verify.py", "--proof-only"], wt, work / "proof_only.log")
    main_result = wt / "linear_input/lean_check/MainResult.lean"
    report = wt / "verification/main-result.json"
    ok = S["proof_only"]["exit"] == 0 and main_result.is_file() and report.is_file()
    status["proof_only_passed"] = ok
    if not ok:
        (work / "status.json").write_text(json.dumps(status, indent=1))
        return
    shutil.copy(main_result, work / "PrimitiveMain.lean")
    S["compile_main"] = run(["lake", "env", "lean", f"--root={work}", "-o", str(work / "PrimitiveMain.olean"),
                             str(work / "PrimitiveMain.lean")], lean, work / "compile_main.log")
    lp = f"LEAN_PATH=$LEAN_PATH:{work}"
    modules, module_sources = ["PrimitiveMain"], {}

    registered = set(re.findall(r"'(linear_input/lean_check/[^']+\.inc)'",
                                (wt / "tools/verify_main_result.py").read_text()))
    probes = [p for p in a.own if p.endswith(".inc") and p not in registered and not p.startswith("lean/")]
    if probes:
        text = "import PrimitiveMain\n\n" + "\n\n".join((wt / p).read_text() for p in probes)  # caller passes ancestry order
        (work / "ExtraProbe.lean").write_text(text)
        S["compile_probes"] = run(["lake", "env", "sh", "-c", f"{lp} lean --root={work} -o {work}/ExtraProbe.olean {work}/ExtraProbe.lean"],
                                  lean, work / "compile_probes.log")
        if S["compile_probes"]["exit"] == 0:
            modules.append("ExtraProbe")
            module_sources["ExtraProbe"] = "+".join(probes)

    own_lean = [p for p in a.own if p.startswith("lean/") and p.endswith(".lean")]
    mods = {p[len("lean/"):-len(".lean")].replace("/", "."): p for p in own_lean}
    deps = {}
    for m, p in mods.items():
        src = (wt / p).read_text()
        deps[m] = [l.split()[1] for l in src.splitlines() if l.startswith("import ") and l.split()[1] in mods]
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for d in deps[m]:
            visit(d)
        order.append(m)
    for m in sorted(mods):
        visit(m)
    for m in order:
        out = work / (m.replace(".", "/") + ".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        key = "compile_" + m
        S[key] = run(["lake", "env", "sh", "-c", f"{lp} lean --root={lean} -o {out} {wt / mods[m]}"],
                     lean, work / (key + ".log"))
        if S[key]["exit"] == 0:
            modules.append(m)
            module_sources[m] = mods[m]

    prefixes = ["Elastica", *modules]
    S["extract"] = run(["lake", "env", "sh", "-c",
                        f"{lp} lean --run {TOOLS}/ExtractDeps.lean {work}/raw.json {' '.join(modules)} -- {' '.join(prefixes)}"],
                       lean, work / "extract.log")
    if S["extract"]["exit"] == 0:
        cmd = ["python3", str(TOOLS / "analyze.py"), "--raw", str(work / "raw.json"),
               "--assembled", str(work / "PrimitiveMain.lean"), "--report", str(report),
               "--out", str(work / "deps.json"), "--root", str(wt)]
        for m, s in module_sources.items():
            cmd += ["--module-source", f"{m}={s}"]
        S["analyze"] = run(cmd, wt, work / "analyze.log")
    status["modules"] = modules
    status["module_sources"] = module_sources
    (work / "status.json").write_text(json.dumps(status, indent=1))


if __name__ == "__main__":
    main()
