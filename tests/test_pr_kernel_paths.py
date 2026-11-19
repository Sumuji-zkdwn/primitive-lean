"""Argument boundaries of tools/deps/pr_kernel.py (fake lake/lean, no Lean).

Each Lean invocation that needs the work directory first on LEAN_PATH must reach
`lean` with exactly the intended argv and LEAN_PATH, also when the worktree, the
work directory and the tool directory contain spaces or shell metacharacters.
This checks process arguments only: no Lean file is compiled, and the final
analyze step (which needs a real ExtractDeps output) is not checked.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

FAKE_LAKE = """#!/bin/sh
# Stand-in for `lake env CMD...`: install a package LEAN_PATH, then run CMD.
[ "$1" = env ] || exit 90
shift
LEAN_PATH="$FAKE_LAKE_LIB"
export LEAN_PATH
exec "$@"
"""

FAKE_LEAN = """#!{python}
import json, os, sys
from pathlib import Path
args = sys.argv[1:]
with open(os.environ["FAKE_LEAN_LOG"], "a", encoding="utf-8") as f:
    f.write(json.dumps(dict(argv=args, lean_path=os.environ.get("LEAN_PATH"), cwd=os.getcwd())) + "\\n")
if "-o" in args:
    out = Path(args[args.index("-o") + 1])
    if not out.parent.is_dir():
        sys.exit(3)
    out.write_text("fake olean")
for a in args:
    if a.endswith(".lean") and "-o" in args and not Path(a).is_file():
        sys.exit(4)
"""

FAKE_VERIFY = """from pathlib import Path
Path("linear_input/lean_check").mkdir(parents=True, exist_ok=True)
Path("linear_input/lean_check/MainResult.lean").write_text("-- assembled\\n")
Path("verification").mkdir(exist_ok=True)
Path("verification/main-result.json").write_text("{}\\n")
"""


class PrKernelPathTests(unittest.TestCase):
    def kernel_run(self, base_name, gap):
        temp = Path(tempfile.mkdtemp(prefix="pr-kernel-paths-"))
        self.addCleanup(shutil.rmtree, temp)
        base = temp / base_name
        bindir, wt, work = base / "bin", base / f"head{gap}worktree", base / f"work{gap}dir"
        tools = base / f"tool{gap}copy" / "deps"
        lake_lib = base / f"lake{gap}lib"
        for d in (bindir, tools, lake_lib, wt / "tools", wt / "lean" / "Research", wt / "linear_input/lean_check"):
            d.mkdir(parents=True)
        shutil.copy(ROOT / "tools/deps/pr_kernel.py", tools / "pr_kernel.py")
        (bindir / "lake").write_text(FAKE_LAKE)
        (bindir / "lean").write_text(FAKE_LEAN.format(python=sys.executable))
        for exe in ("lake", "lean"):
            (bindir / exe).chmod(0o755)
        (wt / "tools/verify.py").write_text(FAKE_VERIFY)
        (wt / "tools/verify_main_result.py").write_text("SUPPLEMENTS = ['linear_input/lean_check/Registered.inc']\n")
        (wt / "linear_input/lean_check/Probe.inc").write_text("theorem probe : True := trivial\n")
        (wt / "lean/Research/Base.lean").write_text("import PrimitiveMain\n")
        (wt / "lean/Research/Top.lean").write_text("import Research.Base\n")
        log = base / "lean-calls.jsonl"
        env = dict(os.environ, PATH=f"{bindir}{os.pathsep}{os.environ.get('PATH', '')}",
                   FAKE_LAKE_LIB=str(lake_lib), FAKE_LEAN_LOG=str(log))
        env.pop("PR_KERNEL_WORK", None)
        own = ["linear_input/lean_check/Probe.inc", "lean/Research/Top.lean", "lean/Research/Base.lean"]
        p = subprocess.run([sys.executable, "-B", str(tools / "pr_kernel.py"), "--worktree", str(wt),
                            "--work", str(work), "--own", *own], env=env, capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stderr)
        status = json.loads((work / "status.json").read_text())
        calls = [json.loads(l) for l in log.read_text().splitlines()]
        return dict(wt=wt, work=work, tools=tools, lake_lib=lake_lib, status=status, calls=calls)

    def check(self, r):
        wt, work, steps = r["wt"], r["work"], r["status"]["steps"]
        for key in ("proof_only", "compile_main", "compile_probes",
                    "compile_Research.Base", "compile_Research.Top", "extract"):
            self.assertEqual(steps[key]["exit"], 0, (key, steps[key]))
        modules = ["PrimitiveMain", "ExtraProbe", "Research.Base", "Research.Top"]
        self.assertEqual(r["status"]["modules"], modules)
        expected = [
            # compile_main: plain `lake env lean`, no work-first LEAN_PATH.
            ([f"--root={work}", "-o", str(work / "PrimitiveMain.olean"), str(work / "PrimitiveMain.lean")],
             str(r["lake_lib"])),
            ([f"--root={work}", "-o", str(work / "ExtraProbe.olean"), str(work / "ExtraProbe.lean")], None),
            ([f"--root={wt / 'lean'}", "-o", str(work / "Research/Base.olean"),
              str(wt / "lean/Research/Base.lean")], None),
            ([f"--root={wt / 'lean'}", "-o", str(work / "Research/Top.olean"),
              str(wt / "lean/Research/Top.lean")], None),
            (["--run", str(r["tools"] / "ExtractDeps.lean"), str(work / "raw.json"), *modules,
              "--", "Elastica", *modules], None),
        ]
        work_first = f"{work}:{r['lake_lib']}"
        self.assertEqual([c["argv"] for c in r["calls"]], [e[0] for e in expected])
        for call, (_, lean_path) in zip(r["calls"], expected):
            self.assertEqual(call["lean_path"], lean_path or work_first)
            self.assertEqual(call["cwd"], str(wt / "lean"))

    def test_plain_paths(self):
        self.check(self.kernel_run("plain", "_"))

    def test_paths_with_spaces_and_shell_metacharacters(self):
        r = self.kernel_run("with spaces $HOME 'q' ;x", " ")
        self.check(r)
        self.assertTrue((r["work"] / "Research/Top.olean").is_file())


if __name__ == "__main__":
    unittest.main()
