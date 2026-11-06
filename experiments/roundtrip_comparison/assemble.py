"""Compile the comparison file on top of the unchanged baseline and rounds R01–R13.

The baseline check and assembly are those of ../roundtrip/assemble.py. In addition, the
SHA-256 of every R*.inc must equal the value recorded in ../roundtrip/verification.json,
so the earlier 13 round trips are used exactly as recorded and are not modified.
"""
import hashlib, json, pathlib, re, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RT = ROOT / "experiments/roundtrip"
spec = (RT / "assemble.py").read_text(encoding="utf-8")
PARTS = eval(re.search(r"PARTS = (\(.*?\))\n", spec, re.S).group(1))
RECORD = ROOT / "evidence/kaggle/20261025T123036-471322/main-result.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    recorded = json.loads(RECORD.read_text(encoding="utf-8"))["source_hashes"]
    proofs = ROOT / "linear_input/lean_check"
    files = sorted((ROOT / "lean/Elastica").glob("*.lean")) + [proofs / n for n in PARTS]
    bad = [p.name for p in files if recorded.get(p.relative_to(ROOT).as_posix()) != sha(p)]
    rounds = sorted(RT.glob("R[0-9][0-9]_*.inc"))
    prior = json.loads((RT / "verification.json").read_text(encoding="utf-8"))["round_sha256"]
    bad += [p.name for p in rounds if prior.get(p.name) != sha(p)]
    if bad or len(rounds) != 13:
        sys.exit("changed sources: " + ", ".join(bad))
    comps = sorted(HERE.glob("C[0-9][0-9]_*.inc"))
    imports, bodies = ["import Elastica"], []
    for path in [proofs / n for n in PARTS] + rounds + comps:
        lines = []
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith("import "):
                if line not in imports:
                    imports.append(line)
            else:
                lines.append(line)
        bodies.append("-- Source: " + path.name + "\n" + "\n".join(lines))
    decls = []
    for path in comps:
        code = path.read_text(encoding="utf-8")
        ns = re.findall(r"(?m)^namespace\s+(\w+)", code)
        assert len(ns) == 1
        decls += [dict(name=ns[0] + "." + m.group(2), kind=m.group(1), file=path.name)
                  for m in re.finditer(r"(?m)^(theorem|lemma|def|abbrev)\s+(\w+)", code)]
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
            sys.exit("forbidden token in " + path.name)
    out = HERE / "Joint.lean"
    out.write_text("\n".join(imports) + "\n\n" + "\n\n".join(bodies) + "\n\n" +
                   "\n".join("#print axioms " + d["name"] for d in decls) + "\n", encoding="utf-8")
    r = subprocess.run(["lake", "env", "lean", "--trust=0", str(out)], cwd=ROOT / "lean",
                       capture_output=True, text=True)
    log = r.stdout + r.stderr
    (HERE / "build.log").write_text(log, encoding="utf-8")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    msgs = [l for l in log.splitlines() if "error" in l or "warning" in l]
    axioms = re.findall(r"depends on axioms: \[([^\]]*)\]", log)
    extra = sorted({a.strip() for g in axioms for a in g.split(",")} - allowed)
    result = dict(passed=r.returncode == 0 and not msgs and not extra and len(axioms) == len(decls),
                  command="python3 -B experiments/roundtrip_comparison/assemble.py",
                  baseline_and_rounds_unchanged=True, rounds_reused=[p.name for p in rounds],
                  comparison_files=[p.name for p in comps], new_declarations=len(decls),
                  new_theorems=sum(d["kind"] == "theorem" for d in decls),
                  errors_or_warnings=len(msgs), axiom_reports=len(axioms), unexpected_axioms=extra,
                  comparison_sha256={p.name: sha(p) for p in comps},
                  gpt_script_sha256=sha(HERE / "gpt/primitive_465_roundtrip_experiment.py"))
    (HERE / "verification.json").write_text(json.dumps(result, indent=1) + "\n", encoding="utf-8")
    (HERE / "declarations.json").write_text(json.dumps(decls, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "comparison_sha256"}, indent=1))
    if msgs:
        print("\n".join(log.splitlines()[:80]))
    sys.exit(0 if result["passed"] else 1)


main()
