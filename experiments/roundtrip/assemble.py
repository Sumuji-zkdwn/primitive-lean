"""Assemble the initial 465-theorem / 509-declaration baseline with round-trip drafts.

Only the 24 Elastica modules (imported as the built library) and the 36 original
linear-input drafts are used.  None of the later supplements (MainResult.inc and
everything registered after it) is included, so every round-trip theorem depends
only on the initial baseline and Mathlib.
"""
import hashlib, json, pathlib, re, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PROOFS = ROOT / "linear_input" / "lean_check"
PARTS = ("Design.lean", "Observation.lean", "Calculus.lean", "Consequences.inc",
         "Coercivity.inc", "Gradient.inc", "Dissipation.lean", "RegularBand.inc",
         "Invariance.inc", "CurvatureBridge.inc", "VariationalBridge.inc", "Feedback.inc",
         "Constraints.inc", "AreaVariation.inc", "PressureCurvature.inc", "PressureStationary.inc",
         "AreaRegularity.inc", "AreaParameters.inc", "AreaFamily.inc",
         "AreaExactVariation.inc", "AreaMinimum.inc", "StrictEnergy.inc",
         "GradientBound.inc", "InternalUpdate.inc", "TrajectoryExistence.inc",
         "FiniteBand.inc", "CompactLocalExistence.inc", "GlobalContinuation.inc",
         "GlobalTrajectory.inc", "ForwardUniqueness.inc", "GlobalConsequences.inc",
         "LevelGeometry.inc", "FiniteInternalUpdate.inc", "CoupledTrajectory.inc",
         "LevelConvergence.inc", "CoupledConsequences.inc")
# Kaggle record of the fixed baseline sources (2026-10-25, 494/538 run).
RECORD = ROOT / "evidence/kaggle/20261025T123036-471322/main-result.json"
ROUNDS = sorted(HERE.glob("R[0-9][0-9]_*.inc"))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    recorded = json.loads(RECORD.read_text(encoding="utf-8"))["source_hashes"]
    mismatched = []
    for path in sorted((ROOT / "lean/Elastica").glob("*.lean")):
        key = path.relative_to(ROOT).as_posix()
        if recorded.get(key) != sha(path):
            mismatched.append(key)
    for name in PARTS:
        key = "linear_input/lean_check/" + name
        if recorded.get(key) != sha(PROOFS / name):
            mismatched.append(key)
    if mismatched:
        sys.exit("baseline source changed: " + ", ".join(mismatched))
    # Re-identify the initial baseline: 465 theorems and 509 declarations.
    pattern = re.compile(r"(?m)^(?:@\[[^\n]*\]\s*)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)")
    kinds = []
    for path in sorted((ROOT / "lean/Elastica").glob("*.lean")) + [PROOFS / n for n in PARTS]:
        code = re.sub(r"/-.*?-/", "", path.read_text(encoding="utf-8"), flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        kinds += [m.group(1) for m in pattern.finditer(code)]
    counts = (sum(k == "theorem" for k in kinds), len(kinds))
    if counts != (465, 509):
        sys.exit(f"baseline count mismatch: {counts}")
    imports, bodies = ["import Elastica"], []
    for path in [PROOFS / n for n in PARTS] + ROUNDS:
        lines = []
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith("import "):
                if line not in imports:
                    imports.append(line)
            else:
                lines.append(line)
        bodies.append("-- Source: " + path.name + "\n" + "\n".join(lines))
    decls = []
    for path in ROUNDS:
        code = path.read_text(encoding="utf-8")
        ns = re.findall(r"(?m)^namespace\s+(\w+)", code)
        assert len(ns) == 1, (path.name, ns)
        for m in re.finditer(r"(?m)^(theorem|lemma|def|abbrev)\s+(\w+)", code):
            decls.append(dict(name=ns[0] + "." + m.group(2), kind=m.group(1), file=path.name))
        for m in re.finditer(r"\b(sorry|admit|axiom|native_decide)\b", code):
            sys.exit(f"forbidden token {m.group()} in {path.name}")
    source = "\n".join(imports) + "\n\n" + "\n\n".join(bodies) + "\n\n"
    source += "\n".join("#print axioms " + d["name"] for d in decls) + "\n"
    out = HERE / "Joint.lean"
    out.write_text(source, encoding="utf-8")
    (HERE / "declarations.json").write_text(
        json.dumps(decls, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    print(f"baseline hashes ok, {counts[0]} theorems / {counts[1]} declarations; {len(ROUNDS)} round files, {len(decls)} new declarations "
          f"({sum(d['kind'] == 'theorem' for d in decls)} theorems)")
    if "--compile" in sys.argv:
        r = subprocess.run(["lake", "env", "lean", "--trust=0", str(out)], cwd=ROOT / "lean",
                           capture_output=True, text=True)
        log = r.stdout + r.stderr
        (HERE / "build.log").write_text(log, encoding="utf-8")
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        bad = [l for l in log.splitlines() if "error" in l or "warning" in l]
        axioms = re.findall(r"depends on axioms: \[([^\]]*)\]", log)
        extra = sorted({a.strip() for grp in axioms for a in grp.split(",")} - allowed)
        print("exit", r.returncode, "errors/warnings", len(bad), "axiom reports", len(axioms),
              "unexpected axioms", extra)
        version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT / "lean",
                                 capture_output=True, text=True).stdout.strip()
        manifest = json.loads((ROOT / "lean/lake-manifest.json").read_text(encoding="utf-8"))
        result = dict(
            passed=r.returncode == 0 and not bad and not extra and len(axioms) == len(decls),
            lean=version,
            mathlib=next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"),
            command="python3 -B experiments/roundtrip/assemble.py --compile",
            baseline=dict(theorems=counts[0], declarations=counts[1],
                          elastica_modules=24, linear_input_parts=len(PARTS),
                          hash_record=RECORD.relative_to(ROOT).as_posix()),
            rounds=[p.name for p in ROUNDS],
            new_declarations=len(decls),
            new_theorems=sum(d["kind"] == "theorem" for d in decls),
            errors_or_warnings=len(bad), axiom_reports=len(axioms),
            allowed_axioms=sorted(allowed), unexpected_axioms=extra,
            joint_sha256=sha(out),
            round_sha256={p.name: sha(p) for p in ROUNDS},
        )
        (HERE / "verification.json").write_text(
            json.dumps(result, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
        if bad:
            print("\n".join(log.splitlines()[:60]))
        sys.exit(r.returncode or bool(bad) or bool(extra))


main()
