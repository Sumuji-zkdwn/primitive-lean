"""Replay the circular-arc proofs from the current checkout in a temporary directory."""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FRAGMENTS = ROOT / "linear_input" / "lean_check"
PARTS = (
    "CurveWordAlgebra", "CurveWordFinite", "CurveWordArc", "RobotWalkArc",
    "RobotCyclotomic", "RobotWalkSupport", "RobotWalkLengths", "RobotWalkClassification",
)
IMPORTS = (
    "Elastica.Geometry", "Elastica.Variation", "Mathlib.Tactic",
    "Mathlib.Analysis.SpecialFunctions.Integrals.Basic",
    "Mathlib.Algebra.Polynomial.OfFn", "Mathlib.RingTheory.Polynomial.Cyclotomic.Roots",
    "Mathlib.RingTheory.RootsOfUnity.Complex",
)
PROOF_MODULES = {
    "RobotSix": ("RobotPR159", "Mathlib.RingTheory.Polynomial.Cyclotomic.Expand"),
    "RobotFacingOdd": ("RobotSix", "Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed", "Mathlib.Algebra.CharP.Two"),
    "RobotFacingOrders": ("RobotFacingOdd", "Mathlib.Data.Nat.Factorization.Basic", "Mathlib.Algebra.Field.GeomSum"),
}


def output(args, cwd):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def assemble(imports, names):
    header = "".join(f"import {module}\n" for module in imports).encode()
    return b"\n".join([header, *((FRAGMENTS / f"{name}.inc").read_bytes() for name in names)])


def verify(build):
    lake_dir = ROOT / "lean"
    revision = output(["git", "rev-parse", "HEAD"], ROOT)
    print(f"primitive-lean {revision}", flush=True)
    print(output(["lake", "env", "lean", "--version"], lake_dir), flush=True)
    subprocess.run(["lake", "build", "Elastica.Geometry", "Elastica.Variation"],
                   cwd=lake_dir, check=True)
    prefix = Path(output(["lake", "env", "lean", "--print-prefix"], lake_dir))
    lean = shutil.which("lean", path=str(prefix / "bin"))
    if lean is None:
        raise SystemExit(f"Lean executable missing under {prefix}.")
    lake_path = output(["lake", "env", sys.executable, "-c",
                        "import os; print(os.environ['LEAN_PATH'])"], lake_dir)
    env = {**os.environ, "LEAN_PATH": os.pathsep.join([str(build), lake_path]),
           "PATH": os.pathsep.join([str(prefix / "bin"), os.environ["PATH"]])}
    (build / "RobotPR159.lean").write_bytes(assemble(IMPORTS, PARTS))
    for module, imports in PROOF_MODULES.items():
        (build / f"{module}.lean").write_bytes(assemble(imports, (module,)))
    for module in ("RobotPR159", *PROOF_MODULES):
        print(f"lean --trust=0 -DwarningAsError=true {module}.lean -o {module}.olean", flush=True)
        subprocess.run([lean, "--trust=0", "-DwarningAsError=true", f"{module}.lean", "-o", f"{module}.olean"],
                       cwd=build, env=env, check=True)

    public_proofs = [
        f"{module}.{line.split()[1]}"
        for module in PROOF_MODULES
        for line in (build / f"{module}.lean").read_text(encoding="utf-8").splitlines()
        if line.startswith("theorem ")
    ]
    audit = "import RobotFacingOrders\n" + "".join(f"#print axioms {n}\n" for n in public_proofs)
    (build / "Audit.lean").write_text(audit, encoding="utf-8")
    audit_run = subprocess.run([lean, "--trust=0", "Audit.lean"], cwd=build, env=env,
                               check=True, text=True, stdout=subprocess.PIPE)
    print(audit_run.stdout, end="", flush=True)
    permitted = {"propext", "Classical.choice", "Quot.sound"}
    for name in public_proofs:
        marker = f"'{name}'"
        entries = [line for line in audit_run.stdout.splitlines() if line.startswith(marker)]
        if len(entries) != 1:
            raise SystemExit(f"Missing or duplicate audit entry for {name}")
        line = entries[0]
        if line == f"{marker} does not depend on any axioms":
            continue
        prefix_text = f"{marker} depends on axioms: ["
        if not line.startswith(prefix_text) or not line.endswith("]"):
            raise SystemExit(f"Unrecognized audit line: {line}")
        axioms = set(line[len(prefix_text):-1].split(", "))
        if axioms - permitted:
            raise SystemExit(f"Unexpected axioms in {name}: {axioms - permitted}")
    checker = shutil.which("leanchecker", path=str(prefix / "bin"))
    if checker is None:
        raise SystemExit(f"leanchecker missing under {prefix}.")
    for module in PROOF_MODULES:
        subprocess.run([checker, "-v", module], cwd=build, env=env, check=True)
    print(f"PASS: four modules, kernel replay of the three new modules, "
          f"axiom audit of {len(public_proofs)} public theorems.")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="lean-robot-facing-") as directory:
        verify(Path(directory).resolve())
