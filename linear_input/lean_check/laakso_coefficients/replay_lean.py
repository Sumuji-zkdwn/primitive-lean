"""Replay the standalone proof against PR #154 or its Lean 4.36 port."""

import argparse
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile


AUDIT = {"block_correction", "decomposition", "scale_identity", "even_eq_iff",
         "even_least", "odd_least", "odd_origin_minimal_iff", "odd_eq_iff",
         "odd_positive_bound", "weak_rational_witness"}
PR_INPUTS = {
    "Design.lean": "e8ce22c9c6fadd68aeb9b33a9f7cf828ab58e9b5e8fc5f1b4494f5763f0cf549",
    "LaaksoFiniteGraph.inc": "14b6a3bf2af0396d4a68aa2456bc63bac2f84c242da8c2bf3c717df30249d143",
    "LaaksoSignedConnection.inc": "c117e42c6a26129259aba01d79d3c3ebc2b0811f08bf133a4c03cd1e99211459",
    "LaaksoSignedEnergy.inc": "c3714d5eddb67214a8f2c76dae3cad78a592f9aa2a88ba15cb43215a828b82e9",
    "LaaksoSignedGauge.inc": "1d6763e9444cf0eaffbff85319d4d892cf9babf442121f9d933cf87ad103c9bc",
    "LaaksoSignedMinimum.inc": "bbada2054a93e3634d6626dd510642b5333fcaaf07f213b8555fe9b4b4eae82a",
}
PROFILES = {
    "4.30.0-rc2": (
        "099b77ae5b9bad7bdcafe70a70cf31f6fb8c98b9",
        "5450b53e5ddc75d46418fabb605edbf36bd0beb6",
        "Mathlib.Data.Setoid.Basic",
        PR_INPUTS,
    ),
    "4.36.0-rc2": (
        "8ed4c9347609ff350f947da7e44101abcd993ed9",
        "2ddf59c8f14245864e6c0ed227a2dab76b9efea2",
        "Mathlib.Order.Setoid.Basic",
        {
            **PR_INPUTS,
            "Design.lean": "d8b91da37eed29f562ef1e6ce35eaf5cc2e841c1639da94ffa5b6fddd9538a45",
            "LaaksoFiniteGraph.inc": "a50c9225099c788d2df76b7b325b866a61a4f20613e0366b8883cd3800a0457c",
            "LaaksoSignedConnection.inc": "87a4ea5c2093c2ff785addbe011ff973284ff11945a8ec328a724ba596fcaefa",
            "LaaksoSignedEnergy.inc": "ae07897b3238f9028c269da496753b441dc6f713784f7c83243453f5d4df9140",
        },
    ),
}
IMPORTS = """Mathlib.Tactic.FinCases Mathlib.Tactic.NormNum Mathlib.Tactic.Tauto
Mathlib.Logic.Relation Mathlib.Data.Fintype.Card Mathlib.Data.Fintype.Prod
Mathlib.Data.Fintype.Sum Mathlib.SetTheory.Cardinal.Finite Mathlib.Data.Fin.VecNotation
Mathlib.Algebra.BigOperators.Fin""".split()


def pinned_wrapper(repo, inputs, setoid_module):
    imports = [f"import {module}" for module in [*IMPORTS, setoid_module]]
    bodies = []
    for filename, digest in inputs.items():
        data = (repo / "linear_input" / "lean_check" / filename).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError(f"Incorrect pinned content: {filename}")
        lines = data.decode().splitlines()
        if filename == "Design.lean":
            imports.extend(line for line in lines if line.startswith("import "))
            lines = [line for line in lines if not line.startswith("import ")]
            lines.append("end")  # close its file-scoped noncomputable section
        bodies.append("\n".join(lines))
    return "\n".join(imports + ["set_option maxHeartbeats 2000000"] + bodies) + "\n"


def run(repo, mathlib, work):
    toolchain = (repo / "lean/lean-toolchain").read_text().strip()
    lean_version = toolchain.removeprefix("leanprover/lean4:v")
    if lean_version not in PROFILES:
        raise ValueError(f"No pinned source profile for {toolchain}")
    head, mathlib_pin, setoid_module, inputs = PROFILES[lean_version]
    env = dict(os.environ, ELAN_TOOLCHAIN=toolchain)
    version = subprocess.check_output(["lean", "--version"], env=env, text=True).strip()
    if f"version {lean_version}," not in version:
        raise ValueError(f"Expected {toolchain}, found {version}")
    print(version)
    if subprocess.check_output(["git", "-C", mathlib, "rev-parse", "HEAD"], text=True).strip() != mathlib_pin:
        raise ValueError("Wrong mathlib commit")
    (work / "PinnedLaakso.lean").write_text(pinned_wrapper(repo, inputs, setoid_module), encoding="utf-8")
    print(f"Verified {len(inputs)} pinned files from {head}; mathlib {mathlib_pin}.")
    module = Path(__file__).with_name("CoefficientBounds.lean")
    (work / module.name).write_bytes(module.read_bytes())
    project = mathlib
    if mathlib.parent.name == "packages" and mathlib.parent.parent.name == ".lake":
        project = mathlib.parent.parent.parent
    lake_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=project, env=env, text=True).strip()
    env["LEAN_PATH"] = os.pathsep.join([str(work), lake_path])
    for source in ("PinnedLaakso", "CoefficientBounds"):
        cmd = ["lean", "--trust=0", "-o", f"{source}.olean", f"{source}.lean"]
        result = subprocess.run(cmd, cwd=work, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        print(result.stdout, end="")
        result.check_returncode()
        if "warning:" in result.stdout or "sorryAx" in result.stdout:
            raise RuntimeError(f"Unexpected diagnostic in {source}")
        if source == "CoefficientBounds":
            records = re.findall(r"'LaaksoCoefficientBounds\.(\w+)' depends on axioms: \[([^\]]*)\]", result.stdout)
            if {name for name, _ in records} != AUDIT:
                raise RuntimeError("Incomplete axiom output")
            for name, axioms in records:
                if set(axioms.split(", ")) - {"propext", "Classical.choice", "Quot.sound"}:
                    raise RuntimeError(f"Unexpected axiom in {name}")
        print(f"PASS {source}.lean (--trust=0)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("mathlib", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as directory:
        run(args.repo.resolve(), args.mathlib.resolve(), Path(directory))
