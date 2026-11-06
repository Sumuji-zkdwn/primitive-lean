"""Trust-zero check and axiom audit for the independent finite Markov model."""
from pathlib import Path
import json
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean/Research/FiniteMarkovTransport.lean"
OUT = ROOT / "verification"
THEOREMS = (
    "historyKernel_is_probability_kernel",
    "same_readout_after_different_operations",
    "controlledKernel_is_probability_kernel",
    "best_pair_reaches_target",
    "every_target_pair_has_minimum_action",
    "finite_minimum_action_values",
    "finite_markov_action_matches_curvature_gramian",
    "finite_markov_action_is_half_existing_required_action",
    "canonical_plan_is_target_coupling",
    "every_target_coupling_has_cost",
    "best_pair_induces_target_coupling",
    "finite_transport_cost_same_across_histories",
    "finite_action_history_gap_and_ot_equality",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    source = SOURCE.read_text(encoding="utf-8")
    for theorem in THEOREMS:
        if f"#print axioms Elastica.FiniteMarkov.{theorem}" not in source:
            raise RuntimeError(f"Missing axiom audit directive: {theorem}")

    lean_root = ROOT / "lean"
    (lean_root / ".lake/build/lib/lean/Research").mkdir(parents=True, exist_ok=True)
    dependency_command = [
        "lake", "env", "lean", "--trust=0", "-o",
        ".lake/build/lib/lean/Research/OkanoharaTransport.olean",
        "Research/OkanoharaTransport.lean",
    ]
    command = ["lake", "env", "lean", "--trust=0", "Research/FiniteMarkovTransport.lean"]
    dependency = subprocess.run(
        dependency_command, cwd=lean_root, capture_output=True, text=True
    )
    process = (
        subprocess.run(command, cwd=lean_root, capture_output=True, text=True)
        if dependency.returncode == 0
        else None
    )
    log = dependency.stdout + dependency.stderr
    if process is not None:
        log += process.stdout + process.stderr
    OUT.mkdir(exist_ok=True)
    (OUT / "finite-markov-transport.log").write_text(log, encoding="utf-8")

    audited: dict[str, list[str]] = {}
    issues: list[str] = []
    for theorem in THEOREMS:
        name = "Elastica.FiniteMarkov." + theorem
        if f"'{name}' does not depend on any axioms" in log:
            audited[name] = []
            continue
        match = re.search(
            r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log, re.S
        )
        if not match:
            issues.append(f"Missing axiom output for {name}")
            continue
        used = [item.strip() for item in match.group(1).split(",") if item.strip()]
        audited[name] = used
        issues.extend(f"Unexpected axiom {name}: {axiom}" for axiom in used if axiom not in ALLOWED_AXIOMS)

    issues.extend(
        line for line in log.splitlines()
        if any(marker in line for marker in ("warning:", "warning(", "error:", "error("))
    )
    result = {
        "passed": dependency.returncode == 0 and process is not None and process.returncode == 0 and not issues,
        "commands": [dependency_command, command],
        "exit_code": dependency.returncode if process is None else process.returncode,
        "checked_theorems": len(audited),
        "axioms": audited,
        "issues": issues,
        "log": "verification/finite-markov-transport.log",
        "scope": (
            "Finite rational two-state controlled Markov kernel and two-step action grid; "
            "not an empirical constitutive law, general Wasserstein theorem, or general learning theorem"
        ),
    }
    (OUT / "finite-markov-transport.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
