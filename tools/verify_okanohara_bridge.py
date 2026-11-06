"""Trust-zero Lean check and explicit axiom audit for an isolated Okanohara extension.

The retained Elastica proof sources and their root import surface are immutable.
This sidecar imports their compiled modules without changing that baseline.
"""
from pathlib import Path
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "lean/Research/OkanoharaTransport.lean"
OUT = ROOT / "verification"
OUT.mkdir(exist_ok=True)
NAMES = (
    "two_step_speed_limit",
    "balanced_path_attains_bound",
    "required_action_exact",
    "history_unit_cost_mono",
    "same_observation_different_cost",
    "adaptation_cost_not_observation_factor",
    "energy_le_history_augmented",
    "history_augmented_energy_mono",
    "history_weight_le_original",
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def main():
    source = SRC.read_text(encoding="utf-8")
    # The explicit #print directives must remain in the trusted source.
    for name in NAMES:
        if f"#print axioms Elastica.{name}" not in source:
            raise RuntimeError(f"Missing axiom check: {name}")
    cmd = ["lake", "env", "lean", "--trust=0", "Research/OkanoharaTransport.lean"]
    p = subprocess.run(cmd, cwd=ROOT / "lean", capture_output=True, text=True)
    log = p.stdout + p.stderr
    (OUT / "okanohara-bridge.log").write_text(log, encoding="utf-8")
    axioms = {}
    issues = []
    for name in NAMES:
        key = "Elastica." + name
        if f"'{key}' does not depend on any axioms" in log:
            axioms[key] = []
            continue
        pattern = re.compile(r"'" + re.escape(key) + r"' depends on axioms: \[([^\]]*)\]", re.S)
        m = pattern.search(log)
        if not m:
            issues.append(f"Missing axiom output for {key}")
            continue
        used = [x.strip() for x in m.group(1).split(",") if x.strip()]
        axioms[key] = used
        for ax in used:
            if ax not in ALLOWED:
                issues.append(f"Forbidden axiom {key}: {ax}")
    issues.extend(x for x in log.splitlines() if "warning:" in x or "error:" in x)
    result = {
        "passed": p.returncode == 0 and not issues,
        "command": cmd,
        "exit_code": p.returncode,
        "checked_theorems": len(axioms),
        "axioms": axioms,
        "issues": issues,
        "log": "verification/okanohara-bridge.log",
        "scope": "Finite scalar speed-limit and history-cost Elastica interface; not general Wasserstein ESL",
    }
    (OUT / "okanohara-bridge.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if result["passed"] else 1

if __name__ == "__main__":
    sys.exit(main())
