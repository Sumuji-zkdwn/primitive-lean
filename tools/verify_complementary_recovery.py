"""Independently compile generic recovery, then inspect its F16 integration.

--standalone imports only mathlib and the general/examples supplements.
--integration requires a fresh passing tools/verify.py --proof-only result.
Both modes check the original PR #23 sources against pinned Git blob hashes.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import importlib.util
import json
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
GROUPS = (
    ("linear_input/lean_check/ComplementaryPencilRecovery.inc", "LinearInputComplementaryPencilRecovery"),
    ("linear_input/lean_check/F16ConstructiveRecovery.inc", "LinearInputF16ConstructiveRecovery"),
    ("linear_input/lean_check/ComplementaryObservationExamples.inc", "LinearInputComplementaryObservationExamples"),
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def preserved():
    manifest = json.loads((ROOT / "tools/complementary_recovery_baseline.json").read_text())
    changed = []
    for relative, expected in manifest["git_blob_sha1"].items():
        path = ROOT / relative
        if not path.is_file():
            changed.append(relative + ": missing")
            continue
        content = path.read_bytes()
        blob = b"blob " + str(len(content)).encode() + b"\0" + content
        if hashlib.sha1(blob).hexdigest() != expected:
            changed.append(relative)
    return dict(base_commit=manifest["base_commit"], base_run=manifest["base_run"],
                file_count=len(manifest["git_blob_sha1"]), changed=changed, passed=not changed)


def source_declarations(groups):
    spec = importlib.util.spec_from_file_location("recovery_common", ROOT / "tools/verify.py")
    common = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(common)
    result = []
    for relative, namespace in groups:
        source = (ROOT / relative).read_bytes()
        code = common.strip_comments_strings(source.decode("utf-8"))
        if re.findall(r"(?m)^namespace\s+([^\s]+)", code) != [namespace]:
            raise ValueError("Unexpected namespaces in " + relative)
        if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code):
            raise ValueError("Forbidden proof token in " + relative)
        for found in re.finditer(
            r"(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)", code
        ):
            result.append(dict(name=namespace + "." + found.group(2), kind=found.group(1), file=relative))
    if not result or len({d["name"] for d in result}) != len(result):
        raise ValueError("Missing or duplicate recovery declarations")
    return result


def standalone(report):
    groups = (GROUPS[0], GROUPS[2])
    declarations = source_declarations(groups)
    header = "\n".join([
        "import Mathlib.LinearAlgebra.Matrix.NonsingularInverse",
        "import Mathlib.Data.Real.Basic", "import Mathlib.Data.ZMod.Basic", "import Mathlib.Tactic",
    ]) + "\n\n"
    source = header.encode() + b"\n".join((ROOT / p).read_bytes() for p, _ in groups)
    source += ("\n\n" + "\n".join("#print axioms " + d["name"] for d in declarations) + "\n").encode()
    assembly = OUT / "ComplementaryRecoveryStandalone.lean"
    assembly.write_bytes(source)
    hashes = {p: digest(ROOT / p) for p, _ in groups}
    started = time.monotonic()
    command = ["lake", "env", "lean", "--trust=0", "../verification/ComplementaryRecoveryStandalone.lean"]
    proc = subprocess.run(command, cwd=ROOT / "lean", capture_output=True, text=True, encoding="utf-8")
    log = proc.stdout + proc.stderr
    (OUT / "complementary-recovery-standalone.log").write_text(log, encoding="utf-8")
    report.update(command=command, exit_code=proc.returncode, seconds=round(time.monotonic() - started, 3),
                  declarations=declarations, source_sha256=hashes, axioms={},
                  theorem_count=sum(d["kind"] in ("theorem", "lemma") for d in declarations),
                  declaration_count=len(declarations), log="verification/complementary-recovery-standalone.log")
    if proc.returncode:
        print(log)
        report["errors"].append("Standalone Lean compilation failed")
    report["warnings"] = [line for line in log.splitlines() if re.search(r"\bwarning:", line)]
    if report["warnings"]:
        report["errors"].append("Standalone Lean compilation emitted warnings")
    for d in declarations:
        name = d["name"]
        matches = re.findall("'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", log, re.S)
        empty = log.count("'" + name + "' does not depend on any axioms")
        if len(matches) + empty != 1:
            report["errors"].append("Incomplete axiom audit: " + name)
            continue
        axioms = [a.strip() for a in matches[0].split(",") if a.strip()] if matches else []
        report["axioms"][name] = axioms
        if not set(axioms) <= ALLOWED:
            report["errors"].append("Unexpected axiom: " + name)
    if any(digest(ROOT / p) != h for p, h in hashes.items()):
        report["errors"].append("Sources changed during standalone verification")


def integration(report):
    proof = json.loads((OUT / "proof-only.json").read_text())
    joint = json.loads((OUT / "main-result.json").read_text())
    if not proof["passed"] or not joint["passed"] or not joint["joint_axiom_audit"]:
        raise ValueError("The full proof-only integration is not passing")
    # Require the joint report to match every source hash, not only new modules.
    for relative, expected in joint["source_hashes"].items():
        if digest(ROOT / relative) != expected:
            raise ValueError("Stale integrated source: " + relative)
    declarations = source_declarations(GROUPS)
    groups = [g for g in joint["supplemental_groups"] if g["source"] in {p for p, _ in GROUPS}]
    if len(groups) != len(GROUPS):
        raise ValueError("Not all recovery modules were independently counted")
    audited = {d["name"]: joint["axioms"][d["name"]] for d in declarations}
    if any(not set(axioms) <= ALLOWED for axioms in audited.values()):
        raise ValueError("Unexpected axiom in integrated recovery")
    report.update(total_theorem_count=joint["total_theorem_count"],
                  total_declaration_count=joint["total_declaration_count"],
                  added_theorem_count=sum(g["theorem_count"] for g in groups),
                  added_declaration_count=sum(g["declaration_count"] for g in groups),
                  groups=groups, axioms=audited,
                  source_sha256={p: digest(ROOT / p) for p, _ in GROUPS},
                  evidence="verification/main-result.json")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--standalone", action="store_true")
    modes.add_argument("--integration", action="store_true")
    args = parser.parse_args()
    mode = "standalone" if args.standalone else "integration"
    OUT.mkdir(exist_ok=True)
    report = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(), mode=mode,
                  passed=False, errors=[], preservation=preserved())
    try:
        if not report["preservation"]["passed"]:
            raise ValueError("Original PR #23 files changed")
        (standalone if args.standalone else integration)(report)
        report["passed"] = not report["errors"]
    except (OSError, ValueError, KeyError, TypeError) as error:
        report["errors"].append(str(error))
    (OUT / ("complementary-recovery-" + mode + ".json")).write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in {"axioms", "declarations", "groups"}}, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
