"""Isolated additive optical verification, called by tools/verify.py.

Checks the PR #92 dependency bytes, compiles with the repository-pinned Lean
and Mathlib, audits every added theorem, and runs the independent experiment.
This does not claim that the stacked PRs have been integrated into main.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time

BASE_COMMIT = "b293710217765e12992de522a866d0fafef4d95a"
PRESERVED = {
    "lean/DarkBrightObservation.lean": "cc4eed983b9027c26c3ac2f789b26ed619043befa983c3eef3d15c4a026ad016",
    "lean/PrismHysteresisReadout.lean": "8425a731133460caebf7b93e91a4fc398fc9398d13f160b265c3c17bc7153423",
    "lean/FluidPrismPhaseMemory.lean": "708a98bd54831aa3571a61d5f51045ad9ba04ab03413d3b6ad7deb44c7037e5c",
    "lean/lean-toolchain": "ce4c4e3d87434b9663f46de25ce34b48a0cf0d392e0a320a0787b4674a2d7b61",
    "lean/lakefile.toml": "24cbaef7acf55e1276267d5383d3107b695d5caa5ab0f12abd535c594c86eabe",
    "lean/lake-manifest.json": "5781fd49aff59347f594d12cbfa61129eebb10ef293729ead611bd7410740590",
}
ANCESTORS = ["DarkBrightObservation", "PrismHysteresisReadout", "FluidPrismPhaseMemory"]
ADDITIONS = ["TwoWavelengthPhase", "TwoWavelengthSeparation", "TwoWavelengthRecovery"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run_two_wavelength(root, rebuild=False):
    from verify import strip_comments_strings
    root = Path(root)
    lean = root / "lean"
    out = root / "verification" / "two-wavelength"
    out.mkdir(parents=True, exist_ok=True)
    report = {"scope": "isolated additive extension of PR #92", "base_commit": BASE_COMMIT,
              "timestamp_utc": datetime.now(timezone.utc).isoformat(), "passed": False,
              "commands": [], "source_sha256": {}, "theorems": [], "axioms": {}}

    def digest(p):
        return hashlib.sha256(p.read_bytes()).hexdigest()

    def save():
        (out / "verification.json").write_text(json.dumps(report, indent=2) + "\n")

    def command(argv, name, cwd=lean):
        start = time.monotonic()
        result = subprocess.run(argv, cwd=cwd, text=True, capture_output=True)
        text = result.stdout + result.stderr
        (out / (name + ".log")).write_text(text)
        entry = {"argv": argv, "exit_code": result.returncode,
                 "seconds": round(time.monotonic() - start, 3),
                 "log": str((out / (name + ".log")).relative_to(root))}
        report["commands"].append(entry)
        save()
        if result.returncode or re.search(r"\b(?:error|warning):", text):
            raise RuntimeError(f"{name} failed or emitted a warning:\n{text}")
        return text

    try:
        report["preserved_pr92_sources"] = {
            p: digest(root / p) == expected for p, expected in PRESERVED.items()}
        if not all(report["preserved_pr92_sources"].values()):
            raise RuntimeError("A preserved PR #92 source or dependency pin changed")
        additions = ADDITIONS
        if not all((lean / (m + ".lean")).is_file() for m in additions):
            raise RuntimeError("Missing two-wavelength module")
        report["modules"] = ANCESTORS + additions
        for module in additions:
            source = strip_comments_strings((lean / (module + ".lean")).read_text())
            if re.search(r"\b(sorry|admit|axiom|unsafe)\b", source):
                raise RuntimeError(f"Forbidden declaration or unproved term in {module}")
            names = re.findall(r"^theorem\s+(\w+)", source, re.M)
            if not names:
                raise RuntimeError(f"No audited theorems found in {module}")
            report["theorems"].extend(module + "." + n for n in names)
        build = lean / ".lake" / "build" / "lib" / "lean"
        build.mkdir(parents=True, exist_ok=True)
        if rebuild:
            for module in report["modules"]:
                for suffix in (".olean", ".ilean", ".olean.private", ".olean.server"):
                    (build / (module + suffix)).unlink(missing_ok=True)
        lake = shutil.which("lake")
        if lake is None:
            raise RuntimeError("lake is not available in PATH")
        report["lean_version"] = command([lake, "env", "lean", "--version"], "version").strip()
        for module in report["modules"]:
            command([lake, "env", "lean", "--trust=0", "-o",
                     str(build / (module + ".olean")), module + ".lean"], module)
        audit = lean / "TwoWavelengthAudit.lean"
        audit.write_text("\n".join("import " + m for m in additions) + "\n" +
                         "\n".join("#print axioms " + n for n in report["theorems"]) + "\n")
        audit_text = command([lake, "env", "lean", "--trust=0", audit.name], "axioms")
        rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_text)
        no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", audit_text)
        report["axioms"] = {name: [a.strip() for a in used.split(",") if a.strip()]
                            for name, used in rows}
        report["axioms"].update({name: [] for name in no_axioms})
        if set(report["axioms"]) != set(report["theorems"]):
            raise RuntimeError("Axiom audit does not cover exactly the added theorem names")
        for name, used in report["axioms"].items():
            if not set(used) <= ALLOWED:
                raise RuntimeError(f"Unexpected axioms for {name}: {used}")
        command([sys.executable, "-B", "tools/check_fluid_prism_phase.py"], "parent-python", root)
        command([sys.executable, "-B", "tools/check_two_wavelength_phase.py", "--output",
                 str(out / "experiments.json")], "independent-python", root)
        paths = list(PRESERVED) + ["lean/" + m + ".lean" for m in additions] + [
            "tools/check_two_wavelength_phase.py", "tools/verify_two_wavelength.py", "tools/verify.py"]
        report["source_sha256"] = {p: digest(root / p) for p in paths}
        report["theorem_count"] = len(report["theorems"])
        report["passed"] = True
    except Exception as error:
        report["error"] = str(error)
    save()
    return report
