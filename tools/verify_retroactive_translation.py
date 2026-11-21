"""Verify the retroactive-translation supplement through tools/verify.py.

Finite model regressions and kernel-checked deterministic lemmas have separate
results. The general adaptive probability theorem remains a handwritten proof.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from verify_toolchain_modules import run as verify_modules

ROOT = Path(__file__).resolve().parents[1]
MODULES = ("Research.RetroactiveTranslation", "Research.RetroactiveWorkBounds")
RESULTS = {
    "stage1/results.json", "stage1/compression_results.json",
    "stage2/parity_probe_results.json", "stage2/repeated_squaring_results.json",
}
OUT = ROOT / "verification" / "retroactive-translation"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run() -> dict:
    OUT.mkdir(parents=True, exist_ok=True)
    # An early input or environment failure must not leave an older success.
    (OUT / "report.json").write_text(json.dumps({
        "passed": False,
        "stage": "initializing",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
    }, indent=2) + "\n", encoding="utf-8")
    sources = [
        ROOT / "lean" / (name.replace(".", "/") + ".lean")
        for name in MODULES
    ] + [
        Path(__file__), ROOT / "tools/check_retroactive_translation.py",
        ROOT / "tools/verify.py", ROOT / "tools/pr_integration.py",
        ROOT / "tools/verify_toolchain_modules.py",
        ROOT / "lean/lean-toolchain", ROOT / "lean/lake-manifest.json",
        ROOT / "lean/lakefile.toml",
        ROOT / ".github/workflows/retroactive-translation.yml",
    ]
    sources += sorted(
        p for p in (ROOT / "experiments/retroactive_translation").rglob("*")
        if p.is_file() and p.suffix in {".py", ".json"}
    )
    hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in sources}
    report = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "source_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "dirty": bool(subprocess.check_output(
            ["git", "status", "--porcelain"], cwd=ROOT, text=True).strip()),
        "source_sha256": hashes,
        "passed": False,
        "scope": "Finite model regression; deterministic Lean lemmas and complete local theorem axiom audit",
        "not_formalized": [
            "The full adaptive probabilistic parity-query optimality theorem",
            "Information-theoretic entropy inequalities",
            "General cryptographic security or sequential-time lower bounds",
        ],
        "errors": [],
    }

    def save() -> None:
        (OUT / "report.json").write_text(
            json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    save()
    finite = subprocess.run(
        [sys.executable, "-B", "tools/check_retroactive_translation.py"],
        cwd=ROOT, text=True, encoding="utf-8", capture_output=True)
    (OUT / "python.log").write_text(finite.stdout + finite.stderr, encoding="utf-8")
    report["finite_exit_code"] = finite.returncode
    report["finite_log"] = "verification/retroactive-translation/python.log"
    if finite.returncode:
        report["errors"].append("Finite regression failed; see python.log")
    else:
        try:
            result = json.loads(finite.stdout)
            checks = result.get("checks", [])
            if (result.get("passed") is not True or result.get("artifact_pairs") != 4
                    or len(checks) != 4 or not all(c.get("matched") is True for c in checks)
                    or {c.get("result") for c in checks} != RESULTS):
                raise ValueError("Expected four successful finite artifact comparisons")
            report["finite_coverage"] = result["coverage"]
        except (ValueError, TypeError, KeyError, AttributeError) as exc:
            report["errors"].append(f"Invalid finite verification result: {exc}")
    if not report["errors"]:
        try:
            lean = verify_modules(
                root=ROOT, selected=list(MODULES), output="retroactive-translation-lean")
            report["lean_passed"] = lean["passed"]
            report["lean_source_theorems"] = lean["explicit_source_theorems"]
            report["lean_audited_theorems"] = len(lean["axioms"])
            report["lean_audit_pointer"] = "verification/retroactive-translation-lean/latest-partial.json"
            report["errors"].extend(lean["errors"])
            if lean["passed"] is not True:
                report["errors"].append("Lean verification did not report success")
            if (set(lean["inventory"]) != set(MODULES)
                    or {row["module"] for row in lean["modules"]} != set(MODULES)
                    or {row["module"] for row in lean["axioms"]} != set(MODULES)
                    or any(row["explicit_theorems"] == 0 for row in lean["inventory"].values())):
                report["errors"].append("The expected two nonempty theorem modules were not audited")
            mathlib = ROOT / "lean/.lake/packages/mathlib"
            revision = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
            manifest = json.loads((ROOT / "lean/lake-manifest.json").read_text("utf-8"))
            expected = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
            report["mathlib_commit"] = revision
            if revision != expected:
                report["errors"].append("Installed mathlib revision disagrees with the manifest")
        except (OSError, ValueError, subprocess.CalledProcessError) as exc:
            report["errors"].append(f"Lean verification did not complete: {exc}")
    changed = [p for p, h in hashes.items() if digest(ROOT / p) != h]
    if changed:
        report["errors"].append("Inputs changed during verification: " + repr(changed))
    report["passed"] = not report["errors"]
    save()
    print(json.dumps({k: v for k, v in report.items() if k != "source_sha256"},
                     ensure_ascii=False, indent=2))
    return report


def main() -> int:
    if not __debug__:
        raise RuntimeError("Run without -O: the finite models require active assertions")
    return 0 if run()["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
