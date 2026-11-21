#!/usr/bin/env python3
"""Verify the planar discrepancy and projective-lock models from this checkout.

The complete route runs both independent Python checks, then delegates fresh
trust-zero Lean compilation and all-owned-theorem axiom auditing to the existing
standalone-module checker. Numerical-only success is explicitly not a Lean pass.
Use tools/verify.py --planar-sync-only as the unified entry point.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
from importlib import metadata
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
MODULES = ("PlanarSyncMoments", "ProjectiveLock")
NUMERICAL_CHECKS = (
    ("moments", "tools/planar_sync/check_moments.py", "verification-results.json"),
    ("projective", "tools/planar_sync/check_projective.py", "projective-lock-results.json"),
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def package_version(name: str) -> str | None:
    try:
        return metadata.version(name)
    except metadata.PackageNotFoundError:
        return None


def run(root: Path = ROOT, *, numerical_only: bool = False) -> dict:
    root = Path(root).resolve()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output = root / "verification" / "planar-sync" / stamp
    output.mkdir(parents=True)
    source_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    expected_head = os.environ.get("EXPECTED_HEAD")
    inputs = [
        "tools/verify_planar_sync.py", "tools/verify_toolchain_modules.py",
        "tools/verify.py", "lean/lean-toolchain", "lean/lakefile.toml",
        "lean/lake-manifest.json",
        *(path for _, path, _ in NUMERICAL_CHECKS),
    ]
    if not numerical_only:
        inputs.extend("lean/" + name + ".lean" for name in MODULES)
    missing = [path for path in inputs if not (root / path).is_file()]
    source_hashes = {path: digest(root / path) for path in inputs if path not in missing}
    report = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "source_commit": source_commit,
        "expected_head": expected_head,
        "dirty": bool(subprocess.check_output(
            ["git", "status", "--porcelain"], cwd=root, text=True).strip()),
        "scope": "numerical_only" if numerical_only else "numerical_and_lean",
        "claim": "Constructed mathematical models; no empirical celestial or quantum validation",
        "passed": False,
        "requested_checks_passed": False,
        "status": "running",
        "runtime": {"python": platform.python_version(),
                    "numpy": package_version("numpy"), "scipy": package_version("scipy")},
        "toolchain": (root / "lean/lean-toolchain").read_text().strip(),
        "source_sha256": source_hashes,
        "numerical": {},
        "lean": {"status": "not_run", "passed": False, "modules": list(MODULES)},
        "errors": [],
    }

    def save() -> None:
        write_json(output / "report.json", report)
        pointer = "latest-numerical.json" if numerical_only else "latest.json"
        write_json(output.parent / pointer, {
            "report": (output / "report.json").relative_to(root).as_posix(),
            "scope": report["scope"], "status": report["status"],
            "passed": report["passed"],
            "requested_checks_passed": report["requested_checks_passed"],
        })

    if missing:
        report["errors"].append("Missing verification inputs: " + ", ".join(missing))
    if expected_head and source_commit != expected_head:
        report["errors"].append("Checked-out source does not match EXPECTED_HEAD")
    save()
    if report["errors"]:
        report["status"] = "failed"
        save()
        return report

    for name, script, filename in NUMERICAL_CHECKS:
        check_output = output / name
        check_output.mkdir()
        command = [sys.executable, "-B", "-X", "utf8", str(root / script),
                   "--output-dir", str(check_output)]
        started = time.monotonic()
        completed = subprocess.run(command, cwd=root, capture_output=True,
                                   text=True, encoding="utf-8", errors="replace")
        log = check_output / "run.log"
        log.write_text(completed.stdout + completed.stderr, encoding="utf-8")
        result_path = check_output / filename
        row = {
            "command": command,
            "exit_code": completed.returncode,
            "seconds": round(time.monotonic() - started, 3),
            "log": log.relative_to(root).as_posix(),
            "passed": False,
        }
        if result_path.is_file():
            try:
                result = json.loads(result_path.read_text(encoding="utf-8"))
                row.update(result=result_path.relative_to(root).as_posix(),
                           result_sha256=digest(result_path),
                           result_status=result.get("overall_status"),
                           passed=completed.returncode == 0 and
                                  result.get("overall_status") == "passed")
            except (json.JSONDecodeError, UnicodeError) as exc:
                row["error"] = "Invalid result JSON: " + str(exc)
        else:
            row["error"] = "The current run did not create its expected result file"
        report["numerical"][name] = row
        if not row["passed"]:
            report["errors"].append(name + ": independent Python verification failed")
        print(name + ": " + ("passed" if row["passed"] else "failed"), flush=True)
        save()

    if not numerical_only:
        try:
            from verify_toolchain_modules import run as verify_modules
            kernel = verify_modules(root=root, selected=list(MODULES),
                                    output="planar-sync-kernel")
            report["lean"] = {
                "status": "passed" if kernel["passed"] else "failed",
                "passed": kernel["passed"],
                "modules": list(MODULES),
                "report_pointer": "verification/planar-sync-kernel/latest-partial.json",
                "audited_theorems": kernel.get("audited_theorem_declarations_including_generated", 0),
                "source_commit": kernel["source_commit"],
                "lean_version": kernel.get("lean_version"),
                "manifest_sha256": kernel["manifest_sha256"],
                "errors": kernel["errors"],
            }
            if not kernel["passed"]:
                report["errors"].append("Lean source compilation or theorem axiom audit failed")
        except Exception as exc:
            report["lean"].update(status="failed", error=f"{type(exc).__name__}: {exc}")
            report["errors"].append("Lean verification could not complete")

    changed = [path for path, value in source_hashes.items()
               if not (root / path).is_file() or digest(root / path) != value]
    if changed:
        report["errors"].append("Verification inputs changed during the run: " + ", ".join(changed))
    report["requested_checks_passed"] = not report["errors"]
    report["passed"] = not numerical_only and report["requested_checks_passed"]
    report["status"] = (
        "failed" if report["errors"] else
        "numerical_passed_lean_not_run" if numerical_only else "passed"
    )
    save()
    print(json.dumps({
        "status": report["status"], "passed": report["passed"],
        "requested_checks_passed": report["requested_checks_passed"],
        "scope": report["scope"], "errors": report["errors"],
        "report": str(output / "report.json"),
    }, ensure_ascii=False, indent=2), flush=True)
    return report


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerical-only", action="store_true",
                        help="Run the independent Python checks; does not report a Lean pass")
    args = parser.parse_args(argv)
    report = run(numerical_only=args.numerical_only)
    return 0 if report["requested_checks_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
