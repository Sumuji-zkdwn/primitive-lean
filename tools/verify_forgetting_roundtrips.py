"""Verify forgetting round trips through the repository's unified entry point.

The finite enumerations are independent checks. Lean compilation, source checks,
and theorem-axiom collection are delegated to the existing standalone verifier.
No neurophysiological, energetic, or fluid constitutive claim is audited here.
"""
from datetime import datetime, timezone
import json
from pathlib import Path
import sys

from verify import command
from verify_toolchain_modules import run as verify_modules


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification" / "forgetting-roundtrips"
MODULES = ["Research.ForgettingRoundTrips"]


def run():
    OUT.mkdir(parents=True, exist_ok=True)
    report = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "scope": (
            "Independent bounded finite checks and fresh trust-zero compilation "
            "with the existing all-local-theorem axiom audit; no empirical "
            "memory, energy-cost, or fluid-model validation"
        ),
        "selected_modules": MODULES,
        "passed": False,
        "stage": "finite_checks",
        "checks": [],
        "python_results": None,
        "lean_results": None,
        "errors": [],
    }

    def save():
        (OUT / "report.json").write_text(
            json.dumps(report, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

    def check(name, args, cwd=ROOT):
        record = command(args, "forgetting-roundtrips/" + name, cwd=cwd)
        report["checks"].append({"name": name, **record})
        if record["exit_code"]:
            report["errors"].append(name + " failed; see " + record["log"])
        save()
        return record

    save()
    try:
        finite = check(
            "finite-python",
            [sys.executable, "-B", "-O", "tools/forgetting_roundtrips.py"],
        )
        check(
            "python-tests",
            [sys.executable, "-B", "-m", "unittest", "discover", "-s", "tests",
             "-p", "test_forgetting_roundtrips.py", "-v"],
        )
        if finite["exit_code"] == 0:
            report["python_results"] = json.loads(
                (ROOT / finite["log"]).read_text(encoding="utf-8")
            )
            if report["python_results"].get("status") != "all checks passed":
                report["errors"].append("Finite checker did not report successful completion")
        if report["errors"]:
            return report

        report["stage"] = "elastica_prerequisite"
        save()
        check("build-elastica-geometry", ["lake", "build", "Elastica.Geometry"],
              cwd=ROOT / "lean")
        if report["errors"]:
            return report

        report["stage"] = "lean_compilation_and_axioms"
        save()
        report["lean_results"] = verify_modules(
            root=ROOT,
            selected=MODULES,
            output="forgetting-roundtrips-lean",
        )
        if not report["lean_results"]["passed"]:
            report["errors"].append("Standalone Lean verification failed; see lean_results")
        report["passed"] = not report["errors"]
        report["stage"] = "completed"
    except Exception as error:
        report["errors"].append(type(error).__name__ + ": " + str(error))
    finally:
        save()
    return report


def main():
    report = run()
    print(json.dumps({
        "passed": report["passed"],
        "stage": report["stage"],
        "errors": report["errors"],
        "report": str(OUT / "report.json"),
    }, ensure_ascii=False, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
