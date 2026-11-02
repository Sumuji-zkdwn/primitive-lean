"""Fresh Lean checks without the separate historical-delivery audit.

Called only through tools/verify.py --proof-only. Proof sources and the two
existing checkers are unchanged. This mode does not certify archived releases.
"""
from pathlib import Path
from datetime import datetime, timezone
import json
import shutil
import sys
import time


def run_proof_only(root, command, rebuild=False):
    root = Path(root).resolve()
    out = root / "verification"
    out.mkdir(exist_ok=True)
    result_path = out / "proof-only.json"
    result = dict(
        timestamp_utc=datetime.now(timezone.utc).isoformat(), passed=False,
        scope="Fresh Elastica build and joint Lean proof/axiom checks only",
        historical_preservation="not_checked", delivery_and_rendering="not_checked",
        build_requested=True, clean_project_build=rebuild, stages=[], errors=[],
        theorem_count=None, declaration_count=None,
    )

    def save():
        result_path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", "utf-8")

    def retire(path):
        if path.exists():
            history = out / "proof-history"
            history.mkdir(exist_ok=True)
            path.rename(history / (path.stem + "-" + str(time.time_ns()) + path.suffix))

    retire(result_path)
    save()
    try:
        if rebuild:
            target = (root / "lean/.lake/build").resolve()
            if target != root / "lean/.lake/build":
                raise ValueError("Refusing to clean an external/symlinked build directory")
            if target.exists():
                shutil.rmtree(target)
        stages = (
            ("joint", "linear_input/verify_lean.py", root / "linear_input/lean_results.json"),
            ("supplement", "tools/verify_main_result.py", out / "main-result.json"),
        )
        for name, script, report_path in stages:
            # A previous successful report must never stand in for this run.
            retire(report_path)
            run = command([sys.executable, "-X", "utf8", script], "proof-only-" + name, cwd=root)
            row = dict(name=name, run=run, fresh_report=report_path.is_file(), passed=False)
            result["stages"].append(row)
            if report_path.is_file():
                report = json.loads(report_path.read_text("utf-8"))
                row["passed"] = run["exit_code"] == 0 and report.get("passed") is True
                row["report"] = report_path.relative_to(root).as_posix()
                row["warnings"] = run.get("warnings", [])
                if row["warnings"]:
                    row["passed"] = False
                if name == "supplement" and row["passed"]:
                    result["theorem_count"] = report["total_theorem_count"]
                    result["declaration_count"] = report["total_declaration_count"]
            save()
            if not row["passed"]:
                raise ValueError(name + " checker failed or did not produce a fresh passing report")
        result["passed"] = True
    except (OSError, ValueError, KeyError, TypeError) as error:
        result["errors"].append(str(error))
    save()
    return result
