#!/usr/bin/env python3
"""Reproduce the archived CPR comparisons from bundled derived inputs only.

All archived scripts run in a disposable copy. Archived results are never
overwritten. The only persistent output is the verification record requested
by --output (default: verification.json beside this script).

This verifies numerical reproduction, not the scientific assumptions of the
model or the raw-log/design audits that require the omitted source archives.
"""
from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import math
import os
from pathlib import Path, PurePosixPath
import platform
import shutil
import subprocess
import sys
import tempfile
import time


BASE = Path(__file__).resolve().parent
MANIFEST = "cpr_coop_comp/package_manifest.json"
EXPECTED_MANIFEST_FILES = 521
EXPECTED_CONTROL_NPZ = 314
REL_TOL = 1e-12
ABS_TOL = 1e-12
FONT = Path("/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc")
FONT_SHA256 = "b76b0433203017ca80401b2ee0dd69350349871c4b19d504c34dbdd80541690a"
TEXT_COLUMNS = {"trial", "subject", "pair_id", "condition", "group", "metric", "analysis", "qc"}
STAGES = (
    ("cpr_coop_comp/analyze_conditions.py", (
        "cpr_coop_comp/round_metrics.csv",
        "cpr_coop_comp/dyad_metrics.csv",
        "cpr_coop_comp/condition_comparison.csv",
        "cpr_coop_comp/by_round.csv",
        "cpr_coop_comp/comparison.json",
    )),
    ("cpr_coop_comp/controls/analyze_controls.py", (
        "cpr_coop_comp/controls/prefix90_trials.csv",
        "cpr_coop_comp/controls/prefix90_pairs.csv",
        "cpr_coop_comp/controls/prefix90_group_summary.csv",
        "cpr_coop_comp/controls/spatial99_trials.csv",
        "cpr_coop_comp/controls/spatial99_pairs.csv",
        "cpr_coop_comp/controls/spatial99_group_summary.csv",
        "cpr_coop_comp/controls/group_differences.csv",
        "cpr_coop_comp/controls/metadata.json",
    )),
    ("cpr_coop_comp/analyze_controls.py", (
        "cpr_coop_comp/control_round_metrics.csv",
        "cpr_coop_comp/control_dyad_metrics.csv",
        "cpr_coop_comp/control_comparison.json",
    )),
    ("cpr_coop_comp/audit/check_controls.py", (
        "cpr_coop_comp/audit/control_comparison_check.json",
    )),
    ("cpr_coop_comp/render_comparison.py", (
        "cpr_coop_comp/coop_comp_comparison.png",
        "cpr_coop_comp/figure_metadata.json",
    )),
)


class VerificationError(RuntimeError):
    """A deliberately concise failure message without raw data or temp paths."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def versions():
    result = {"python": platform.python_version(), "implementation": platform.python_implementation(),
              "system": platform.system(), "machine": platform.machine()}
    for package in ("numpy", "matplotlib", "Pillow"):
        try:
            result[package] = importlib.metadata.version(package)
        except importlib.metadata.PackageNotFoundError:
            result[package] = "not installed"
    return result


def manifest_entries():
    require((BASE / MANIFEST).is_file(), f"Missing {MANIFEST}")
    manifest = json.loads((BASE / MANIFEST).read_text(encoding="utf-8"))
    entries = manifest.get("files", [])
    require(len(entries) == EXPECTED_MANIFEST_FILES, "Unexpected archived manifest entry count")
    require(manifest.get("raw_archives_included") is False, "Unexpected raw-archive inclusion")
    seen = set()
    for entry in entries:
        relative = entry["path"]
        path = PurePosixPath(relative)
        require(not path.is_absolute() and ".." not in path.parts, "Unsafe manifest path")
        require(relative not in seen and relative != MANIFEST, "Duplicate or self-referential manifest entry")
        require(not (BASE / relative).is_symlink(), f"Unexpected symlink: {relative}")
        seen.add(relative)
    return entries


def check_manifest(entries):
    for entry in entries:
        relative = entry["path"]
        path = BASE / relative
        require(path.is_file(), f"Missing archived file: {relative}")
        require(path.stat().st_size == entry["size_bytes"], f"Archived size mismatch: {relative}")
        require(sha256(path) == entry["sha256"], f"Archived SHA256 mismatch: {relative}")


class ScalarComparison:
    def __init__(self):
        self.numeric_values = 0
        self.exact_values = 0
        self.max_absolute_difference = 0.0
        self.max_relative_difference = 0.0

    def number(self, expected, actual, location):
        self.numeric_values += 1
        if isinstance(expected, int) and isinstance(actual, int):
            require(expected == actual, f"Integer mismatch: {location}")
            return
        expected, actual = float(expected), float(actual)
        if math.isnan(expected) or math.isnan(actual):
            require(math.isnan(expected) and math.isnan(actual), f"NaN mismatch: {location}")
            return
        if math.isinf(expected) or math.isinf(actual):
            require(expected == actual, f"Infinity mismatch: {location}")
            return
        difference = abs(expected - actual)
        self.max_absolute_difference = max(self.max_absolute_difference, difference)
        scale = max(abs(expected), abs(actual))
        relative = difference / scale if scale else 0.0
        self.max_relative_difference = max(self.max_relative_difference, relative)
        require(math.isclose(expected, actual, rel_tol=REL_TOL, abs_tol=ABS_TOL),
                f"Numerical mismatch: {location}")

    def exact(self, expected, actual, location):
        self.exact_values += 1
        require(type(expected) is type(actual) and expected == actual, f"Value mismatch: {location}")

    def as_dict(self):
        return {"relative_tolerance": REL_TOL, "absolute_tolerance": ABS_TOL,
                "numeric_values_compared": self.numeric_values,
                "exact_non_numeric_values_compared": self.exact_values,
                "max_absolute_difference": self.max_absolute_difference,
                "max_relative_difference": self.max_relative_difference}


def compare_csv(relative, work, comparison):
    def read(path):
        with path.open(newline="", encoding="utf-8-sig") as stream:
            return list(csv.reader(stream))
    original, rebuilt = read(BASE / relative), read(work / relative)
    require(len(original) == len(rebuilt), f"CSV row count mismatch: {relative}")
    require(bool(original) and original[0] == rebuilt[0], f"CSV header mismatch: {relative}")
    header = original[0]
    for row_index, (old, new) in enumerate(zip(original[1:], rebuilt[1:]), 1):
        require(len(old) == len(new) == len(header), f"CSV column count mismatch: {relative}")
        for column, left, right in zip(header, old, new):
            location = f"{relative}:row{row_index}:{column}"
            if column not in TEXT_COLUMNS:
                try:
                    numeric_left, numeric_right = float(left), float(right)
                except ValueError:
                    pass
                else:
                    comparison.number(numeric_left, numeric_right, location)
                    continue
            comparison.exact(left, right, location)
    return {"path": relative, "rows": len(original) - 1, "columns": len(header), "status": "pass"}


def compare_json(relative, work, comparison):
    original = json.loads((BASE / relative).read_text(encoding="utf-8"))
    rebuilt = json.loads((work / relative).read_text(encoding="utf-8"))
    ignored = []

    def walk(left, right, keys=()):
        location = relative + (":" + ".".join(map(str, keys)) if keys else "")
        if isinstance(left, dict):
            require(isinstance(right, dict) and left.keys() == right.keys(), f"JSON keys mismatch: {location}")
            for key in left:
                if relative == "cpr_coop_comp/controls/metadata.json" and not keys and key == "wall_seconds":
                    ignored.append("wall_seconds")
                    continue
                walk(left[key], right[key], (*keys, key))
        elif isinstance(left, list):
            require(isinstance(right, list) and len(left) == len(right), f"JSON list mismatch: {location}")
            for index, (x, y) in enumerate(zip(left, right)):
                walk(x, y, (*keys, index))
        elif isinstance(left, (int, float)) and not isinstance(left, bool):
            require(isinstance(right, (int, float)) and not isinstance(right, bool), f"JSON type mismatch: {location}")
            comparison.number(left, right, location)
        else:
            comparison.exact(left, right, location)

    walk(original, rebuilt)
    return {"path": relative, "ignored_fields": ignored, "status": "pass"}


def compare_npz(paths, work):
    import numpy as np
    arrays = elements = 0
    for relative in paths:
        with np.load(BASE / relative, allow_pickle=False) as original, \
                np.load(work / relative, allow_pickle=False) as rebuilt:
            require(set(original.files) == set(rebuilt.files), f"NPZ keys mismatch: {relative}")
            for key in original.files:
                left, right = original[key], rebuilt[key]
                location = f"{relative}:{key}"
                require(left.dtype == right.dtype and left.shape == right.shape, f"NPZ layout mismatch: {location}")
                require(np.array_equal(left, right, equal_nan=True), f"NPZ array mismatch: {location}")
                arrays += 1
                elements += left.size
    return {"files_compared": len(paths), "arrays_compared": arrays, "elements_compared": elements,
            "criterion": "Identical keys, shapes, dtypes and array values; no numerical tolerance", "status": "pass"}


def check_figure(work):
    import numpy as np
    from PIL import Image
    relative = "cpr_coop_comp/coop_comp_comparison.png"
    with Image.open(work / relative) as image:
        require(image.format == "PNG", "Regenerated figure is not PNG")
        image.verify()
    with Image.open(work / relative) as image, Image.open(BASE / relative) as archived:
        require(image.size == archived.size, "Regenerated figure dimensions differ")
        pixels = np.asarray(image.convert("RGB"))
        require(np.any(pixels != pixels[0, 0]), "Regenerated figure is blank")
        pixel_equal = bool(np.array_equal(pixels, np.asarray(archived.convert("RGB"))))
        dimensions = list(image.size)
    return {"path": relative, "dimensions_pixels": dimensions, "decoded_successfully": True,
            "nonblank": True, "pixels_equal_to_archive": pixel_equal,
            "sha256_equal_to_archive": sha256(work / relative) == sha256(BASE / relative),
            "criterion": "Fresh PNG generated and decoded, nonblank, same dimensions; figure metadata also compared numerically",
            "status": "pass"}


def run_stage(relative, expected_outputs, work):
    print(f"Running {relative}", flush=True)
    environment = os.environ.copy()
    environment.pop("PYTHONOPTIMIZE", None)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["MPLBACKEND"] = "Agg"
    environment["MPLCONFIGDIR"] = str(work / ".matplotlib-cache")
    started = time.perf_counter()
    try:
        completed = subprocess.run([sys.executable, "-B", relative], cwd=work, env=environment,
                                   capture_output=True, text=True, check=False, timeout=300)
    except subprocess.TimeoutExpired as error:
        raise VerificationError(f"Timed out: {relative}") from error
    require(completed.returncode == 0, f"Stage exited with code {completed.returncode}: {relative}")
    for output in expected_outputs:
        require((work / output).is_file(), f"Stage did not generate {output}")
    return {"script": relative, "command": ["python", "-B", relative], "returncode": completed.returncode,
            "elapsed_seconds": round(time.perf_counter() - started, 3), "status": "pass"}


def verify(record):
    require(sys.flags.optimize == 0, "Run without -O/-OO or an optimizing PYTHONOPTIMIZE value; archived assertions must execute")
    require(FONT.is_file(), "Required NotoSansCJK-Regular.ttc font is unavailable")
    require(sha256(FONT) == FONT_SHA256, "Required Japanese font SHA256 differs from the pinned file")
    record["font"] = {"filename": FONT.name, "sha256": FONT_SHA256}
    entries = manifest_entries()
    check_manifest(entries)
    manifest_hash = sha256(BASE / MANIFEST)
    record["archive_integrity"] = {"manifest": MANIFEST, "manifest_sha256": manifest_hash,
                                   "files_checked": len(entries), "size_and_sha256_match": True, "status": "pass"}
    npz_paths = sorted(e["path"] for e in entries if e["path"].endswith(".npz") and
                       e["path"].startswith(("cpr_coop_comp/controls/prefix90/", "cpr_coop_comp/controls/spatial99/")))
    require(len(npz_paths) == EXPECTED_CONTROL_NPZ, "Unexpected control NPZ count")
    scalar_outputs = [path for _, outputs in STAGES for path in outputs if path.endswith((".csv", ".json"))]
    all_outputs = [path for _, outputs in STAGES for path in outputs] + npz_paths
    comparison = ScalarComparison()
    record["stages"] = []
    record["csv_checks"] = []
    record["json_checks"] = []
    try:
        with tempfile.TemporaryDirectory(prefix="cpr-sandpile-reproduction-") as temporary:
            work = Path(temporary)
            for relative in [e["path"] for e in entries] + [MANIFEST]:
                target = work / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(BASE / relative, target)
            # Eliminate every regenerated output first; archived copies cannot
            # accidentally satisfy the reproduction checks.
            for relative in all_outputs:
                (work / relative).unlink()
            for script, outputs in STAGES:
                stage_outputs = (*outputs, *npz_paths) if script == "cpr_coop_comp/controls/analyze_controls.py" else outputs
                record["stages"].append(run_stage(script, stage_outputs, work))
            for relative in scalar_outputs:
                if relative.endswith(".csv"):
                    record["csv_checks"].append(compare_csv(relative, work, comparison))
                else:
                    record["json_checks"].append(compare_json(relative, work, comparison))
            record["scalar_comparison"] = comparison.as_dict()
            record["control_arrays"] = compare_npz(npz_paths, work)
            record["figure"] = check_figure(work)
            main = json.loads((work / "cpr_coop_comp/comparison.json").read_text())
            controls = json.loads((work / "cpr_coop_comp/control_comparison.json").read_text())
            audit = json.loads((work / "cpr_coop_comp/audit/control_comparison_check.json").read_text())
            require(len(main["comparison"]) == 5 and len(controls["results"]) == 2 and len(controls["holm_seven"]) == 7,
                    "Unexpected primary/control metric family size")
            require(audit["status"] == "pass", "Independent control audit did not pass")
            record["reproduced_scope"] = {
                "trials": main["main_rounds"], "main_metrics": len(main["comparison"]),
                "control_metrics": len(controls["results"]), "holm_family_size": len(controls["holm_seven"]),
                "prefix_harvest_count": 90, "spatial_shuffles_per_trial": 99,
                "main_bootstrap_seed": main["methods"]["seed"],
                "control_bootstrap_seed": controls["method"]["bootstrap_seed"],
                "main_bootstrap_draws": main["methods"]["bootstrap_draws"],
                "control_bootstrap_draws": controls["method"]["bootstrap_draws"],
                "exact_label_assignments": main["methods"]["exact_assignments"],
                "independent_control_audit": audit["status"],
            }
    finally:
        check_manifest(entries)
        require(sha256(BASE / MANIFEST) == manifest_hash, "Original package manifest changed during verification")
        record["original_archive_unchanged"] = True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=BASE / "verification.json",
                        help="Verification JSON path; relative paths are resolved from the current working directory")
    args = parser.parse_args()
    try:
        output_relative = args.output.resolve().relative_to(BASE)
    except ValueError:
        pass
    else:
        if output_relative.parts and (output_relative.parts[0] in {"cpr_coop_comp", "cpr_empirical", "cpr_redefinition"}
                                      or output_relative == Path(__file__).relative_to(BASE)):
            print(json.dumps({"result": "fail", "failure": "--output must not overwrite an archived file or the runner"}))
            return 2
    record = {
        "schema_version": 1,
        "result": "running",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "package_root": "experiments/cpr_sandpile",
        "runner": "verify_reproduction.py",
        "runner_sha256": sha256(Path(__file__)),
        "versions": versions(),
        "execution_policy": "Archived scripts execute only in a disposable copy; regenerated outputs are removed before execution; optimization disabled",
        "not_rerun": [
            {"script": "cpr_coop_comp/audit/independent_compare.py", "reason": "Requires omitted raw ZIP; its pinned saved audit is used as an input"},
            {"script": "cpr_coop_comp/design/audit_design_and_describe.py", "reason": "Requires omitted raw ZIP and original design records"},
            {"script": "cpr_empirical/analyze_sand.py", "reason": "Raw-log baseline requires omitted source archives"},
            {"script": "cpr_redefinition/harvest_asm/analyze_harvest_asm.py", "reason": "Full baseline requires omitted source archives and upstream files; bundled derived summaries/events/NPZ are inputs"},
        ],
        "interpretation": "Numerical reproduction of the bundled derived-data analysis, not validation of causal, independence, exchangeability or mechanistic assumptions",
    }
    started = time.perf_counter()
    try:
        verify(record)
    except VerificationError as error:
        record["result"] = "fail"
        record["failure"] = str(error)
    except Exception as error:
        # Do not place raw subprocess output, participant labels or temporary
        # directory names in the public verification record.
        record["result"] = "fail"
        record["failure"] = f"Unexpected {type(error).__name__}; no archived output was intentionally modified"
    else:
        record["result"] = "pass"
    record["elapsed_seconds"] = round(time.perf_counter() - started, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"result": record["result"], "elapsed_seconds": record["elapsed_seconds"],
                      "failure": record.get("failure")}, ensure_ascii=False), flush=True)
    return 0 if record["result"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
