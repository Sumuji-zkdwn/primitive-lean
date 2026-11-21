#!/usr/bin/env python3
"""Reproduce both finite research stages and reject stale committed results.

Usage: python3 tools/check_retroactive_translation.py
Python 3.10+, standard library only. Each verifier runs on a temporary copy;
the committed result files are never overwritten by this checker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


if not __debug__:
    raise RuntimeError("Verification requires assertions; do not use -O or PYTHONOPTIMIZE.")


ROOT = Path(__file__).resolve().parents[1]
EXPERIMENTS = ROOT / "experiments" / "retroactive_translation"
CASES = (
    ("stage1/experiments.py", "stage1/results.json"),
    ("stage1/compression_boundary.py", "stage1/compression_results.json"),
    ("stage2/parity_probe_model.py", "stage2/parity_probe_results.json"),
    ("stage2/repeated_squaring_model.py", "stage2/repeated_squaring_results.json"),
)


def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_nonfinite(value):
    raise ValueError(f"Nonfinite JSON number: {value}")


def load_normalized(path):
    data = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=reject_duplicate_keys,
        parse_constant=reject_nonfinite,
    )
    canonical = json.dumps(
        data, sort_keys=True, ensure_ascii=False, separators=(",", ":"), allow_nan=False
    ).encode("utf-8")
    return data, canonical


def coverage(results):
    first = results["stage1/results.json"]
    compression = results["stage1/compression_results.json"]
    parity = results["stage2/parity_probe_results.json"]
    square = results["stage2/repeated_squaring_results.json"]
    return {
        "direct_permutation_histories": first["permutation_collapse"]["direct_comparison_histories"],
        "bit_roundtrip_cases": first["fixed_key_public_update"]["roundtrip_cases_exhausted"],
        "secret_table_prefix_cases": first["preshared_lookup_table"]["all_table_prefix_cases_checked"],
        "binary_map_pairs": compression["all_binary_maps_on_four_states"]["pairs_checked"],
        "full_adaptive_DP_budget_cases": parity["small_full_adaptive_DP"]["budget_case_count"],
        "symmetry_DP_budget_cases": parity["larger_symmetry_DP"]["budget_case_count"],
        "optimal_policy_table_column_replays": parity["small_full_adaptive_DP"]["total_replayed_table_J_pairs_across_budget_cases"],
        "expected_budget_counterexample_cases": parity["expected_budget_boundary_counterexample"]["total_table_J_coin_cases"],
        "repeated_squaring_arithmetic_cases": square["exhaustive_arithmetic"]["all_unit_base_and_T_cases"],
        "repeated_squaring_cache_identities": square["exhaustive_arithmetic"]["cache_semigroup_identity_cases"],
        "related_base_identities": square["exhaustive_arithmetic"]["related_base_identity_cases"],
    }


def check(experiment_root=EXPERIMENTS):
    experiment_root = Path(experiment_root)
    for script, expected in CASES:
        for relative in (script, expected):
            if not (experiment_root / relative).is_file():
                raise FileNotFoundError(f"Missing research artifact: {relative}")
    checks, regenerated = [], {}
    with tempfile.TemporaryDirectory(prefix="retroactive-translation-") as directory:
        temporary = Path(directory)
        for script, expected in CASES:
            source = experiment_root / script
            temporary_script = temporary / script
            temporary_script.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, temporary_script)
            completed = subprocess.run(
                [sys.executable, "-B", "-X", "utf8", str(temporary_script)],
                cwd=temporary_script.parent,
                capture_output=True, text=True, encoding="utf-8", timeout=60,
            )
            if completed.returncode:
                diagnostic = (completed.stdout + completed.stderr)[-2000:]
                raise RuntimeError(f"Verifier failed: {script}\n{diagnostic}")
            generated_path = temporary / expected
            if not generated_path.is_file():
                raise FileNotFoundError(f"Verifier produced no result: {expected}")
            _, expected_bytes = load_normalized(experiment_root / expected)
            actual, actual_bytes = load_normalized(generated_path)
            if actual_bytes != expected_bytes:
                raise ValueError(f"Stale or inconsistent committed result: {expected}")
            regenerated[expected] = actual
            checks.append({
                "script": script,
                "result": expected,
                "matched": True,
                "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "normalized_result_sha256": hashlib.sha256(actual_bytes).hexdigest(),
            })
    return {
        "passed": True,
        "artifact_pairs": len(checks),
        "comparison": "Exact canonical JSON; only whitespace and object-key ordering are normalized",
        "scope": "Deterministic finite verification, not a Lean proof, wall-clock lower bound, or cryptographic security proof",
        "checks": checks,
        "coverage": coverage(regenerated),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--experiment-root", type=Path, default=EXPERIMENTS,
        help="Alternative artifact directory for isolated integrity checks",
    )
    args = parser.parse_args(argv)
    try:
        result = check(args.experiment_root)
    except (OSError, ValueError, RuntimeError, KeyError, subprocess.TimeoutExpired) as error:
        print(json.dumps({"passed": False, "error": str(error)}, ensure_ascii=False))
        return 1
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
