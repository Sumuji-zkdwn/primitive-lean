#!/usr/bin/env python3
"""Generate a private Lean 4.36 compatibility copy from verbatim Elastica sources.

The canonical primitive-lean sources and their hashes are never changed.
Only the exact 4 proof-tactic rewrites listed below are allowed.
"""
from __future__ import annotations

import hashlib
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
ORIGINAL = ROOT / "lean"
COMPAT = HERE / "compat"

# Git blob SHA-1 of the two exact source files inspected at PR construction.
PINS = {
    "Elastica/Equations.lean": "ad94ffd23eda631fb7f91c220e2a44bb28de7da7",
    "Elastica/Variation.lean": "f4e5faaad829a008dfeb891d2256e6b35f1f77aa",
    "Elastica/SecondVariation.lean": "35c47942ea382c3441b048c3ff0f4f0b00f3584b",
}


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def replace_once(path: Path, before: str, after: str) -> None:
    data = path.read_text(encoding="utf-8")
    if data.count(before) != 1:
        raise ValueError(f"Expected exactly one replacement in {path}: {before!r}")
    path.write_text(data.replace(before, after), encoding="utf-8")


def main() -> None:
    for rel, expected in PINS.items():
        actual = blob_sha((ORIGINAL / rel).read_bytes())
        if actual != expected:
            raise RuntimeError(f"Refusing to patch changed original: {rel} {actual} != {expected}")
    if COMPAT.exists():
        shutil.rmtree(COMPAT)
    shutil.copytree(ORIGINAL / "Elastica", COMPAT / "Elastica")
    shutil.copy2(ORIGINAL / "Elastica.lean", COMPAT / "Elastica.lean")

    # 'convert' now exposes both pointwise function and ring-identity goals.
    equations = COMPAT / "Elastica" / "Equations.lean"
    replace_once(
        equations,
        "  ring\n\n/-- On an open connected interval",
        "  all_goals first | (funext t; rfl) | ring\n\n/-- On an open connected interval",
    )
    # This obsolete simp rewrite is no longer needed in mathlib 4.36.
    replace_once(
        equations,
        "  simp only [id_eq]\n  ring\n\n/-- The actual second derivative",
        "  all_goals first | (funext x; simp [Pi.pow_apply]) | (simp [id_eq]; ring)\n\n/-- The actual second derivative",
    )
    variation = COMPAT / "Elastica" / "Variation.lean"
    replace_once(
        variation,
        "    simp\n  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le",
        "    all_goals first | (funext x; rfl) | ring\n  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le",
    )
    second_variation = COMPAT / "Elastica" / "SecondVariation.lean"
    replace_once(
        second_variation,
        "    simp\n  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le",
        "    all_goals first | (funext x; rfl) | (simp; ring)\n  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le",
    )
    print("Elastica 4.36 compatibility copy ready: 3 files / 4 proof-tactic edits")


if __name__ == "__main__":
    main()
