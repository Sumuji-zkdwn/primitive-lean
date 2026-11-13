#!/usr/bin/env python3
"""Build a hash-checked Lean 4.36 compatibility copy of Elastica.Variation.

This is the *actual* primitive-lean curvature-energy definition and a
pointwise-derivative proof; no source definitions or theorem statements change.
The canonical Lean 4.30 source is not modified. A later, separately scoped
project can port the full Elastica proof library.
"""
from __future__ import annotations

import hashlib
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
ORIGINAL = ROOT / "lean" / "Elastica" / "Variation.lean"
EXPECTED_GIT_BLOB = "f4e5faaad829a008dfeb891d2256e6b35f1f77aa"
COMPAT = HERE / "compat"
TARGET = COMPAT / "Elastica" / "Variation.lean"

BEFORE = "    simp\n  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le"
AFTER = (
    "    all_goals first | (funext x; rfl) | ring\n"
    "  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le"
)


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    original = ORIGINAL.read_bytes()
    actual = blob_sha(original)
    if actual != EXPECTED_GIT_BLOB:
        raise RuntimeError(f"Original Elastica.Variation changed: {actual} != {EXPECTED_GIT_BLOB}")
    if COMPAT.exists():
        shutil.rmtree(COMPAT)
    TARGET.parent.mkdir(parents=True, exist_ok=True)
    text = original.decode("utf-8")
    if text.count(BEFORE) != 1:
        raise RuntimeError("Expected exactly one Lean 4.30 proof-tactic site")
    TARGET.write_text(text.replace(BEFORE, AFTER), encoding="utf-8")
    print("Prepared hash-pinned Elastica.Variation compatibility copy")
    print("Original Git blob:", actual)
    print("Generated SHA-256:", hashlib.sha256(TARGET.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
