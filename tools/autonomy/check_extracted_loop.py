#!/usr/bin/env python3
"""Fail-closed independent finite check of the REAL primitive-lean growth ledger.

This is an additional gate. It never seals, writes proofs or replaces Lean CI.
The source of truth remains tools/autonomy/grow.py + pinned Lean/method audit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

CONTROL_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(CONTROL_ROOT))

from loopcore.adapters import finite
from tools.autonomy import grow


def verify(root: Path, require_sealed: bool = False):
    ledger = json.loads((root / grow.LEDGER_PATH).read_text(encoding="utf-8"))
    cycles = ledger.get("cycles")
    if ledger.get("schema_version") != 1 or not isinstance(cycles, list):
        raise ValueError("invalid original growth ledger")
    known = {tuple(sorted(m.items())) for m in finite.candidates()}
    seen = set()
    for pos, row in enumerate(cycles, 1):
        if row.get("cycle") != pos:
            raise ValueError("nonsequential growth ledger")
        model = row.get("model")
        if not isinstance(model, dict):
            raise ValueError("missing model")
        fingerprint = tuple(sorted(model.items()))
        if fingerprint not in known or fingerprint in seen:
            raise ValueError("invalid or duplicated finite model")
        seen.add(fingerprint)
        status = row.get("status")
        if status != "verified" and not (pos == len(cycles) and status == "candidate" and not require_sealed):
            raise ValueError(f"unverified growth cycle at {pos}")
        target = Path(row["source"])
        if target.is_absolute() or ".." in target.parts or target.parts[:2] != ("linear_input", "lean_check"):
            raise ValueError("unsafe proof source path")
        source = (root / target).read_bytes()
        if hashlib.sha256(source).hexdigest() != row.get("sha256"):
            raise ValueError(f"original proof hash mismatch at {pos}")
        expected = grow.proof_source(pos, model).encode("utf-8")
        if source != expected:
            raise ValueError(f"original proof source template mismatch at {pos}")
        finite_report = finite.check(model, finite.build(model, pos), pos)
        if finite_report.get("passed") is not True:
            raise ValueError(f"independent finite check failed at {pos}")
    return {
        "passed": True,
        "source_of_truth": "primitive-lean autonomy ledger and original Lean audit",
        "finite_cycles_checked": len(cycles),
        "verified_cycles": sum(r["status"] == "verified" for r in cycles),
        "candidate_cycles": sum(r["status"] == "candidate" for r in cycles),
        "method": "independent_exhaustive_finite_python_and_exact_source_sha256",
        "lean_status": "NOT_RUN_BY_THIS_GATE",
    }


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--root", type=Path, required=True)
    p.add_argument("--sealed", action="store_true")
    args = p.parse_args()
    root = args.root.resolve()
    result = verify(root, require_sealed=args.sealed)
    path = root / "verification" / "operator-loop-reentry.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()
