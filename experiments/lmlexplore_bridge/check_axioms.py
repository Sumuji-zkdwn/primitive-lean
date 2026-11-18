#!/usr/bin/env python3
"""Check the current bridge source and reject unapproved theorem axioms.

Run after preparing the compatibility module and building its dependencies.
The generated audit contains the current bridge source, not an import of its
cached .olean. Logs and the machine-readable result live in .lake/axiom-audit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "ElasticaLMLExploreBridge.lean"
NAMESPACE = "ElasticaLMLExploreBridge"
THEOREMS = (
    "curveGibbs_apply",
    "curveGibbs_mem_simplex",
    "curveGibbs_pos",
    "curveFreeEnergy_eq_neg_log_partition_add_kl",
    "curveFreeEnergy_gibbs_eq",
    "curveFreeEnergy_gap_eq_kl",
    "curveFreeEnergy_min",
    "curveFreeEnergy_eq_iff",
)
EXPECTED = {f"{NAMESPACE}.{name}" for name in THEOREMS}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_RECORD = re.compile(
    r"^'([^'\r\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|"
    r"does not depend on any axioms)[ \t]*$",
    re.MULTILINE,
)


def parse_axioms(output: str) -> dict[str, list[str]]:
    """Require exactly one complete, permitted axiom record per theorem."""
    output = re.sub(r"\x1b\[[0-9;]*m", "", output)
    found: dict[str, list[str]] = {}
    for match in AXIOM_RECORD.finditer(output):
        name, raw = match.groups()
        if name not in EXPECTED:
            raise ValueError(f"Unexpected axiom record: {name}")
        if name in found:
            raise ValueError(f"Duplicate axiom record: {name}")
        axioms = [part.strip() for part in raw.split(",")] if raw and raw.strip() else []
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"Unapproved axioms for {name}: {sorted(unexpected)}")
        found[name] = sorted(axioms)
    if set(found) != EXPECTED:
        raise ValueError(f"Missing axiom records: {sorted(EXPECTED - set(found))}")
    return found


def self_test() -> None:
    names = sorted(EXPECTED)
    rows = [f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in names]
    valid = "\n".join(rows)
    assert set(parse_axioms(valid)) == EXPECTED
    alternate = rows.copy()
    alternate[0] = f"'{names[0]}' does not depend on any axioms"
    alternate[1] = f"'{names[1]}' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
    assert parse_axioms("\n".join(alternate))[names[0]] == []
    invalid = {
        "missing": "\n".join(rows[1:]),
        "duplicate": valid + "\n" + rows[0],
        "sorryAx": valid.replace("propext", "sorryAx", 1),
        "new axiom": valid.replace("propext", "Untrusted.newAxiom", 1),
        "unexpected theorem": valid + "\n'Other.theorem' does not depend on any axioms",
        "malformed list": valid.replace("propext,", "propext,,", 1),
        "truncated": valid.rsplit("]", 1)[0],
    }
    for label, output in invalid.items():
        try:
            parse_axioms(output)
        except ValueError:
            continue
        raise AssertionError(f"Accepted invalid fixture: {label}")
    print(f"PASS: axiom parser, 2 positive and {len(invalid)} negative fixtures")


def audit() -> int:
    source_bytes = SOURCE.read_bytes()
    source = source_bytes.decode("utf-8")
    # This small bridge uses ordinary top-level theorem/lemma declarations in
    # one namespace. Require its explicit inventory to stay in sync with CI.
    declared = re.findall(r"(?m)^[ \t]*(?:theorem|lemma)\s+([^\s(:{]+)", source)
    if len(declared) != len(THEOREMS) or set(declared) != set(THEOREMS):
        raise ValueError(f"Update the axiom audit inventory for bridge declarations: {declared}")
    out = HERE / ".lake" / "axiom-audit"
    out.mkdir(parents=True, exist_ok=True)
    audit_file = out / "Audit.lean"
    audit_file.write_text(
        source + "\n" + "\n".join(f"#print axioms {name}" for name in sorted(EXPECTED)) + "\n",
        encoding="utf-8", newline="\n",
    )
    command = ["lake", "env", "lean", "--trust=0", str(audit_file.relative_to(HERE))]
    process = subprocess.run(command, cwd=HERE, capture_output=True, text=True, encoding="utf-8")
    output = process.stdout + process.stderr
    (out / "audit.log").write_text(output, encoding="utf-8", newline="\n")
    errors = []
    if process.returncode:
        errors.append(f"Lean exited with code {process.returncode}")
    axioms: dict[str, list[str]] = {}
    try:
        axioms = parse_axioms(output)
    except ValueError as error:
        errors.append(str(error))
    report = {
        "passed": not errors,
        "source": SOURCE.name,
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "command": command,
        "exit_code": process.returncode,
        "expected_theorems": sorted(EXPECTED),
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "axioms": axioms,
        "errors": errors,
    }
    (out / "audit.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(output, end="")
    print(json.dumps(report, indent=2))
    return 0 if report["passed"] else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="exercise parser without Lean")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    return audit()


if __name__ == "__main__":
    raise SystemExit(main())
