"""Supplemental consistency audit for 494-theorem result ZIPs.

This is separate from the historical handoff auditor. It checks internal records,
not their authenticity or their independent correspondence to a notebook or commit.
"""
import argparse
import hashlib
import json
import re
import zipfile

from audit_kaggle_result import audit as historical_audit

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LOGS = (
    "proof-run.log", "proofs/verification/main-result.log",
    "proofs/verification/proof-only-joint.log",
    "proofs/verification/proof-only-supplement.log",
    "proofs/linear_input/lean_check/build.log",
    "proofs/linear_input/lean_check/elastica-build.log",
)


def audit_records(path, expected_source):
    report = historical_audit(path, expected_source)
    with zipfile.ZipFile(path) as archive:
        names = set(archive.namelist())
        required = (*LOGS, "notebook_run.json", "proofs/verification/proof-only.json",
                    "proofs/verification/main-result.json", "proofs/linear_input/lean_results.json")
        for name in required:
            if name not in names:
                raise ValueError("Result archive lacks " + name)
        state = json.loads(archive.read("notebook_run.json"))
        proof = json.loads(archive.read("proofs/verification/proof-only.json"))
        main = json.loads(archive.read("proofs/verification/main-result.json"))
        joint = json.loads(archive.read("proofs/linear_input/lean_results.json"))
        if hashlib.sha256(archive.read("proofs/verification/main-result.log")).hexdigest() != main.get("log_sha256"):
            raise ValueError("Supplement log hash differs from the recorded hash")

    if proof != state.get("proofs", {}).get("result"):
        raise ValueError("Stored proof report differs from notebook record")
    source = state.get("source", {})
    hashes = source.get("sha256", {})
    if (not isinstance(hashes, dict) or source.get("verified_files") != 117 or len(hashes) != 117
            or any(not isinstance(path, str) or not isinstance(digest, str)
                   or re.fullmatch(r"[0-9a-f]{64}", digest) is None for path, digest in hashes.items())):
        raise ValueError("Source hash inventory is incomplete or malformed")
    proof_hashes = main.get("source_hashes", {})
    if (not isinstance(proof_hashes, dict) or not set(proof_hashes).intersection(hashes)
            or any(hashes[k] != proof_hashes[k] for k in set(proof_hashes).intersection(hashes))):
        raise ValueError("Source hashes disagree with the supplement report")
    if (proof.get("passed") is not True or proof.get("theorem_count") != 494
            or proof.get("declaration_count") != 538 or proof.get("errors")):
        raise ValueError("Proof report does not show 494 theorems / 538 declarations passing")
    stages = proof.get("stages", [])
    if ([s.get("name") for s in stages] != ["joint", "supplement"]
            or any(s.get("passed") is not True or s.get("fresh_report") is not True
                   or s.get("run", {}).get("exit_code") != 0 or s.get("warnings")
                   or s.get("run", {}).get("warnings") for s in stages)):
        raise ValueError("Both proof stages must be fresh, passing and warning-free")
    if (main.get("passed") is not True or main.get("total_theorem_count") != 494
            or main.get("total_declaration_count") != 538 or main.get("joint_axiom_audit") is not True
            or main.get("baseline_axioms_match") is not True
            or main.get("compile", {}).get("exit_code") != 0
            or any(main.get(k) for k in ("errors", "warnings", "unexpected", "forbidden_tokens", "changed_during_verification"))):
        raise ValueError("Supplement report does not show a complete passing audit")
    declarations = main.get("all_declarations", [])
    axioms = main.get("axioms", {})
    declaration_names = [row.get("name") for row in declarations]
    if (len(declaration_names) != 538 or len(set(declaration_names)) != 538
            or set(declaration_names) != set(axioms)
            or any(not isinstance(value, list) or not set(value).issubset(ALLOWED_AXIOMS)
                   for value in axioms.values())):
        raise ValueError("Declaration names or allowed axioms are inconsistent")
    if (joint.get("passed") is not True or joint.get("joint_axiom_audit") is not True
            or joint.get("compile", {}).get("exit_code") != 0
            or joint.get("unexpected") or joint.get("forbidden_tokens")):
        raise ValueError("Joint report does not show a passing audit")
    deps = state.get("setup", {}).get("dependencies", [])
    if (len(deps) != 9 or len({d.get("name") for d in deps}) != 9
            or any(d.get("match") is not True or d.get("expected") != d.get("actual") for d in deps)
            or deps != joint.get("dependencies") or deps != main.get("dependencies")
            or deps != main.get("dependencies_after_compile")):
        raise ValueError("Dependency revision records disagree")
    report["scope"] = ("Internal consistency of recorded 494/538 evidence only; does not rerun Lean "
                       "or authenticate the source commit, Notebook, Kaggle execution, or records")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result_zip")
    parser.add_argument("--expected-source", required=True)
    args = parser.parse_args()
    try:
        result = audit_records(args.result_zip, args.expected_source)
    except (OSError, ValueError, KeyError, TypeError, zipfile.BadZipFile) as error:
        print(json.dumps({"status": "FAIL", "error": str(error)}, ensure_ascii=False))
        return 1
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
