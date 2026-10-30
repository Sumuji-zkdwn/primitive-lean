"""Audit the 717-theorem Kaggle result against its exact CI handoff."""
from pathlib import PurePosixPath
import argparse
import hashlib
import json
import zipfile

MAX_ARCHIVE_BYTES = 256 * 1024 * 1024
MAX_ENTRIES = 10000
EXPECTED_THEOREMS = 717
EXPECTED_DECLARATIONS = 836
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _read_json(archive, name):
    try:
        return json.loads(archive.read(name).decode("utf-8"))
    except KeyError:
        raise ValueError("Result archive lacks " + name) from None


def audit(result_zip, expected_source, handoff_path, notebook_path=None):
    if len(expected_source) != 40 or any(c not in "0123456789abcdef" for c in expected_source):
        raise ValueError("expected-source must be a full lowercase commit SHA")
    handoff = json.loads(open(handoff_path, encoding="utf-8").read())
    if handoff.get("schema") != "primitive-lean-kaggle-handoff-717-v1":
        raise ValueError("Unexpected handoff manifest schema")
    if handoff.get("proof_source_commit") != expected_source:
        raise ValueError("Handoff manifest source does not match expected-source")
    source_manifest = handoff.get("source_snapshot", {}).get("source_sha256", {})
    if len(source_manifest) != 126:
        raise ValueError("Handoff manifest does not specify 126 pinned source files")

    notebook_digest = None
    if notebook_path:
        notebook_digest = sha_file(notebook_path)
        notebook_name = "primitive_lean_717_proof_check.ipynb"
        expected_notebook = handoff.get("notebooks", {}).get(notebook_name, {}).get("sha256")
        if not expected_notebook or notebook_digest != expected_notebook:
            raise ValueError("Notebook bytes do not match the CI handoff manifest")

    with zipfile.ZipFile(result_zip) as archive:
        infos = archive.infolist()
        if len(infos) > MAX_ENTRIES:
            raise ValueError("Result archive has too many entries")
        if sum(info.file_size for info in infos) > MAX_ARCHIVE_BYTES:
            raise ValueError("Result archive exceeds the size limit")
        names = [info.filename for info in infos]
        if len(names) != len(set(names)):
            raise ValueError("Result archive has duplicate paths")
        for name in names:
            path = PurePosixPath(name)
            if path.is_absolute() or ".." in path.parts or "\\" in name:
                raise ValueError("Result archive contains an unsafe path")
        corrupt = archive.testzip()
        if corrupt is not None:
            raise ValueError("Result archive CRC failure: " + corrupt)
        state = _read_json(archive, "notebook_run.json")
        main = _read_json(archive, "proofs/verification/main-result.json")

    source = state.get("source", {})
    setup = state.get("setup", {})
    proofs = state.get("proofs", {})
    if state.get("source_commit") != expected_source or source.get("source_commit") != expected_source:
        raise ValueError("Notebook result is not pinned to the expected proof source")
    if source.get("status") != "passed" or source.get("verified_files") != 126:
        raise ValueError("Notebook did not verify the 126-file source snapshot")
    if source.get("sha256") != source_manifest:
        raise ValueError("Notebook source hashes differ from the CI handoff manifest")
    if setup.get("status") != "passed":
        raise ValueError("Lean setup did not pass")
    if setup.get("toolchain") != handoff["lean"]["toolchain"]:
        raise ValueError("Lean toolchain differs from the handoff manifest")
    expected_dependencies = handoff["lean"]["dependencies"]
    actual_dependencies = [{"name": row.get("name"), "revision": row.get("actual")}
                           for row in setup.get("dependencies", []) if row.get("match") is True]
    if actual_dependencies != expected_dependencies or len(actual_dependencies) != len(expected_dependencies):
        raise ValueError("Kaggle dependency revisions differ from the pinned manifest")
    if proofs.get("status") != "passed" or proofs.get("run", {}).get("exit_code") != 0:
        raise ValueError("Notebook did not record a fresh passing Lean run")
    proof_result = proofs.get("result", {})
    if (proof_result.get("passed") is not True
            or proof_result.get("theorem_count") != EXPECTED_THEOREMS
            or proof_result.get("declaration_count") != EXPECTED_DECLARATIONS):
        raise ValueError("Proof-only report does not show 717/836 passing")
    stages = proof_result.get("stages", [])
    if len(stages) != 2 or any(
        stage.get("passed") is not True or stage.get("run", {}).get("exit_code") != 0
        or stage.get("run", {}).get("warnings") for stage in stages
    ):
        raise ValueError("Both Lean proof stages must have fresh zero-exit runs without warnings")
    if (main.get("passed") is not True
            or main.get("total_theorem_count") != EXPECTED_THEOREMS
            or main.get("total_declaration_count") != EXPECTED_DECLARATIONS
            or main.get("joint_axiom_audit") is not True
            or main.get("baseline_axioms_match") is not True):
        raise ValueError("Fresh joint axiom report does not show all 836 declarations passing")
    declarations = main.get("all_declarations", [])
    axioms = main.get("axioms", {})
    if len(declarations) != EXPECTED_DECLARATIONS or len(axioms) != EXPECTED_DECLARATIONS:
        raise ValueError("Axiom audit is incomplete")
    if main.get("errors") or main.get("unexpected") or main.get("warnings") or main.get("forbidden_tokens"):
        raise ValueError("Axiom report contains errors, warnings, or unexpected axioms")
    if any(not set(value).issubset(ALLOWED_AXIOMS) for value in axioms.values()):
        raise ValueError("Axiom report contains an unapproved axiom")
    for path in handoff["source_snapshot"]["added_proof_sources"]:
        if main.get("source_hashes", {}).get(path) != source_manifest.get(path):
            raise ValueError("Fresh Lean report source hash mismatch: " + path)
    if handoff.get("proof_counts") != {"theorems": EXPECTED_THEOREMS, "declarations": EXPECTED_DECLARATIONS}:
        raise ValueError("Handoff proof counts are inconsistent")

    return {
        "status": "PASS",
        "proof_source_commit": expected_source,
        "notebook_run_id": state.get("run_id"),
        "verified_source_files": source["verified_files"],
        "lean_toolchain": setup["toolchain"],
        "dependency_count": len(actual_dependencies),
        "theorem_count": proof_result["theorem_count"],
        "declaration_count": proof_result["declaration_count"],
        "axioms_audited": len(axioms),
        "proof_exit_code": proofs["run"]["exit_code"],
        "notebook_sha256": notebook_digest,
        "scope": "Fresh Kaggle source, setup, Lean proof and 836-declaration axiom checks for the pinned 717-theorem commit",
        "official_competition_submission": False,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result_zip")
    parser.add_argument("--expected-source", required=True)
    parser.add_argument("--handoff", required=True)
    parser.add_argument("--notebook")
    parser.add_argument("--out")
    args = parser.parse_args(argv)
    try:
        report = audit(args.result_zip, args.expected_source, args.handoff, args.notebook)
    except (OSError, ValueError, KeyError, TypeError, zipfile.BadZipFile) as error:
        report = {"status": "FAIL", "error": str(error)}
        code = 1
    else:
        code = 0
    text = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as stream:
            stream.write(text)
    print(text, end="")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
