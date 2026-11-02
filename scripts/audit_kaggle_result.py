"""Audit a Kaggle result ZIP against the GitHub source commit in its handoff."""
from pathlib import PurePosixPath
import argparse
import json
import sys
import zipfile


MAX_ARCHIVE_BYTES = 256 * 1024 * 1024
MAX_ENTRIES = 10000


def audit(result_zip, expected_source):
    result_zip = str(result_zip)
    if len(expected_source) != 40 or any(c not in "0123456789abcdef" for c in expected_source):
        raise ValueError("expected-source must be a full lowercase commit SHA")
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
        if "notebook_run.json" not in names:
            raise ValueError("Result archive lacks notebook_run.json")
        state = json.loads(archive.read("notebook_run.json").decode("utf-8"))

    source = state.get("source", {})
    setup = state.get("setup", {})
    proofs = state.get("proofs", {})
    if state.get("source_commit") != expected_source:
        raise ValueError("Notebook run source commit does not match the handoff")
    if source.get("status") != "passed" or source.get("source_commit") != expected_source:
        raise ValueError("Notebook did not pass source verification for the handoff commit")
    if setup.get("status") != "passed":
        raise ValueError("Notebook did not pass Lean environment setup")
    proof_result = proofs.get("result", {})
    proof_run = proofs.get("run", {})
    if (proofs.get("status") != "passed" or proof_result.get("passed") is not True
            or proof_run.get("exit_code") != 0):
        raise ValueError("Notebook did not record a fresh passing proof check")
    if not source.get("sha256") or not source.get("verified_files"):
        raise ValueError("Notebook result lacks source hash evidence")
    if not proof_result.get("timestamp_utc") or not proof_result.get("stages"):
        raise ValueError("Proof report lacks fresh stage evidence")

    return {
        "status": "PASS",
        "source_commit": expected_source,
        "run_id": state.get("run_id"),
        "verified_files": source["verified_files"],
        "source_sha256": source["sha256"],
        "theorem_count": proof_result.get("theorem_count"),
        "declaration_count": proof_result.get("declaration_count"),
        "proof_exit_code": proof_run["exit_code"],
        "scope": "Kaggle Notebook source, setup, proof-only and axiom checks for this pinned commit",
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result_zip")
    parser.add_argument("--expected-source", required=True)
    parser.add_argument("--out")
    args = parser.parse_args(argv)
    try:
        report = audit(args.result_zip, args.expected_source)
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
