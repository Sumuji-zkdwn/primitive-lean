"""Create a clean, commit-bound Kaggle Notebook handoff package."""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "Sumuji-zkdwn/primitive-lean"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_notebook(path, source_ref, setup, proofs):
    notebook = json.loads(path.read_text("utf-8"))
    if notebook.get("nbformat") != 4:
        raise ValueError(f"Not an nbformat 4 notebook: {path.name}")
    if notebook.get("metadata", {}).get("primitive_lean", {}).get("source_commit") != source_ref:
        raise ValueError(f"Notebook source commit mismatch: {path.name}")
    code = [cell for cell in notebook.get("cells", []) if cell.get("cell_type") == "code"]
    if len(code) != 1:
        raise ValueError(f"Expected exactly one self-contained code cell: {path.name}")
    cell = code[0]
    if cell.get("execution_count") is not None or cell.get("outputs") != []:
        raise ValueError(f"Notebook contains saved execution state: {path.name}")
    source = "".join(cell.get("source", []))
    compile(source, path.name, "exec")
    required = [
        'SOURCE_MODE = "github"',
        f"RUN_SETUP = {setup}",
        f"RUN_PROOFS = {proofs}",
        'GITHUB_SECRET_LABEL = "GITHUB_TOKEN"',
        "primitive_lean_result.zip",
    ]
    for marker in required:
        if marker not in source:
            raise ValueError(f"Notebook missing expected setting {marker!r}: {path.name}")
    for forbidden in ("ghp_", "github_pat_", "KAGGLE_API_TOKEN", "kaggle kernels submit"):
        if forbidden in source:
            raise ValueError(f"Unexpected credential or submission marker in {path.name}")
    return notebook


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-ref", required=True, help="Full commit SHA to embed in both notebooks")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--run-id", default=os_environ("GITHUB_RUN_ID"))
    parser.add_argument("--run-attempt", default=os_environ("GITHUB_RUN_ATTEMPT"))
    parser.add_argument("--server-url", default=os_environ("GITHUB_SERVER_URL"))
    parser.add_argument("--repository", default=os_environ("GITHUB_REPOSITORY", REPOSITORY))
    args = parser.parse_args(argv)

    if len(args.source_ref) != 40 or any(c not in "0123456789abcdef" for c in args.source_ref):
        parser.error("source-ref must be a full lowercase commit SHA")
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    if head != args.source_ref:
        parser.error(f"source-ref must match checked-out HEAD ({head})")
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        parser.error(f"output-dir must be empty: {out}")

    setup_path = out / "primitive_lean_setup_one_cell.ipynb"
    proof_path = out / "primitive_lean_proof_check.ipynb"
    common = [
        sys.executable, "-X", "utf8", str(ROOT / "scripts/build_kaggle_notebook.py"),
        "--source-ref", args.source_ref, "--source-mode", "github",
    ]
    subprocess.run(common + ["--setup-one-cell", "--output", str(setup_path)],
                   cwd=ROOT, check=True)
    subprocess.run(common + ["--proof-check-one-cell", "--output", str(proof_path)],
                   cwd=ROOT, check=True)

    read_notebook(setup_path, args.source_ref, "True", "False")
    read_notebook(proof_path, args.source_ref, "True", "True")
    files = {
        path.name: {"bytes": path.stat().st_size, "sha256": sha256(path)}
        for path in (setup_path, proof_path)
    }
    manifest = {
        "schema": "primitive-lean-kaggle-handoff-v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "repository": args.repository,
        "source_commit": args.source_ref,
        "github_actions": {
            "run_id": args.run_id or None,
            "run_attempt": args.run_attempt or None,
            "run_url": (args.server_url.rstrip("/") + "/" + args.repository
                        + "/actions/runs/" + args.run_id)
                       if args.server_url and args.repository and args.run_id else None,
        },
        "notebooks": files,
        "claims": {
            "notebook_cells_have_saved_outputs": False,
            "notebook_source_is_commit_pinned": True,
            "github_writeback": False,
            "kaggle_competition_submission": False,
        },
    }
    (out / "handoff.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", "utf-8"
    )
    (out / "README.txt").write_text(
        "primitive-lean Kaggle handoff\n\n"
        f"GitHub source commit: {args.source_ref}\n"
        f"Actions run: {manifest['github_actions']['run_url'] or 'local package build'}\n\n"
        "Import primitive_lean_proof_check.ipynb to run source verification, Lean setup, "
        "proof checks, and axiom audit in one cell. It is configured to fetch this exact "
        "private GitHub commit using Kaggle Secrets key GITHUB_TOKEN.\n"
        "primitive_lean_setup_one_cell.ipynb checks sources and prepares Lean without "
        "running proofs. Both notebooks are clean, self-contained, and leave the Kaggle "
        "result ZIP at /kaggle/working/primitive_lean_result.zip.\n\n"
        "The notebook only reads GitHub source. It does not write to GitHub or submit "
        "anything to the competition. Keep handoff.json with the notebook so a returned "
        "result ZIP can be checked against source_commit.\n",
        "utf-8",
    )
    print(json.dumps(manifest, ensure_ascii=False, indent=2))


def os_environ(name, default=""):
    import os
    return os.environ.get(name, default)


if __name__ == "__main__":
    main()
