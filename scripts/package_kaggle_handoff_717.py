"""Build the 717-theorem Kaggle handoff from immutable source commit 185a1713..."""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "Sumuji-zkdwn/primitive-lean"
SOURCE_COMMIT = "185a1713f2fca219e5f9fb1c5aa11955925cb97f"
LEGACY_SOURCE_COMMIT = "5d23c590398680aa7a67919a54fc2bdd915614b4"
UPDATED_BASE_PATHS = {
    "tools/verify.py",
    "tools/verify_main_result.py",
    "linear_input/lean_check/README.md",
    "原始の形式化.md",
    "検証と再実行.md",
}
OVERLAY_PATHS = [
    "tools/verify.py",
    "tools/verify_main_result.py",
    "linear_input/lean_check/README.md",
    "原始の形式化.md",
    "検証と再実行.md",
    "tools/proof_only.py",
    "linear_input/lean_check/BranchFibers.inc",
    "linear_input/lean_check/BranchForgetting.inc",
    "linear_input/lean_check/F0Counting.inc",
    "linear_input/lean_check/F0MergeChains.inc",
    "linear_input/lean_check/F0Retractions.inc",
    "linear_input/lean_check/FiniteBayes.inc",
    "linear_input/lean_check/FourBayes.inc",
    "linear_input/lean_check/HistorySignature.inc",
    "linear_input/lean_check/VariablePairObservations.inc",
]
PROOF_TREE_PATHS = [
    "lean/Elastica",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/lake-manifest.json",
    "linear_input/verify_lean.py",
    "linear_input/lean_check",
    "tools/verify.py",
    "tools/verify_main_result.py",
    "tools/proof_only.py",
]
ADDED_PROOFS = [p for p in OVERLAY_PATHS if p.endswith(".inc")]


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


def sha_file(path):
    return sha_bytes(Path(path).read_bytes())


def git_bytes(ref, path):
    return subprocess.check_output(["git", "show", "{}:{}".format(ref, path)], cwd=ROOT)


def verify_source_relation(source_ref, head):
    if source_ref != SOURCE_COMMIT:
        raise ValueError("This handoff is pinned to {}".format(SOURCE_COMMIT))
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", source_ref, head], cwd=ROOT
    )
    if ancestor.returncode != 0:
        raise ValueError("The proof source must be an ancestor of the validation commit")
    diff = subprocess.run(
        ["git", "diff", "--quiet", source_ref, head, "--", *PROOF_TREE_PATHS], cwd=ROOT
    )
    if diff.returncode != 0:
        raise ValueError("Proof inputs differ between the pinned source and validation commit")


def source_snapshot(source_ref):
    inventory = json.loads(git_bytes(source_ref, "docs/import/archive_inventory.json"))
    rows = [row for row in inventory["files"] if row["imported"]]
    if len(rows) != 116:
        raise ValueError("Unexpected imported-file baseline: {}".format(len(rows)))
    source_hashes = {}
    for row in rows:
        path = row["path"]
        digest = sha_bytes(git_bytes(source_ref, path))
        if path not in UPDATED_BASE_PATHS and digest != row["sha256"]:
            raise ValueError("Archive baseline no longer matches {}".format(path))
        source_hashes[path] = digest
    for path in OVERLAY_PATHS:
        source_hashes[path] = sha_bytes(git_bytes(source_ref, path))
    if len(source_hashes) != 126:
        raise ValueError("Expected 126 source files, found {}".format(len(source_hashes)))
    return inventory, source_hashes


def dependency_snapshot(source_ref):
    toolchain = git_bytes(source_ref, "lean/lean-toolchain").decode("utf-8").strip()
    lake_manifest = json.loads(git_bytes(source_ref, "lean/lake-manifest.json"))
    dependencies = [{"name": row["name"], "revision": row["rev"]}
                    for row in lake_manifest["packages"]]
    return toolchain, dependencies


def validate_ci_proof_results(source_ref, expected_source_hashes, dependencies):
    proof_path = ROOT / "verification/proof-only.json"
    main_path = ROOT / "verification/main-result.json"
    if not proof_path.is_file() or not main_path.is_file():
        raise ValueError("Fresh proof-only and main-result reports are required")
    proof = json.loads(proof_path.read_text("utf-8"))
    main = json.loads(main_path.read_text("utf-8"))
    if proof.get("passed") is not True or proof.get("theorem_count") != 717 or proof.get("declaration_count") != 836:
        raise ValueError("GitHub Actions proof-only report does not show 717/836 passing")
    stages = proof.get("stages", [])
    if len(stages) != 2 or any(
        stage.get("passed") is not True or stage.get("run", {}).get("exit_code") != 0
        or stage.get("run", {}).get("warnings") for stage in stages
    ):
        raise ValueError("Both fresh Lean proof stages must pass without warnings")
    if main.get("passed") is not True or main.get("total_theorem_count") != 717 or main.get("total_declaration_count") != 836:
        raise ValueError("Joint proof and axiom report does not show 717/836")
    if main.get("joint_axiom_audit") is not True or main.get("baseline_axioms_match") is not True:
        raise ValueError("The full declaration axiom audit did not pass")
    if len(main.get("all_declarations", [])) != 836 or len(main.get("axioms", {})) != 836:
        raise ValueError("The proof report does not audit all 836 declarations")
    if main.get("errors") or main.get("unexpected") or main.get("warnings") or main.get("forbidden_tokens"):
        raise ValueError("Proof report contains errors, warnings, or unexpected axioms")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if any(not set(axioms).issubset(allowed) for axioms in main["axioms"].values()):
        raise ValueError("Proof report contains an unapproved axiom")
    dependency_rows = main.get("dependencies_after_compile", [])
    observed = [{"name": row["name"], "revision": row["actual"]}
                for row in dependency_rows if row.get("match")]
    if observed != dependencies or len(dependency_rows) != len(dependencies):
        raise ValueError("Lean dependency revisions differ from the pinned manifest")
    for path in ADDED_PROOFS + ["tools/verify.py", "tools/verify_main_result.py"]:
        if main.get("source_hashes", {}).get(path) != expected_source_hashes[path]:
            raise ValueError("Lean report source hash mismatch: {}".format(path))
    return proof, main


def read_notebook(path, source_ref, setup, proofs, source_mode):
    notebook = json.loads(path.read_text("utf-8"))
    if notebook.get("nbformat") != 4:
        raise ValueError("Not an nbformat 4 notebook: {}".format(path.name))
    snapshot = notebook.get("metadata", {}).get("primitive_lean", {})
    if snapshot.get("source_commit") != source_ref:
        raise ValueError("Notebook source commit mismatch: {}".format(path.name))
    if snapshot.get("expected_theorem_count") != 717 or snapshot.get("expected_declaration_count") != 836:
        raise ValueError("Notebook expected counts mismatch: {}".format(path.name))
    code = [cell for cell in notebook.get("cells", []) if cell.get("cell_type") == "code"]
    if len(code) != 1:
        raise ValueError("Expected one self-contained executable cell: {}".format(path.name))
    cell = code[0]
    if cell.get("execution_count") is not None or cell.get("outputs") != []:
        raise ValueError("Notebook contains saved execution state: {}".format(path.name))
    source = "".join(cell.get("source", []))
    compile(source, path.name, "exec")
    for marker in [
        'SOURCE_MODE = "{}"'.format(source_mode),
        "RUN_SETUP = {}".format(setup),
        "RUN_PROOFS = {}".format(proofs),
        'GITHUB_SECRET_LABEL = "GITHUB_TOKEN"',
        "primitive_lean_result.zip",
        source_ref,
    ]:
        if marker not in source:
            raise ValueError("Notebook is missing expected marker {}".format(marker))
    for forbidden in ("ghp_", "github_pat_", "KAGGLE_API_TOKEN", "kaggle kernels submit"):
        if forbidden in source:
            raise ValueError("Unexpected credential or competition submission marker")
    return notebook


def os_environ(name, default=""):
    return os.environ.get(name, default)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-ref", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--source-mode", choices=("auto", "path", "github"), default="auto")
    parser.add_argument("--run-id", default=os_environ("GITHUB_RUN_ID"))
    parser.add_argument("--run-attempt", default=os_environ("GITHUB_RUN_ATTEMPT"))
    parser.add_argument("--server-url", default=os_environ("GITHUB_SERVER_URL"))
    parser.add_argument("--repository", default=os_environ("GITHUB_REPOSITORY", REPOSITORY))
    args = parser.parse_args(argv)
    if len(args.source_ref) != 40 or any(c not in "0123456789abcdef" for c in args.source_ref):
        parser.error("source-ref must be a full lowercase commit SHA")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    try:
        verify_source_relation(args.source_ref, head)
        inventory, source_hashes = source_snapshot(args.source_ref)
        toolchain, dependencies = dependency_snapshot(args.source_ref)
        proof_report, main_report = validate_ci_proof_results(args.source_ref, source_hashes, dependencies)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        parser.error(str(error))

    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        parser.error("output-dir must be empty: {}".format(out))
    setup_path = out / "primitive_lean_717_setup_one_cell.ipynb"
    proof_path = out / "primitive_lean_717_proof_check.ipynb"
    common = [
        sys.executable, "-X", "utf8", str(ROOT / "scripts/build_kaggle_notebook_717.py"),
        "--source-ref", args.source_ref, "--source-mode", args.source_mode,
    ]
    subprocess.run(common + ["--setup-one-cell", "--output", str(setup_path)], cwd=ROOT, check=True)
    subprocess.run(common + ["--proof-check-one-cell", "--output", str(proof_path)], cwd=ROOT, check=True)
    read_notebook(setup_path, args.source_ref, "True", "False", args.source_mode)
    read_notebook(proof_path, args.source_ref, "True", "True", args.source_mode)

    auditor_path = out / "audit_kaggle_result_717.py"
    auditor_path.write_bytes((ROOT / "scripts/audit_kaggle_result_717.py").read_bytes())
    notebooks = {
        path.name: {"bytes": path.stat().st_size, "sha256": sha_file(path)}
        for path in (setup_path, proof_path)
    }
    run_url = (args.server_url.rstrip("/") + "/" + args.repository + "/actions/runs/" + args.run_id
               if args.server_url and args.repository and args.run_id else None)
    manifest = {
        "schema": "primitive-lean-kaggle-handoff-717-v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "repository": args.repository,
        "proof_source_commit": args.source_ref,
        "validation_commit": head,
        "github_actions": {"run_id": args.run_id or None, "run_attempt": args.run_attempt or None,
                           "run_url": run_url},
        "proof_counts": {"theorems": 717, "declarations": 836},
        "proof_check": {
            "passed": True, "stages": proof_report["stages"],
            "fresh_joint_axiom_audit": True, "axioms_audited": 836,
            "allowed_axioms": sorted({"propext", "Classical.choice", "Quot.sound"}),
            "main_result_sha256": sha_file(ROOT / "verification/main-result.json"),
        },
        "lean": {"toolchain": toolchain, "dependencies": dependencies},
        "source_snapshot": {
            "archive_sha256": inventory["archive_sha256"],
            "verified_source_files": len(source_hashes),
            "source_sha256": source_hashes,
            "overlay_paths": sorted(OVERLAY_PATHS),
            "added_proof_sources": ADDED_PROOFS,
        },
        "notebooks": notebooks,
        "result_auditor": {"path": auditor_path.name, "bytes": auditor_path.stat().st_size,
                           "sha256": sha_file(auditor_path)},
        "prior_validation": {
            "source_commit": LEGACY_SOURCE_COMMIT,
            "theorems": 494, "declarations": 538,
            "github_actions_run": "40703848720",
            "kaggle_notebook": "sumuji/primitive-lean-proof-check",
            "kaggle_saved_version_id": 363335255,
            "result_zip_sha256": "becc42a804a5915466ae68514853848d2ba48fd7a9d436a05956e96685e2bc8c",
            "status": "previously passed; retained as a separate record; not rerun here",
        },
        "claims": {
            "notebook_source_is_commit_pinned": True,
            "github_writeback": False,
            "kaggle_competition_submission": False,
            "kaggle_saved_version_execution": "not yet recorded",
        },
    }
    (out / "handoff_717.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", "utf-8")
    (out / "README_717.txt").write_text(
        "primitive-lean 717-theorem Kaggle handoff\n\n"
        "Proof source commit: {}\nValidation commit: {}\nActions run: {}\n"
        "Counts: 717 theorems / 836 declarations.\n"
        "Lean toolchain: {}. Pinned dependencies: {}.\n"
        "Attach the existing archive ZIP used by the 494/538 saved Version (dataset version 21217503), "
        "or set SOURCE_MODE='github' and provide GITHUB_TOKEN via Kaggle Secrets.\n"
        "Run primitive_lean_717_proof_check.ipynb with Internet enabled. The Notebook does not submit to a competition or write to GitHub.\n"
        "Audit the downloaded output with: python -X utf8 audit_kaggle_result_717.py "
        "primitive_lean_result.zip --expected-source {} --handoff handoff_717.json\n"
        .format(args.source_ref, head, run_url or "local build", toolchain, len(dependencies), args.source_ref),
        "utf-8",
    )
    print(json.dumps(manifest, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
