"""Verify the #99/#100 interface and the fixed-boundary curvature witness.

Called through tools/verify.py --elastica-boundary-only.  The existing operator
fragments and the #99 fragment are assembled without editing or duplicating
their repository files.  All Lean checks use the pinned toolchain and --trust=0.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
PROOFS = ROOT / "linear_input" / "lean_check"
PR99 = "abc94a7d313efc194fe43a6bfc1ed955fa36f17b"
PR100 = "a721c47b6cfa18ef101fd5dc563881c3c9654af7"
MATHLIB = "2ddf59c8f14245864e6c0ed227a2dab76b9efea2"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

NEW_MODULES = (
    ("ElasticaUnifiedOperatorAdapter", "ElasticaUnifiedOperatorAdapter"),
    ("ElasticaFixedBoundaryWitness", "FixedBoundaryWitness"),
    ("ElasticaCurveDistinct", "FixedBoundaryCurveDistinct"),
    ("ElasticaFixedBoundaryEnergy", "FixedBoundaryExactEnergy"),
)


def command(args, cwd=ROOT, env=None):
    print("+", " ".join(map(str, args)), flush=True)
    result = subprocess.run(args, cwd=cwd, env=env, check=False,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, encoding="utf-8")
    if result.returncode:
        print(result.stdout, end="", flush=True)
        raise subprocess.CalledProcessError(result.returncode, args)
    return result


def git_bytes(commit, path):
    args = ["git", "show", f"{commit}:{path}"]
    print("+", " ".join(args), flush=True)
    result = subprocess.run(args, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, check=False)
    if result.returncode:
        print(result.stderr.decode("utf-8", errors="replace"), flush=True)
        raise subprocess.CalledProcessError(result.returncode, args)
    return result.stdout


def git_file(commit, path):
    return git_bytes(commit, path).decode("utf-8")


def check_sources():
    from check_lean_migration import audit as audit_migration, accepts_current_hash

    migration = audit_migration(ROOT)
    if not migration['passed']:
        raise RuntimeError('Invalid toolchain migration: ' + '; '.join(migration['errors']))
    # #99 and #100 share these exact original sources.  Check bytes rather than
    # assuming a shared filename implies a shared definition. A verified
    # migration records the old Git bytes separately from the current proof.
    sources = (
        (PR99, "lean/Elastica/Geometry.lean"),
        (PR99, "linear_input/lean_check/OperatorWordObservations.inc"),
        (PR99, "linear_input/lean_check/OperatorVocabularyRefinement.inc"),
        (PR100, "lean/Research/ElasticaObservationQuotient.lean"),
    )
    for commit, path in sources:
        original = git_bytes(commit, path)
        current = (ROOT / path).read_bytes()
        original_sha, current_sha = hashlib.sha256(original).hexdigest(), hashlib.sha256(current).hexdigest()
        if not accepts_current_hash(migration, path, original_sha, current_sha):
            raise RuntimeError(f"source differs from pinned original without a verified migration: {path}")
        print("source provenance", json.dumps(dict(path=path, original_commit=commit,
            original_sha256=original_sha, current_sha256=current_sha,
            byte_identical=current == original,
            migration_verified=current != original), sort_keys=True), flush=True)
    if (LEAN / "lean-toolchain").read_text(encoding="utf-8").strip() != \
            "leanprover/lean4:v4.36.0-rc2":
        raise RuntimeError("unexpected Lean toolchain pin")
    version = command(["lean", "--version"], cwd=LEAN).stdout.strip()
    if "version 4.36.0-rc2" not in version:
        raise RuntimeError(f"unexpected Lean version: {version}")
    manifest = json.loads((LEAN / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        actual = command(["git", "-C", str(LEAN / ".lake/packages" / package["name"]),
                          "rev-parse", "HEAD"]).stdout.strip()
        if actual != package["rev"]:
            raise RuntimeError(f"dependency revision mismatch: {package['name']}")
        if package["name"] == "mathlib" and actual != MATHLIB:
            raise RuntimeError(f"unexpected mathlib revision: {actual}")
    print("PR #99", PR99, "PR #100", PR100, "Lean", version,
          "mathlib", MATHLIB, flush=True)


def declared_names():
    names = []
    for module, namespace in NEW_MODULES:
        text = (PROOFS / f"{module}.lean").read_text(encoding="utf-8")
        if re.search(r"\b(?:sorry|admit)\b", text):
            raise RuntimeError(f"unaccepted proof placeholder in {module}")
        declarations = re.findall(r"^(?:theorem|def|abbrev)\s+(\w+)",
                                  text, re.MULTILINE)
        if not declarations:
            raise RuntimeError(f"no declarations found in {module}")
        names.extend(f"{namespace}.{name}" for name in declarations)
    if len(names) != len(set(names)):
        raise RuntimeError("duplicate declarations in axiom audit")
    return names


def lean_command(args, env, root):
    result = command(["lean", "--trust=0", "-R", str(root), *map(str, args)],
                     cwd=LEAN, env=env)
    print(result.stdout, end="", flush=True)
    if "sorryAx" in result.stdout or re.search(r"\b(?:error|warning):", result.stdout):
        raise RuntimeError("Lean emitted a warning, error, or sorryAx")
    return result.stdout


def inside_lake():
    check_sources()
    names = declared_names()
    with tempfile.TemporaryDirectory(prefix="elastica-fixed-boundary-") as tmp:
        tmpdir = Path(tmp)
        (tmpdir / "Research").mkdir()
        env = os.environ.copy()
        env["LEAN_PATH"] = tmp + os.pathsep + env.get("LEAN_PATH", "")
        # Compile the actual #99 fragments from the pinned source and the
        # actual #100 module.  No original declaration is rewritten.
        pieces = [
            "import Mathlib\nimport Elastica.Geometry\n",
            (PROOFS / "OperatorWordObservations.inc").read_text(encoding="utf-8"),
            (PROOFS / "OperatorVocabularyRefinement.inc").read_text(encoding="utf-8"),
            git_file(PR99, "linear_input/lean_check/ElasticaOperatorBridge.inc"),
        ]
        theory = tmpdir / "ElasticaOperatorTheory.lean"
        theory.write_text("\n".join(pieces), encoding="utf-8")
        lean_command(["-o", tmpdir / "ElasticaOperatorTheory.olean", theory], env, tmpdir)
        original100 = tmpdir / "Research/ElasticaObservationQuotient.lean"
        shutil.copyfile(LEAN / "Research/ElasticaObservationQuotient.lean", original100)
        lean_command(["-o", tmpdir / "Research/ElasticaObservationQuotient.olean",
                      original100], env, tmpdir)
        for module, _ in NEW_MODULES:
            source = tmpdir / f"{module}.lean"
            shutil.copyfile(PROOFS / f"{module}.lean", source)
            lean_command(["-o", tmpdir / f"{module}.olean", source], env, tmpdir)
        dependencies = tmpdir / "ElasticaDependencyAudit.lean"
        shutil.copyfile(PROOFS / "ElasticaDependencyAudit.lean", dependencies)
        lean_command([dependencies], env, tmpdir)

        audit = tmpdir / "ElasticaAxiomAudit.lean"
        audit.write_text(
            "\n".join(f"import {module}" for module, _ in NEW_MODULES) + "\n" +
            "\n".join(f"#print axioms {name}" for name in names) + "\n",
            encoding="utf-8",
        )
        output = lean_command([audit], env, tmpdir)
        found = {}
        pattern = (r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|"
                   r"does not depend on any axioms)")
        for match in re.finditer(pattern, output, re.MULTILINE):
            found[match.group(1)] = {
                x.strip() for x in (match.group(2) or "").split(",") if x.strip()
            }
        if set(found) != set(names):
            raise RuntimeError(f"incomplete axiom audit: {set(names) - set(found)}")
        for name, axioms in found.items():
            if not axioms <= ALLOWED_AXIOMS:
                raise RuntimeError(f"unexpected axioms for {name}: {axioms}")
        print(f"PASS: {len(found)} declarations, permitted axioms only", flush=True)
    return 0


def main(argv=None):
    args = sys.argv[1:] if argv is None else argv
    if args == ["--inside-lake"]:
        return inside_lake()
    if args:
        raise ValueError(f"unexpected arguments: {args}")
    tests = command([sys.executable, "-m", "unittest", "discover", "-s", "tests",
                     "-p", "test_elastica_fixed_boundary.py", "-v"])
    print(tests.stdout, end="", flush=True)
    build = command(["lake", "build", "Elastica.Geometry"], cwd=LEAN)
    print(build.stdout, end="", flush=True)
    result = command(["lake", "env", sys.executable, __file__, "--inside-lake"], cwd=LEAN)
    print(result.stdout, end="", flush=True)
    print("PASS: independent checks, pinned sources, Lean proofs and axiom audit")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
