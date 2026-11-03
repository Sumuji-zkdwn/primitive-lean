#!/usr/bin/env python3
"""Conservative, deterministic operator-theorem growth for primitive-lean.

Only the explicit finite witness family below is generated. This is NOT
an AI theorem inventor, and a successful finite witness does not imply
a new general theorem. The driver never merges branches or edits main.

Usage:
    python tools/autonomy/grow.py self-test
    python tools/autonomy/grow.py prepare --root ./working --output-file "$GITHUB_OUTPUT"
    python tools/autonomy/grow.py seal --root ./working
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

TARGET_BRANCH = "autonomy/verified-operator-growth"
LEDGER_PATH = Path("docs/autonomy/ledger.json")
MANIFEST_PATH = Path("docs/integration/manifest.json")
REGISTRY_PATH = Path("tools/verify_main_result.py")
SCOPES_PATH = Path("tools/verify.py")
MAX_STATES = 8


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def candidates():
    """Finite, reproducible enumeration; stop when the search space is spent."""
    for n in range(3, MAX_STATES + 1):
        for a in range(n):
            for b in range(n):
                # The states 0 and 1 are initially both observed as 0.
                # The novel primitive must separate them after one action.
                if (a < 2) == (b < 2):
                    continue
                yield {"states": n, "image_of_zero": a, "image_of_one": b}


def select_candidate(ledger):
    seen = {(c["model"]["states"], c["model"]["image_of_zero"],
             c["model"]["image_of_one"]) for c in ledger["cycles"]}
    for entry in candidates():
        key = (entry["states"], entry["image_of_zero"], entry["image_of_one"])
        if key not in seen:
            return entry
    return None


def name_for(number):
    return f"AutonomyCycle{number:05d}"


def proof_source(number, model):
    n = model["states"]
    a, b = model["image_of_zero"], model["image_of_one"]
    ns = f"LinearInputAutoCycle{number:05d}"
    template = r'''/-!
Autonomously generated finite witness, cycle __ID__.

Initial states 0 and 1 have the same readout; the old action is
the identity. The generated additional operator separates them.
This is a finite counterexample certificate, not a new general law.
Generation is restricted to enumerated small finite models.
-/

noncomputable section
namespace __NS__

def observer (x : Fin __N__) : Fin 2 :=
  if x.val < 2 then 0 else 1

def oldStep : Unit → Fin __N__ → Fin __N__ :=
  fun _ x => x

def newStep (x : Fin __N__) : Fin __N__ :=
  if x = 0 then __A__ else if x = 1 then __B__ else x

theorem old_run_identity (word : List Unit) (x : Fin __N__) :
    LinearInputOperatorWords.run oldStep word x = x := by
  induction word with
  | nil => rfl
  | cons _ rest ih =>
      change LinearInputOperatorWords.run oldStep rest x = x
      exact ih

theorem old_indistinguishable :
    LinearInputOperatorWords.WordEq observer oldStep
      (0 : Fin __N__) (1 : Fin __N__) := by
  intro word
  rw [old_run_identity, old_run_identity]
  decide

theorem new_distinguishes :
    ¬ LinearInputOperatorWords.WordEq observer
      (LinearInputOperatorRefinement.sumStep oldStep
        (fun _ : Unit => newStep))
      (0 : Fin __N__) (1 : Fin __N__) := by
  intro h
  have hne : observer (newStep (0 : Fin __N__)) ≠
      observer (newStep (1 : Fin __N__)) := by decide
  have heq := h [Sum.inr ()]
  apply hne
  simpa [LinearInputOperatorWords.run,
    LinearInputOperatorRefinement.sumStep] using heq

theorem no_old_word_dictionary (code : Unit → List Unit) :
    ¬ (∀ x y : Fin __N__,
      LinearInputOperatorWords.WordEq observer
        (LinearInputOperatorWords.generated oldStep code) x y ↔
      LinearInputOperatorWords.WordEq observer
        (LinearInputOperatorRefinement.sumStep oldStep
          (fun _ : Unit => newStep)) x y) := by
  intro h
  have hg : LinearInputOperatorWords.WordEq observer
      (LinearInputOperatorWords.generated oldStep code)
      (0 : Fin __N__) (1 : Fin __N__) :=
    LinearInputOperatorWords.generated_no_new_distinctions
      observer oldStep code old_indistinguishable
  exact new_distinguishes ((h 0 1).mp hg)

theorem minimal_quotient_splits :
    ∃ q r : LinearInputOperatorWords.State observer
        (LinearInputOperatorRefinement.sumStep oldStep
          (fun _ : Unit => newStep)),
      q ≠ r ∧
        LinearInputOperatorRefinement.forget observer oldStep
          (fun _ : Unit => newStep) q =
        LinearInputOperatorRefinement.forget observer oldStep
          (fun _ : Unit => newStep) r := by
  exact LinearInputOperatorRefinement.strict_refinement_splits_quotient
    observer oldStep (fun _ : Unit => newStep)
      0 1 old_indistinguishable new_distinguishes

end __NS__
'''
    replacements = dict(
        __ID__=str(number), __NS__=ns, __N__=str(n),
        __A__=str(a), __B__=str(b),
    )
    for key, value in replacements.items():
        template = template.replace(key, value)
    return template


def read_json(path, fallback=None):
    if not path.exists():
        if fallback is None:
            raise FileNotFoundError(str(path))
        return fallback
    return json.loads(path.read_text(encoding="utf-8"))


def write_text(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def require_branch(root):
    proc = subprocess.run(
        ["git", "branch", "--show-current"],
        cwd=root, check=True, text=True, capture_output=True,
    )
    if proc.stdout.strip() != TARGET_BRANCH:
        raise RuntimeError("Refusing to modify branch " + repr(proc.stdout.strip()))
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()


def append_registration(root, name, namespace):
    path = root / REGISTRY_PATH
    content = path.read_text(encoding="utf-8")
    literal = f"    ('linear_input/lean_check/{name}.inc', '{namespace}'),\n"
    if literal.strip() in content:
        raise RuntimeError("Registry entry already exists")
    marker = "\n)\n\n\ndef sha("
    if content.count(marker) != 1:
        raise RuntimeError("Unexpected supplement registry layout")
    write_text(path, content.replace(marker, "\n" + literal.rstrip("\n") + marker, 1))

    path = root / SCOPES_PATH
    content = path.read_text(encoding="utf-8")
    marker = "\n    }\n    supplemental_groups = {"
    if content.count(marker) != 1:
        raise RuntimeError("Unexpected verification scope layout")
    scope = (
        f"        '{name}': 'Autonomously enumerated finite operator "
        "separation and strictly refined predictive quotient; "
        "five explicit Lean theorems',"
    )
    write_text(path, content.replace(marker, "\n" + scope + marker, 1))


def prepare(root, output_file=None):
    parent = require_branch(root)
    ledger_path = root / LEDGER_PATH
    ledger = read_json(ledger_path, {"schema_version": 1, "cycles": []})
    if ledger.get("schema_version") != 1:
        raise RuntimeError("Unsupported autonomy ledger schema")
    if any(c.get("status") != "verified" for c in ledger["cycles"]):
        raise RuntimeError("Unverified cycle in persistent ledger")
    model = select_candidate(ledger)
    if model is None:
        print("Candidate space exhausted; no new action is necessary.")
        if output_file:
            Path(output_file).open("a").write("created=false\n")
        return False

    number = len(ledger["cycles"]) + 1
    name = name_for(number)
    namespace = f"LinearInputAutoCycle{number:05d}"
    source = proof_source(number, model)
    rel = Path(f"linear_input/lean_check/{name}.inc")
    if (root / rel).exists():
        raise RuntimeError("Refusing to overwrite existing proof")
    if model["states"] < 3 or (model["image_of_zero"] < 2) == (
        model["image_of_one"] < 2
    ):
        raise RuntimeError("Candidate does not separate the observed fiber")
    manifest_path = root / MANIFEST_PATH
    manifest = read_json(manifest_path)
    if any(row["path"] == rel.as_posix() for row in manifest["files"]):
        raise RuntimeError("Manifest entry already exists")

    write_text(root / rel, source)
    append_registration(root, name, namespace)
    h = digest(source)
    manifest["files"].append({
        "path": rel.as_posix(),
        "sha256": h,
        "original_sha256": h,
        "source_pr": None,
        "source_commit": None,
        "source_path": rel.as_posix(),
        "role": "retained_source",
        "byte_identical": True,
        "permitted_adaptations": [],
        "provenance": {
            "generator": "tools/autonomy/grow.py",
            "cycle": number,
            "parent_commit": parent,
            "description": "Generated in CI; Git commit follows validation",
        },
    })
    manifest.setdefault("post_snapshot_additions", []).append({
        "date": datetime.now(timezone.utc).date().isoformat(),
        "path": rel.as_posix(),
        "source_commit": None,
        "note": "Generated finite witness; exact source SHA256 in files; "
                "commit only after successful Lean and source audit.",
    })
    write_text(manifest_path, json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
    ledger["cycles"].append({
        "cycle": number,
        "name": name,
        "status": "candidate",
        "model": model,
        "source": rel.as_posix(),
        "sha256": h,
        "parent_commit": parent,
        "claimed_theorems": 5,
        "claimed_definitions": 3,
        "created_utc": datetime.now(timezone.utc).isoformat(),
    })
    write_text(ledger_path, json.dumps(ledger, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"created": True, "cycle": number, "source": str(rel),
                      "sha256": h, "model": model}, ensure_ascii=False))
    if output_file:
        with Path(output_file).open("a", encoding="utf-8") as file:
            file.write("created=true\n")
    return True


def seal(root):
    require_branch(root)
    ledger_path = root / LEDGER_PATH
    ledger = read_json(ledger_path)
    if not ledger.get("cycles") or ledger["cycles"][-1]["status"] != "candidate":
        raise RuntimeError("No outstanding candidate to seal")
    row = ledger["cycles"][-1]
    actual = digest((root / row["source"]).read_text(encoding="utf-8"))
    if actual != row["sha256"]:
        raise RuntimeError("Proof bytes changed during validation")
    for path in ("verification/pr-integration.json", "verification/proof-only.json",
                 "verification/main-result.json", "verification/pr-source-audit.json"):
        report = read_json(root / path)
        if report.get("passed") is not True:
            raise RuntimeError(f"Verification was not successful: {path}")
    report = read_json(root / "verification/main-result.json")
    # Avoid accepting success from a prior run that did not audit the new file.
    sources = set(report.get("supplemental_sources", []))
    if row["source"] not in sources:
        raise RuntimeError("New source was not included in Lean verification")
    ledger["cycles"][-1].update({
        "status": "verified",
        "verified_utc": datetime.now(timezone.utc).isoformat(),
        "total_theorem_count": report.get("total_theorem_count"),
        "total_declaration_count": report.get("total_declaration_count"),
        "verification_kind": "fresh source audit, Lean trust=0 and axiom audit",
    })
    write_text(ledger_path, json.dumps(ledger, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"sealed": row["cycle"],
                      "theorems": report.get("total_theorem_count"),
                      "declarations": report.get("total_declaration_count")}))


def self_test():
    all_models = list(candidates())
    assert all_models and len(set((m["states"], m["image_of_zero"],
        m["image_of_one"]) for m in all_models)) == len(all_models)
    for m in all_models:
        assert (m["image_of_zero"] < 2) != (m["image_of_one"] < 2)
        src = proof_source(1, m)
        assert "sorry" not in src and "admit" not in src
        assert src.count("theorem ") == 5 and src.count("\ndef ") == 3
    ledger = {"cycles": [{"model": m, "status": "verified"} for m in all_models]}
    assert select_candidate(ledger) is None
    assert select_candidate({"cycles": []}) == all_models[0]
    assert len(all_models) == sum(4 * (n - 2) for n in range(3, MAX_STATES + 1))
    print(json.dumps({"self_test": "ok", "candidate_models": len(all_models),
                      "theorems_per_cycle": 5, "definitions_per_cycle": 3}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["self-test", "prepare", "seal"])
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output-file")
    args = parser.parse_args()
    if args.mode == "self-test":
        self_test()
    elif args.mode == "prepare":
        prepare(args.root.resolve(), args.output_file)
    else:
        seal(args.root.resolve())


if __name__ == "__main__":
    main()
