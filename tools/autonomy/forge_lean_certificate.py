"""Read-only semantic-ledger -> Lean word-closure certificate.

The ledger is data, not Lean code. Revalidate the entire history, independently
replay all finite input tables, then emit only bounded numeral lists and a fixed
proof template. Reuse the existing OperatorWordObservations.inc unchanged.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from tools.autonomy import generic_forge as gf
from tools.autonomy import semantic_forge as sf

ROOT = Path(__file__).resolve().parents[2]
WORDS = ROOT / "linear_input/lean_check/OperatorWordObservations.inc"
OPS = ("reverse", "rotate_left", "add_one", "delta_xor", "clip_top", "swap_pairs")
CONSTANTS = (0, 85, 170, 255)
CORE = r"""
namespace ForgeLeanCertificate
open LinearInputOperatorWords

abbrev Signal := Fin 256
abbrev Constant (x : Signal) : Prop :=
  x = 0 ∨ x = 85 ∨ x = 170 ∨ x = 255

inductive Primitive where
  | reverse | rotate_left | add_one | delta_xor | clip_top | swap_pairs

def tableStep (xs : List Signal) (x : Signal) : Signal :=
  (xs[x.val]?).getD 0
"""
PROOFS = r"""
theorem old_preserves (i : Primitive) (x : Signal) (hx : Constant x) :
    Constant (oldStep i x) := by
  cases i <;> rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem old_word_constant (word : List Primitive) (x : Signal) (hx : Constant x) :
    Constant (run oldStep word x) := by
  induction word generalizing x with
  | nil => exact hx
  | cons i rest ih =>
      change Constant (run oldStep rest (oldStep i x))
      exact ih (oldStep i x) (old_preserves i x hx)

theorem not_old_word (T : Signal → Signal) (x : Signal) (hx : Constant x)
    (hT : ¬ Constant (T x)) (word : List Primitive) :
    T ≠ run oldStep word := by
  intro h
  apply hT
  rw [h]
  exact old_word_constant word x hx

-- This uses the original project theorem run_generated, rather than just
-- asserting the same property of a new word interpreter.
theorem not_macro_word {κ : Type*} (T : Signal → Signal) (x : Signal)
    (hx : Constant x) (hT : ¬ Constant (T x))
    (code : κ → List Primitive) (word : List κ) :
    T ≠ run (generated oldStep code) word := by
  intro h
  apply (not_old_word T x hx hT (compile code word))
  funext y
  exact (congrFun h y).trans (run_generated oldStep code word y)
"""


def require(ok, message):
    if not ok:
        raise ValueError(message)


def table(a, b):
    values = []
    for x in range(256):
        y, z = a(x), b(x)
        require(type(y) is int and 0 <= y < 256 and y == z,
                "finite interpreter disagreement")
        values.append(y)
    return values


def literal(values):
    require(len(values) == 256 and all(type(v) is int and 0 <= v < 256 for v in values),
            "invalid finite table")
    return "[" + ", ".join(map(str, values)) + "]"


def generate(state_path: Path, output: Path):
    require(tuple(gf.DOMAINS["signal4"]) == OPS and gf.DOMAIN_SIZE["signal4"] == 256,
            "primitive vocabulary drift: review required")
    state = sf.validate_state(sf.read(state_path))
    require(bool(state["receipts"]), "no certified semantic receipt to formalize")
    source = WORDS.read_text(encoding="utf-8")
    parts = ["import Mathlib\nset_option maxRecDepth 4096\n"
             "set_option maxHeartbeats 4000000\n", source, CORE,
             "\ndef oldStep : Primitive → Signal → Signal\n"]
    names = ["old_preserves", "old_word_constant", "not_old_word", "not_macro_word"]
    for op in OPS:
        values = table(lambda x: gf.reference_primitive("signal4", op, x),
                       lambda x: gf.independent_primitive("signal4", op, x))
        require(all(values[x] in CONSTANTS for x in CONSTANTS), "old closure invariant failed")
        parts.append(f"  | .{op} => tableStep {literal(values)}\n")
    parts.append(PROOFS)
    rows = []
    for i, row in enumerate(state["receipts"]):
        recipe = row["recipe"]
        values = table(lambda x: sf.apply_recipe(recipe, x, sf.reference_step),
                       lambda x: sf.apply_recipe(recipe, x, sf.independent_step))
        fingerprint = hashlib.sha256(bytes(values)).hexdigest()
        require(fingerprint == row["observation"]["behavior_sha256"], "receipt behavior drift")
        witness = row["observation"]["constant_counterexample"]
        x, y = witness["input"], witness["output"]
        require(type(x) is int and x in CONSTANTS and type(y) is int
                and values[x] == y and y not in CONSTANTS, "bad separation witness")
        prefix = f"certified_{i}"
        parts.append(f"""
def semantic_{i} : Signal → Signal := tableStep {literal(values)}

theorem {prefix}_value : semantic_{i} {x} = {y} := by decide

theorem {prefix}_witness : Constant ({x} : Signal) ∧
    ¬ Constant (semantic_{i} {x}) := by decide

theorem {prefix}_not_old (word : List Primitive) :
    semantic_{i} ≠ run oldStep word :=
  not_old_word semantic_{i} {x} {prefix}_witness.1 {prefix}_witness.2 word

theorem {prefix}_not_macros {{κ : Type*}} (code : κ → List Primitive) (word : List κ) :
    semantic_{i} ≠ run (generated oldStep code) word :=
  not_macro_word semantic_{i} {x} {prefix}_witness.1 {prefix}_witness.2 code word
""")
        names.extend(prefix + suffix for suffix in ("_value", "_witness", "_not_old", "_not_macros"))
        rows.append({"lean_name": f"semantic_{i}", "receipt_id": row["id"],
                     "chain_sha256": row["chain_sha256"], "source_head": row["head_sha"],
                     "behavior_sha256": fingerprint, "input": x, "output": y})
    parts.append("\nend ForgeLeanCertificate\n")
    parts.extend(f"#print axioms ForgeLeanCertificate.{name}\n" for name in names)
    output.mkdir(parents=True, exist_ok=True)
    (output / "Certificate.lean").write_text("".join(parts), encoding="utf-8")
    report = {"ledger_sha256": hashlib.sha256(state_path.read_bytes()).hexdigest(),
              "word_source_sha256": hashlib.sha256(WORDS.read_bytes()).hexdigest(),
              "receipt_count": len(rows), "theorem_count": len(names),
              "theorems": names, "receipts": rows,
              "status": "GENERATED_PENDING_KERNEL_VERIFICATION"}
    (output / "mapping.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                                         encoding="utf-8")


def audit(output: Path):
    report = json.loads((output / "mapping.json").read_text(encoding="utf-8"))
    import re
    log = (output / "lean.log").read_text(encoding="utf-8")
    require(not re.search(r"\b(error:|warning:|sorryAx)\b", log), "Lean diagnostic")
    deps = re.findall(r"depends on axioms:\s*\[([^]]*)\]", log)
    none = log.count("does not depend on any axioms")
    require(len(deps) + none == report["theorem_count"], "missing theorem axiom audit")
    allowed = {"propext", "Quot.sound", "Classical.choice"}
    for group in deps:
        require(set(filter(None, (x.strip() for x in group.split(",")))) <= allowed,
                "unexpected theorem axiom")
    report["status"] = "KERNEL_AND_AXIOM_AUDIT_PASSED"
    (output / "mapping.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                                         encoding="utf-8")
    print(report["status"], report["receipt_count"], "receipts", report["theorem_count"], "theorems")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", action="store_true")
    args = parser.parse_args()
    if args.audit:
        audit(args.output)
    else:
        require(args.state is not None, "state input required")
        generate(args.state, args.output)


if __name__ == "__main__":
    main()
