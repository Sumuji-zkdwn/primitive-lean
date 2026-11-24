"""Proof-gated search beyond the actual semantic receipt alphabet.

Read-only bounded experiment. Prove a disjunctive invariant for arbitrary
words before running a reviewed finite candidate grammar. Only the selected
candidate is sent back to the Lean kernel; no production ledger writes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

from tools.autonomy import generic_forge as gf, semantic_forge as sf
from tools.autonomy import forge_lean_certificate as cert

RANK_CORE = r"""
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
namespace ForgeLeanCertificate
open LinearInputOperatorWords

def Small (T : Signal → Signal) : Prop :=
  ∃ g : Fin 4 → Signal, ∀ x : Signal, ∃ j : Fin 4, T x = g j

def Good (T : Signal → Signal) : Prop :=
  (∀ x, Constant x → Constant (T x)) ∨ Small T

theorem good_comp {f g : Signal → Signal} (hf : Good f) (hg : Good g) :
    Good (fun x => g (f x)) := by
  rcases hf with hf | ⟨a, ha⟩
  · rcases hg with hg | ⟨b, hb⟩
    · exact Or.inl (fun x hx => hg _ (hf x hx))
    · exact Or.inr ⟨b, fun x => hb (f x)⟩
  · refine Or.inr ⟨fun j => g (a j), ?_⟩
    intro x
    obtain ⟨j, hj⟩ := ha x
    exact ⟨j, congrArg g hj⟩

theorem good_word {ι : Type*} (step : ι → Signal → Signal)
    (hstep : ∀ i, Good (step i)) (word : List ι) :
    Good (run step word) := by
  induction word with
  | nil => exact Or.inl (fun _ hx => hx)
  | cons i rest ih =>
      change Good (fun x => run step rest (step i x))
      exact good_comp (hstep i) ih

theorem not_small_of_injective (T : Signal → Signal)
    (probe : Fin 5 → Signal)
    (hinj : Function.Injective (fun i => T (probe i))) :
    ¬ Small T := by
  classical
  rintro ⟨g, hg⟩
  let f : Fin 5 → Fin 4 := fun i => Classical.choose (hg (probe i))
  have hf : ∀ i, T (probe i) = g (f i) :=
    fun i => Classical.choose_spec (hg (probe i))
  have hi : Function.Injective f := by
    intro i j h
    apply hinj
    change T (probe i) = T (probe j)
    calc
      T (probe i) = g (f i) := hf i
      _ = g (f j) := congrArg g h
      _ = T (probe j) := (hf j).symm
  have hcard := Fintype.card_le_of_injective f hi
  norm_num at hcard
"""

def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def finite_function(name, n, values):
    require(0 < len(values) == n and all(type(x) is int and 0 <= x < 256 for x in values),
            "invalid finite function")
    # A reviewed fixed template with integer literals only.
    result = str(values[-1])
    for i in range(n - 2, -1, -1):
        result = f"if i = {i} then {values[i]} else {result}"
    return f"def {name} (i : Fin {n}) : Signal := {result}\n"


def append_proofs(out, code, names, report):
    with (out / "Certificate.lean").open("a", encoding="utf-8") as f:
        f.write(code + "\nend ForgeLeanCertificate\n")
        for name in names:
            f.write(f"#print axioms ForgeLeanCertificate.{name}\n")
    report["theorems"] += names
    report["theorem_count"] = len(report["theorems"])
    report["status"] = "GENERATED_PENDING_KERNEL_VERIFICATION"
    report["certificate_sha256"] = sha(out / "Certificate.lean")
    write(out / "mapping.json", report)


def prepare(state_path, out):
    cert.generate(state_path, out)
    state = sf.validate_state(sf.read(state_path))
    report = read(out / "mapping.json")
    code = [RANK_CORE]
    names = ["good_comp", "good_word", "not_small_of_injective"]
    for i, row in enumerate(state["receipts"]):
        recipe = row["recipe"]
        values = cert.table(lambda x: sf.apply_recipe(recipe, x, sf.reference_step),
                            lambda x: sf.apply_recipe(recipe, x, sf.independent_step))
        image = sorted(set(values))
        require(1 <= len(image) <= 4, "rank invariant invalid for admitted receipt")
        image += [image[-1]] * (4 - len(image))
        code.append(finite_function(f"range_{i}", 4, image))
        code.append(f"""
theorem semantic_{i}_small : Small semantic_{i} := by
  refine ⟨range_{i}, ?_⟩
  decide
""")
        names.append(f"semantic_{i}_small")
    n = len(state["receipts"])
    require(n > 0, "empty semantic alphabet")
    code.append(f"""
def admittedStep : Sum Primitive (Fin {n}) → Signal → Signal
  | .inl p => oldStep p
  | .inr i => match i.val with
""")
    for i in range(n):
        code.append(f"    | {i} => semantic_{i}\n")
    code.append(f"""    | _ => semantic_0

theorem admitted_good (i : Sum Primitive (Fin {n})) : Good (admittedStep i) := by
  cases i with
  | inl p => exact Or.inl (fun x hx => old_preserves p x hx)
  | inr i =>
    fin_cases i <;> first
""")
    for i in range(n):
        code.append(f"      | exact Or.inr semantic_{i}_small\n")
    code.append(f"""
theorem admitted_word_good (word : List (Sum Primitive (Fin {n}))) :
    Good (run admittedStep word) :=
  good_word admittedStep admitted_good word

theorem outside_admitted (T : Signal → Signal) (x : Signal)
    (hx : Constant x) (hT : ¬ Constant (T x)) (hbig : ¬ Small T)
    (word : List (Sum Primitive (Fin {n}))) :
    T ≠ run admittedStep word := by
  intro h
  have hg := admitted_word_good word
  rw [← h] at hg
  rcases hg with hp | hs
  · exact hT (hp x hx)
  · exact hbig hs

theorem outside_admitted_macros {{κ : Type*}} (T : Signal → Signal) (x : Signal)
    (hx : Constant x) (hT : ¬ Constant (T x)) (hbig : ¬ Small T)
    (code : κ → List (Sum Primitive (Fin {n}))) (word : List κ) :
    T ≠ run (generated admittedStep code) word := by
  intro h
  apply outside_admitted T x hx hT hbig (compile code word)
  funext y
  exact (congrFun h y).trans (run_generated admittedStep code word y)
""")
    names += ["admitted_good", "admitted_word_good", "outside_admitted",
              "outside_admitted_macros"]
    report["invariant"] = "CONSTANT_PRESERVING_OR_IMAGE_AT_MOST_FOUR"
    append_proofs(out, "".join(code), names, report)


def recipes():
    for order in ("max", "min"):
        for tie in ("first", "last"):
            yield ("rotate", order, tie, 0)
            for kind in ("mask", "overwrite"):
                for level in (1, 2, 3):
                    yield (kind, order, tie, level)


def reference(recipe, x):
    kind, order, tie, level = recipe
    vals = gf.digits("signal4", x)
    target = max(vals) if order == "max" else min(vals)
    indices = [i for i, v in enumerate(vals) if v == target]
    pos = indices[0] if tie == "first" else indices[-1]
    if kind == "rotate":
        out = vals[pos:] + vals[:pos]
    elif kind == "mask":
        out = [0] * 4
        out[pos] = level
    else:
        require(kind == "overwrite", "unknown candidate kind")
        out = vals.copy()
        out[pos] = level
    return gf.encoded("signal4", out)


def packed(recipe, x):
    kind, order, tie, level = recipe
    best, val = 0, x & 3
    for i in range(1, 4):
        v = (x >> (2 * i)) & 3
        if (v > val if order == "max" else v < val) or (v == val and tie == "last"):
            best, val = i, v
    shift = 2 * best
    if kind == "rotate":
        return ((x >> shift) | (x << (8 - shift))) & 255
    if kind == "mask":
        return level << shift
    require(kind == "overwrite", "unknown candidate kind")
    return (x & (255 ^ (3 << shift))) | (level << shift)


def check_pair(recipe, x):
    a, b = reference(recipe, x), packed(recipe, x)
    require(type(a) is int and 0 <= a < 256 and a == b, "candidate interpreter disagreement")
    return a


def search(state_path, base, out):
    report = read(base / "mapping.json")
    require(report["status"] == "KERNEL_AND_AXIOM_AUDIT_PASSED"
            and report.get("invariant") == "CONSTANT_PRESERVING_OR_IMAGE_AT_MOST_FOUR"
            and "admitted_word_good" in report["theorems"]
            and "outside_admitted" in report["theorems"]
            and report["ledger_sha256"] == sha(state_path)
            and report["certificate_sha256"] == sha(base / "Certificate.lean"),
            "proof-first gate: exact invariant certificate required")
    # Recheck the base log and every new theorem's axiom audit.
    cert.audit(base)
    rejected = {"constant_preserving": 0, "small_image": 0}
    candidates = []
    records = []
    for recipe in recipes():
        witness = next((x for x in cert.CONSTANTS
                        if check_pair(recipe, x) not in cert.CONSTANTS), None)
        if witness is None:
            rejected["constant_preserving"] += 1
            records.append({"recipe": recipe, "status": "NO_SEPARATION_BY_CONSTANT_TEST"})
            continue
        first = {}
        for x in range(256):
            y = check_pair(recipe, x)
            first.setdefault(y, x)
            if len(first) == 5:
                break
        if len(first) < 5:
            rejected["small_image"] += 1
            records.append({"recipe": recipe, "status": "NO_SEPARATION_BY_RANK_TEST",
                            "rank": len(first)})
            continue
        values = cert.table(lambda x: reference(recipe, x), lambda x: packed(recipe, x))
        rank = len(set(values))
        row = {"recipe": recipe, "status": "SEPARATION_CANDIDATE",
               "rank": rank, "constant_input": witness, "constant_output": values[witness],
               "probe_inputs": list(first.values()), "probe_outputs": list(first.keys()),
               "behavior_sha256": hashlib.sha256(bytes(values)).hexdigest()}
        records.append(row)
        candidates.append((row, values))
    require(len(records) == 28 and len(candidates) == 12
            and rejected == {"constant_preserving": 4, "small_image": 12},
            "reviewed finite grammar regression")
    chosen, values = min(candidates, key=lambda item: (-item[0]["rank"], item[0]["recipe"]))
    require(chosen["rank"] == 175, "expected maximum finite image rank drift")
    out.mkdir(parents=True, exist_ok=True)
    (out / "Certificate.lean").write_bytes((base / "Certificate.lean").read_bytes())
    x = chosen["constant_input"]
    n = report["receipt_count"]
    code = [r"""
namespace ForgeLeanCertificate
open LinearInputOperatorWords
""", f"def discovered : Signal → Signal := tableStep {cert.literal(values)}\n",
            finite_function("probes", 5, chosen["probe_inputs"]), f"""
theorem discovered_constant_witness :
    Constant ({x} : Signal) ∧ ¬ Constant (discovered {x}) := by decide

theorem discovered_injective_probes :
    Function.Injective (fun i : Fin 5 => discovered (probes i)) := by
  change ∀ i j : Fin 5, discovered (probes i) = discovered (probes j) → i = j
  decide

theorem discovered_not_small : ¬ Small discovered :=
  not_small_of_injective discovered probes discovered_injective_probes

theorem discovered_not_admitted (word : List (Sum Primitive (Fin {n}))) :
    discovered ≠ run admittedStep word :=
  outside_admitted discovered {x} discovered_constant_witness.1
    discovered_constant_witness.2 discovered_not_small word

theorem discovered_not_admitted_macros {{κ : Type*}}
    (code : κ → List (Sum Primitive (Fin {n}))) (word : List κ) :
    discovered ≠ run (generated admittedStep code) word :=
  outside_admitted_macros discovered {x} discovered_constant_witness.1
    discovered_constant_witness.2 discovered_not_small code word
"""]
    names = ["discovered_constant_witness", "discovered_injective_probes",
             "discovered_not_small", "discovered_not_admitted",
             "discovered_not_admitted_macros"]
    report["prior_certificate_sha256"] = report["certificate_sha256"]
    report["search"] = {"total": len(records), "not_certified_by_invariant": rejected,
                        "separation_candidates": len(candidates), "selected": chosen,
                        "all": records,
                        "scope": "OLD_PRIMITIVES_PLUS_ALL_PINNED_SEMANTIC_RECEIPTS"}
    append_proofs(out, "".join(code), names, report)
    print("SEARCH", len(records), "candidates,", rejected, "selected", chosen)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("stage", choices=("prepare", "search"))
    p.add_argument("--state", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--base", type=Path)
    args = p.parse_args()
    if args.stage == "prepare":
        prepare(args.state, args.output)
    else:
        require(args.base is not None, "verified base required")
        search(args.state, args.base, args.output)


if __name__ == "__main__":
    main()
