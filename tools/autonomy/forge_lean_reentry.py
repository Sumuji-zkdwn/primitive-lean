"""Third stage: admit a certified rank-175 map and search for a reversible extension.

The previous selected map is an actual letter of the expanded word alphabet.
All promotion/search is in an exact-source proof artifact, not a state write.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
from tools.autonomy import forge_lean_certificate as cert
from tools.autonomy import forge_lean_feedback as fb
from tools.autonomy import generic_forge as gf, semantic_forge as sf

CORE = r"""
namespace ForgeLeanCertificate
open LinearInputOperatorWords

def ReversibleGood (T : Signal → Signal) : Prop :=
  (∀ x, Constant x → Constant (T x)) ∨ ¬ Function.Injective T

theorem reversible_good_comp {f g : Signal → Signal}
    (hf : ReversibleGood f) (hg : ReversibleGood g) :
    ReversibleGood (fun x => g (f x)) := by
  rcases hf with hf | hf
  · rcases hg with hg | hg
    · exact Or.inl (fun x hx => hg _ (hf x hx))
    · apply Or.inr
      intro h
      have hfi : Function.Injective f := by
        intro a b hab
        exact h (congrArg g hab)
      have hfs : Function.Surjective f := by
        first
        | exact (Finite.injective_iff_surjective).mp hfi
        | exact (Finite.injective_iff_surjective f).mp hfi
        | exact Finite.surjective_of_injective hfi
        | exact (Finite.surjective_iff_injective).mpr hfi
        | exact (Finite.surjective_iff_injective f).mpr hfi
      apply hg
      intro a b hab
      obtain ⟨u, hu⟩ := hfs a
      obtain ⟨v, hv⟩ := hfs b
      have huv : g (f u) = g (f v) := by rw [hu, hv, hab]
      exact hu.symm.trans ((congrArg f (h huv)).trans hv)
  · apply Or.inr
    intro h
    apply hf
    intro a b hab
    exact h (congrArg g hab)

theorem reversible_good_word {ι : Type*} (step : ι → Signal → Signal)
    (hstep : ∀ i, ReversibleGood (step i)) (word : List ι) :
    ReversibleGood (run step word) := by
  induction word with
  | nil => exact Or.inl (fun _ hx => hx)
  | cons i rest ih =>
    change ReversibleGood (fun x => run step rest (step i x))
    exact reversible_good_comp (hstep i) ih

theorem noninjective_of_collision (T : Signal → Signal) (a b : Signal)
    (hne : a ≠ b) (he : T a = T b) : ¬ Function.Injective T :=
  fun h => hne (h he)
"""

def require(ok, message):
    if not ok:
        raise ValueError(message)


def gate(state_path, base, invariant, required):
    report = fb.read(base / "mapping.json")
    require(report["status"] == "KERNEL_AND_AXIOM_AUDIT_PASSED"
            and report["ledger_sha256"] == fb.sha(state_path)
            and report["certificate_sha256"] == fb.sha(base / "Certificate.lean")
            and report.get(invariant) is not None
            and all(name in report["theorems"] for name in required),
            "proof-first gate: exact audited prior stage required")
    cert.audit(base)
    return report


def collision(values):
    seen = {}
    for x, y in enumerate(values):
        if y in seen:
            return seen[y], x
        seen[y] = x
    raise ValueError("no collision in admitted map")


def collision_proof(name, values):
    a, b = collision(values)
    return f"""
theorem {name}_noninjective : ¬ Function.Injective {name} :=
  noninjective_of_collision {name} {a} {b} (by decide) (by decide)
"""


def prepare(state_path, base, out):
    report = gate(state_path, base, "search",
                  ("discovered_not_admitted", "discovered_not_admitted_macros"))
    require(report["search"]["scope"] == "OLD_PRIMITIVES_PLUS_ALL_PINNED_SEMANTIC_RECEIPTS",
            "unexpected discovery scope")
    chosen = report["search"]["selected"]
    recipe = tuple(chosen["recipe"])
    require(recipe in set(fb.recipes()), "unreviewed selected recipe")
    values = cert.table(lambda x: fb.reference(recipe, x), lambda x: fb.packed(recipe, x))
    behavior = hashlib.sha256(bytes(values)).hexdigest()
    require(behavior == chosen["behavior_sha256"] and len(set(values)) == chosen["rank"] == 175,
            "previous discovery replay mismatch")
    state = sf.validate_state(sf.read(state_path))
    n = len(state["receipts"])
    require(n == report["receipt_count"] > 0, "receipt count mismatch")
    out.mkdir(parents=True, exist_ok=True)
    (out / "Certificate.lean").write_bytes((base / "Certificate.lean").read_bytes())
    code = [CORE]
    names = ["reversible_good_comp", "reversible_good_word", "noninjective_of_collision"]
    for i, row in enumerate(state["receipts"]):
        r = row["recipe"]
        v = cert.table(lambda x: sf.apply_recipe(r, x, sf.reference_step),
                       lambda x: sf.apply_recipe(r, x, sf.independent_step))
        code.append(collision_proof(f"semantic_{i}", v))
        names.append(f"semantic_{i}_noninjective")
    code.append(collision_proof("discovered", values))
    names.append("discovered_noninjective")
    code.append(f"""
abbrev PromotedLetter := Sum (Sum Primitive (Fin {n})) Unit

def promotedStep : PromotedLetter → Signal → Signal
  | .inl i => admittedStep i
  | .inr _ => discovered

-- The previous discovery is now an actual available generator, not a comment.
theorem promoted_reentry (x : Signal) :
    run promotedStep [Sum.inr ()] x = discovered x := rfl

theorem promoted_good (i : PromotedLetter) :
    ReversibleGood (promotedStep i) := by
  cases i with
  | inr j => exact Or.inr discovered_noninjective
  | inl i =>
    cases i with
    | inl p => exact Or.inl (fun x hx => old_preserves p x hx)
    | inr j =>
      fin_cases j <;> first
""")
    for i in range(n):
        code.append(f"        | exact Or.inr semantic_{i}_noninjective\n")
    code.append(r"""
theorem promoted_word_good (word : List PromotedLetter) :
    ReversibleGood (run promotedStep word) :=
  reversible_good_word promotedStep promoted_good word

theorem reversible_outside_promoted (T : Signal → Signal) (x : Signal)
    (hx : Constant x) (hT : ¬ Constant (T x))
    (hinj : Function.Injective T) (word : List PromotedLetter) :
    T ≠ run promotedStep word := by
  intro h
  have hg := promoted_word_good word
  rw [← h] at hg
  rcases hg with hp | hn
  · exact hT (hp x hx)
  · exact hn hinj

theorem reversible_outside_promoted_macros {κ : Type*} (T : Signal → Signal)
    (x : Signal) (hx : Constant x) (hT : ¬ Constant (T x))
    (hinj : Function.Injective T)
    (code : κ → List PromotedLetter) (word : List κ) :
    T ≠ run (generated promotedStep code) word := by
  intro h
  apply reversible_outside_promoted T x hx hT hinj (compile code word)
  funext y
  exact (congrFun h y).trans (run_generated promotedStep code word y)
""")
    names += ["promoted_reentry", "promoted_good", "promoted_word_good",
              "reversible_outside_promoted", "reversible_outside_promoted_macros"]
    report["promotion"] = {
        "scope": "PROOF_ARTIFACT_ALPHABET_ONLY",
        "symbol": "Sum.inr ()", "recipe": list(recipe),
        "behavior_sha256": behavior, "rank": len(set(values)),
        "collision_inputs": list(collision(values)),
        "prior_certificate_sha256": report["certificate_sha256"],
        "prior_theorem": "discovered_not_admitted",
        "invariant": "CONSTANT_PRESERVING_OR_NONINJECTIVE",
    }
    fb.append_proofs(out, "".join(code), names, report)


def recipes():
    for pos in range(4):
        for control in ("all_equal", "not_all_equal", "pair_equal", "even_sum"):
            for mask in (1, 2, 3):
                yield (pos, control, mask)


def reference(recipe, x):
    pos, control, mask = recipe
    vals = gf.digits("signal4", x)
    others = [v for i, v in enumerate(vals) if i != pos]
    triggers = {
        "all_equal": len(set(others)) == 1,
        "not_all_equal": len(set(others)) != 1,
        "pair_equal": others[0] == others[1],
        "even_sum": sum(others) % 2 == 0,
    }
    if triggers[control]:
        vals[pos] ^= mask
    return gf.encoded("signal4", vals)


def packed(recipe, x):
    pos, control, mask = recipe
    a, b, c = ((x >> (2*i)) & 3 for i in range(4) if i != pos)
    if control == "all_equal":
        trigger = a == b == c
    elif control == "not_all_equal":
        trigger = a != b or b != c
    elif control == "pair_equal":
        trigger = a == b
    else:
        require(control == "even_sum", "unknown control")
        trigger = ((a ^ b ^ c) & 1) == 0
    return x ^ (mask << (2*pos)) if trigger else x


def search(state_path, base, out):
    report = gate(state_path, base, "promotion",
                  ("promoted_reentry", "promoted_word_good", "reversible_outside_promoted"))
    require(report["promotion"]["invariant"] == "CONSTANT_PRESERVING_OR_NONINJECTIVE",
            "wrong invariant")
    candidates, records = [], []
    for r in recipes():
        vals = cert.table(lambda x: reference(r, x), lambda x: packed(r, x))
        require(all(vals[vals[x]] == x for x in range(256)), "controlled XOR not involutive")
        witness = next((x for x in cert.CONSTANTS if vals[x] not in cert.CONSTANTS), None)
        row = {"recipe": list(r), "rank": len(set(vals)),
               "changed_inputs": sum(x != y for x, y in enumerate(vals)),
               "behavior_sha256": hashlib.sha256(bytes(vals)).hexdigest()}
        if witness is None:
            row["status"] = "NO_SEPARATION_BY_CONSTANT_TEST"
        else:
            row.update({"status": "SEPARATION_CANDIDATE",
                        "constant_input": witness, "constant_output": vals[witness]})
            candidates.append((row, vals))
        records.append(row)
    require(len(records) == 48 and len(candidates) == 36, "finite grammar regression")
    chosen, vals = min(candidates, key=lambda item: (-item[0]["changed_inputs"], item[0]["recipe"]))
    require(chosen["rank"] == 256 and chosen["changed_inputs"] == 128,
            "expected reversible discovery drift")
    x = chosen["constant_input"]
    out.mkdir(parents=True, exist_ok=True)
    (out / "Certificate.lean").write_bytes((base / "Certificate.lean").read_bytes())
    code = f"""
namespace ForgeLeanCertificate
open LinearInputOperatorWords

def reversibleDiscovery : Signal → Signal := tableStep {cert.literal(vals)}

theorem reversible_discovery_involution :
    ∀ x : Signal, reversibleDiscovery (reversibleDiscovery x) = x := by decide

theorem reversible_discovery_injective : Function.Injective reversibleDiscovery := by
  intro a b h
  calc
    a = reversibleDiscovery (reversibleDiscovery a) := (reversible_discovery_involution a).symm
    _ = reversibleDiscovery (reversibleDiscovery b) := congrArg reversibleDiscovery h
    _ = b := reversible_discovery_involution b

theorem reversible_discovery_witness :
    Constant ({x} : Signal) ∧ ¬ Constant (reversibleDiscovery {x}) := by decide

theorem reversible_discovery_not_promoted (word : List PromotedLetter) :
    reversibleDiscovery ≠ run promotedStep word :=
  reversible_outside_promoted reversibleDiscovery {x} reversible_discovery_witness.1
    reversible_discovery_witness.2 reversible_discovery_injective word

theorem reversible_discovery_not_promoted_macros {{κ : Type*}}
    (code : κ → List PromotedLetter) (word : List κ) :
    reversibleDiscovery ≠ run (generated promotedStep code) word :=
  reversible_outside_promoted_macros reversibleDiscovery {x} reversible_discovery_witness.1
    reversible_discovery_witness.2 reversible_discovery_injective code word
"""
    names = ["reversible_discovery_involution", "reversible_discovery_injective",
             "reversible_discovery_witness", "reversible_discovery_not_promoted",
             "reversible_discovery_not_promoted_macros"]
    report["reversible_search"] = {
        "total": len(records), "constant_test_exclusions": len(records) - len(candidates),
        "separation_candidates": len(candidates), "selected": chosen, "all": records,
        "prior_certificate_sha256": report["certificate_sha256"],
    }
    fb.append_proofs(out, code, names, report)
    print("REVERSIBLE SEARCH", len(records), "candidates", len(candidates), "selected", chosen)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("stage", choices=("prepare", "search"))
    p.add_argument("--state", required=True, type=Path)
    p.add_argument("--base", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    a = p.parse_args()
    (prepare if a.stage == "prepare" else search)(a.state, a.base, a.output)


if __name__ == "__main__":
    main()
