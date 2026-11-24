"""Bounded, persistent, proof-gated semantic evolution on signal4.

Only typed data is admitted. The state file is not executable. Every history
row is replayed from its exact semantic prefix and checked by the Lean kernel.
New predicates are generated from admitted operators, not installed code.
"""
from __future__ import annotations

import argparse
from datetime import date
import hashlib
import json
from pathlib import Path
import re
import subprocess

from tools.autonomy import forge_lean_certificate as cert
from tools.autonomy import forge_lean_feedback as fb
from tools.autonomy import forge_lean_reentry as reentry
from tools.autonomy import generic_forge as gf
from tools.autonomy import semantic_forge as sf

ROOT = cert.ROOT
FIXTURE = ROOT / "tests/fixtures/semantic_bridge_semantic.json"
LIMIT = 8
PARENTS = 4
ZERO = "0" * 64
OLD_SEED = "7f7362913e80569f688708a82fcda85dfb661fba6fd8126558214663a7a6099e"

CORE = r"""
namespace ForgeEvolution
open LinearInputOperatorWords
abbrev Signal := Fin 256

def tableStep (xs : List Signal) (x : Signal) : Signal :=
  (xs[x.val]?).getD 0

def Good (R : Signal → Signal → Prop) (T : Signal → Signal) : Prop :=
  (∀ x y, R x y → R (T x) (T y)) ∨ ¬ Function.Injective T

theorem good_comp (R : Signal → Signal → Prop) {f g : Signal → Signal}
    (hf : Good R f) (hg : Good R g) : Good R (fun x => g (f x)) := by
  rcases hf with hf | hf
  · rcases hg with hg | hg
    · exact Or.inl (fun x y h => hg _ _ (hf x y h))
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

theorem good_word (R : Signal → Signal → Prop) {ι : Type*}
    (step : ι → Signal → Signal) (hstep : ∀ i, Good R (step i))
    (word : List ι) : Good R (run step word) := by
  induction word with
  | nil => exact Or.inl (fun _ _ h => h)
  | cons i rest ih =>
    change Good R (fun x => run step rest (step i x))
    exact good_comp R (hstep i) ih

theorem noninjective_of_collision (T : Signal → Signal) (a b : Signal)
    (hne : a ≠ b) (he : T a = T b) : ¬ Function.Injective T :=
  fun h => hne (h he)
"""


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def digest(value):
    return sf.digest(value)


def fingerprint(values):
    return hashlib.sha256(bytes(values)).hexdigest()


def check_lean(out):
    with (out / "lean.log").open("w", encoding="utf-8") as log:
        proc = subprocess.run(
            ["lake", "env", "lean", "--trust=0", str((out / "Certificate.lean").resolve())],
            cwd=ROOT / "lean", stdout=log, stderr=subprocess.STDOUT,
            timeout=300, check=False)
    require(proc.returncode == 0, f"kernel failed: {out}/lean.log")
    cert.audit(out)


def seed_replay(out):
    """Independently reconstruct and reverify the two discoveries of merged #267."""
    base = out / "base"
    fb.prepare(FIXTURE, base)
    check_lean(base)
    rank = out / "rank"
    fb.search(FIXTURE, base, rank)
    check_lean(rank)
    promoted = out / "promoted"
    reentry.prepare(FIXTURE, rank, promoted)
    check_lean(promoted)
    reversible = out / "reversible"
    reentry.search(FIXTURE, promoted, reversible)
    check_lean(reversible)
    a = fb.read(rank / "mapping.json")["search"]["selected"]
    b = fb.read(reversible / "mapping.json")["reversible_search"]["selected"]
    require(a["behavior_sha256"] == OLD_SEED, "rank seed drift")
    first = tuple(a["recipe"])
    second = tuple(b["recipe"])
    tables = {
        "seed:rank": cert.table(lambda x: fb.reference(first, x), lambda x: fb.packed(first, x)),
        "seed:reversible": cert.table(lambda x: reentry.reference(second, x),
                                      lambda x: reentry.packed(second, x)),
    }
    require(fingerprint(tables["seed:reversible"]) == b["behavior_sha256"], "reversible seed drift")
    return tables


def roots(semantic, n, seeds):
    require(1 <= n <= len(semantic["receipts"]), "invalid semantic prefix")
    result = {}
    for name in cert.OPS:
        result["p:" + name] = cert.table(
            lambda x: gf.reference_primitive("signal4", name, x),
            lambda x: gf.independent_primitive("signal4", name, x))
    for row in semantic["receipts"][:n]:
        recipe = row["recipe"]
        result["s:" + row["id"]] = cert.table(
            lambda x: sf.apply_recipe(recipe, x, sf.reference_step),
            lambda x: sf.apply_recipe(recipe, x, sf.independent_step))
    result.update(seeds)
    return result


def components(tables):
    """Compute closed unary or xor-difference reachability components afresh.

    For injective generators (permutations), inverse powers also exist, so the
    edges on states and the induced edges on differences are reversible in
    reachability. The exact closure is separately checked, not assumed.
    """
    perms = [v for v in tables.values() if len(set(v)) == 256]
    for kind in ("unary", "diff"):
        edges = []
        for d in range(256):
            if kind == "unary":
                edges.append({t[d] for t in perms})
            else:
                edges.append({t[x] ^ t[x ^ d] for t in perms for x in range(256)})
        seen = set()
        for d in range(0 if kind == "unary" else 1, 256):
            if d in seen:
                continue
            orbit, queue = {d}, [d]
            for q in queue:
                for y in sorted(edges[q]):
                    if y not in orbit:
                        orbit.add(y)
                        queue.append(y)
            seen.update(orbit)
            if (kind == "unary" and len(orbit) < 256 or
                    kind == "diff" and len(orbit) <= 8 and 0 not in orbit):
                yield {"kind": kind, "members": sorted(orbit)}


def witness(values, invariant):
    members = set(invariant["members"])
    if invariant["kind"] == "unary":
        for x in invariant["members"]:
            if values[x] not in members:
                return [x, x]
    else:
        for d in invariant["members"]:
            for x in range(256):
                if values[x] ^ values[x ^ d] not in members:
                    return [x, x ^ d]
    return None


def productions(tables):
    # Each admitted symbol supplies a new observable terminal. The newest four
    # terminals are expanded this cycle; older terminals remain in the library.
    for parent in list(tables)[-PARENTS:]:
        for target in range(8):
            for output in range(8):
                for other in [-1] + [b for b in range(8) if b != target]:
                    for mode in ("and", "xor"):
                        yield [parent, target, output, other, mode]


def evaluate(recipe, tables, independent=False):
    require(type(recipe) is list and len(recipe) == 5, "invalid recipe")
    parent, target, output, other, mode = recipe
    require(type(parent) is str and parent in tables
            and type(target) is int and 0 <= target < 8
            and type(output) is int and 0 <= output < 8
            and type(other) is int and -1 <= other < 8 and other != target
            and mode in ("and", "xor"), "invalid typed production")
    p = tables[parent]
    result = []
    for x in range(256):
        if independent:
            digits = [(x // (2 ** j)) % 2 for j in range(8)]
            digits[target] = 0
            masked = sum(v * 2 ** j for j, v in enumerate(digits))
            a = p[masked] // (2 ** output) % 2
            b = 1 if other == -1 else digits[other]
            guard = a * b if mode == "and" else (a + b) % 2
            old = (x // (2 ** target)) % 2
            result.append(x + (1 - 2 * old) * guard * 2 ** target)
        else:
            a = (p[x & ~(1 << target)] >> output) & 1
            b = 1 if other == -1 else (x >> other) & 1
            guard = a & b if mode == "and" else a ^ b
            result.append(x ^ (guard << target))
    return result


def search(tables):
    invariants = list(components(tables))
    known = {tuple(v) for v in tables.values()}
    latest = list(tables)[-1]
    selected, counts = None, {"generated": 0, "distinct": 0, "separating": 0}
    for recipe in productions(tables):
        counts["generated"] += 1
        values = evaluate(recipe, tables)
        key = tuple(values)
        if key in known:
            continue
        known.add(key)
        counts["distinct"] += 1
        broken = [(r, w) for r in invariants if (w := witness(values, r)) is not None]
        if not broken:
            continue
        counts["separating"] += 1
        changed = sum(x != y for x, y in enumerate(values))
        # Preserve as many remaining discovered invariants as possible; prefer
        # even number of swapped pairs, then a latest-parent rule. This is
        # a search heuristic only, not an additional mathematical invariant.
        priority = (len(broken), changed % 4 != 0, recipe[0] != latest,
                    -changed, recipe)
        r, w = min(broken, key=lambda rw: (
            1 if rw[0]["kind"] == "unary" else len(rw[0]["members"]) + 1,
            rw[0]["kind"], rw[0]["members"]))
        if selected is None or priority < selected[0]:
            selected = (priority, recipe, values, r, w)
    if selected is None:
        return None, invariants, counts
    _, recipe, values, invariant, pair = selected
    require(values == evaluate(recipe, tables, independent=True)
            and all(values[values[x]] == x for x in range(256)),
            "candidate independent involution audit failed")
    return (recipe, values, invariant, pair), invariants, counts


def certificate(tables, values, invariant, pair, out):
    require(invariant in list(components(tables)) and witness(values, invariant) == pair,
            "unreproducible invariant or witness")
    source = ["import Mathlib\nset_option maxRecDepth 16384\n"
              "set_option maxHeartbeats 50000000\n", cert.WORDS.read_text(), CORE]
    names = ["good_comp", "good_word", "noninjective_of_collision"]
    kind, members = invariant["kind"], invariant["members"]
    if kind == "unary":
        flags = [int(x in members) for x in range(256)]
        source.append(f"\ndef flag : Signal → Signal := tableStep {cert.literal(flags)}\n")
        source.append("abbrev Relation (x _y : Signal) : Prop := flag x = 1\n")
    else:
        source.append(fb.finite_function("difference", len(members), members))
        source.append(f"""
def shift (i : Fin {len(members)}) (x : Signal) : Signal :=
  ⟨(Nat.xor x.val (difference i).val) % 256, Nat.mod_lt _ (by decide)⟩

abbrev Relation (x y : Signal) : Prop :=
  ∃ i : Fin {len(members)}, y = shift i x
""")
    for i, v in enumerate(tables.values()):
        name = f"op_{i}"
        source.append(f"\ndef {name} : Signal → Signal := tableStep {cert.literal(v)}\n")
        if len(set(v)) != 256:
            a, b = reentry.collision(v)
            source.append(f"""
theorem letter_{i} : Good Relation {name} :=
  Or.inr (noninjective_of_collision {name} {a} {b} (by decide) (by decide))
""")
        elif kind == "unary":
            source.append(f"""
theorem letter_{i} : Good Relation {name} := by
  refine Or.inl ?_
  intro x y h
  have hp : ∀ x : Signal, flag x = 1 → flag ({name} x) = 1 := by decide
  exact hp x h
""")
        else:
            source.append(f"""
theorem letter_{i} : Good Relation {name} := by
  refine Or.inl ?_
  intro x y h
  obtain ⟨j, rfl⟩ := h
  have hp : ∀ (x : Signal) (j : Fin {len(members)}),
      Relation ({name} x) ({name} (shift j x)) := by decide
  exact hp x j
""")
        names.append(f"letter_{i}")
    n = len(tables)
    source.append(f"\ndef alphabet (i : Fin {n}) : Signal → Signal := match i.val with\n")
    source.extend(f"  | {i} => op_{i}\n" for i in range(n))
    source.append("  | _ => op_0\n")
    source.append(f"""
theorem alphabet_good (i : Fin {n}) : Good Relation (alphabet i) := by
  fin_cases i <;> first
""")
    source.extend(f"    | exact letter_{i}\n" for i in range(n))
    x, y = pair
    source.append(f"""
theorem alphabet_word_good (word : List (Fin {n})) :
    Good Relation (run alphabet word) :=
  good_word Relation alphabet alphabet_good word

def candidate : Signal → Signal := tableStep {cert.literal(values)}

theorem candidate_involution : ∀ x : Signal, candidate (candidate x) = x := by decide

theorem candidate_injective : Function.Injective candidate := by
  intro a b h
  calc
    a = candidate (candidate a) := (candidate_involution a).symm
    _ = candidate (candidate b) := congrArg candidate h
    _ = b := candidate_involution b

theorem candidate_witness : Relation ({x} : Signal) {y} ∧
    ¬ Relation (candidate {x}) (candidate {y}) := by decide

theorem candidate_not_word (word : List (Fin {n})) :
    candidate ≠ run alphabet word := by
  intro h
  have hg := alphabet_word_good word
  rw [← h] at hg
  rcases hg with hp | hn
  · exact candidate_witness.2 (hp _ _ candidate_witness.1)
  · exact hn candidate_injective

theorem candidate_not_macros {{κ : Type*}} (code : κ → List (Fin {n})) (word : List κ) :
    candidate ≠ run (generated alphabet code) word := by
  intro h
  apply candidate_not_word (compile code word)
  funext y
  exact (congrFun h y).trans (run_generated alphabet code word y)

end ForgeEvolution
""")
    names += ["alphabet_good", "alphabet_word_good", "candidate_involution",
              "candidate_injective", "candidate_witness", "candidate_not_word",
              "candidate_not_macros"]
    source.extend(f"#print axioms ForgeEvolution.{name}\n" for name in names)
    out.mkdir(parents=True, exist_ok=True)
    path = out / "Certificate.lean"
    path.write_text("".join(source), encoding="utf-8")
    fb.write(out / "mapping.json", {"status": "GENERATED_PENDING_KERNEL_VERIFICATION",
             "receipt_count": 1, "theorem_count": len(names), "theorems": names,
             "alphabet": [{"id": k, "behavior_sha256": fingerprint(v)} for k,v in tables.items()],
             "invariant": invariant, "witness": pair, "behavior_sha256": fingerprint(values),
             "certificate_sha256": fb.sha(path)})
    return fb.sha(path)


def validate_date(d):
    require(type(d) is str and date.fromisoformat(d).isoformat() == d, "invalid day")


def read_history(path):
    state = sf.read(path)
    require(type(state) is dict and set(state) == {"schema_version", "receipts"}
            and type(state["schema_version"]) is int and state["schema_version"] == 1
            and type(state["receipts"]) is list and len(state["receipts"]) <= LIMIT,
            "bad evolution ledger")
    return state


FIELDS = {"generation", "day", "source_sha", "semantic_count", "semantic_prefix_sha256",
          "recipe", "behavior_sha256", "invariant", "witness", "certificate_sha256",
          "theorem", "previous_sha256", "chain_sha256"}


def replay(state, semantic, seeds, out):
    accepted = {}
    previous, last, count = ZERO, None, 1
    for i, row in enumerate(state["receipts"], 1):
        require(type(row) is dict and set(row) == FIELDS and row["generation"] == i
                and row["previous_sha256"] == previous
                and row["chain_sha256"] == digest({k:v for k,v in row.items() if k != "chain_sha256"})
                and re.fullmatch(r"[0-9a-f]{40}", row["source_sha"])
                and row["theorem"] == "ForgeEvolution.candidate_not_word",
                "broken evolution receipt")
        validate_date(row["day"])
        require(last is None or row["day"] > last, "nonmonotone day")
        n = row["semantic_count"]
        require(type(n) is int and count <= n <= len(semantic["receipts"])
                and row["semantic_prefix_sha256"] == semantic["receipts"][n-1]["chain_sha256"],
                "semantic ancestry mismatch")
        tables = roots(semantic, n, seeds)
        tables.update(accepted)
        require(row["recipe"] in productions(tables), "unreviewed historical recipe")
        values = evaluate(row["recipe"], tables)
        require(values == evaluate(row["recipe"], tables, independent=True)
                and all(values[values[x]] == x for x in range(256))
                and fingerprint(values) == row["behavior_sha256"], "historical behavior drift")
        stage = out / f"history-{i}"
        sha = certificate(tables, values, row["invariant"], row["witness"], stage)
        require(sha == row["certificate_sha256"], "historical certificate drift")
        check_lean(stage)
        accepted["e:" + row["chain_sha256"][:24]] = values
        previous, last, count = row["chain_sha256"], row["day"], n
    return accepted


def cycle(state_path, semantic_path, day, head, out):
    validate_date(day)
    require(re.fullmatch(r"[0-9a-f]{40}", head), "exact head required")
    state = read_history(state_path)
    semantic = sf.validate_state(sf.read(semantic_path))
    pinned = sf.validate_state(sf.read(FIXTURE))
    require(semantic["receipts"][:len(pinned["receipts"])] == pinned["receipts"],
            "actual seed receipt missing or changed")
    out.mkdir(parents=True, exist_ok=True)
    seeds = seed_replay(out / "seeds")
    accepted = replay(state, semantic, seeds, out)
    tables = roots(semantic, len(semantic["receipts"]), seeds)
    tables.update(accepted)
    report = {"previous_generations": len(accepted),
              "semantic_count": len(semantic["receipts"]),
              "production_symbols": list(tables),
              "active_production_symbols": list(tables)[-PARENTS:]}
    if len(accepted) >= LIMIT:
        report["status"] = "MAINTENANCE_LIMIT"
    elif state["receipts"] and state["receipts"][-1]["day"] >= day:
        require(state["receipts"][-1]["day"] == day, "clock moved backwards")
        report["status"] = "ALREADY_VERIFIED_TODAY"
    else:
        chosen, invariants, counts = search(tables)
        report.update({"invariants": invariants, "search": counts})
        if chosen is None:
            report["status"] = "BOUNDED_INVARIANT_OR_GRAMMAR_EXHAUSTED"
        else:
            recipe, values, invariant, pair = chosen
            stage = out / "new"
            sha = certificate(tables, values, invariant, pair, stage)
            check_lean(stage)
            row = {"generation": len(accepted)+1, "day": day, "source_sha": head,
                   "semantic_count": len(semantic["receipts"]),
                   "semantic_prefix_sha256": semantic["receipts"][-1]["chain_sha256"],
                   "recipe": recipe, "behavior_sha256": fingerprint(values),
                   "invariant": invariant, "witness": pair, "certificate_sha256": sha,
                   "theorem": "ForgeEvolution.candidate_not_word",
                   "previous_sha256": state["receipts"][-1]["chain_sha256"] if accepted else ZERO}
            row["chain_sha256"] = digest(row)
            state["receipts"].append(row)
            report.update({"status": "NEW_KERNEL_VERIFIED_RECEIPT", "receipt": row,
                           "new_production_symbol": "e:" + row["chain_sha256"][:24]})
    fb.write(out / "next-state.json", state)
    fb.write(out / "report.json", report)
    print(json.dumps(report, sort_keys=True))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--state", required=True, type=Path)
    p.add_argument("--semantic", required=True, type=Path)
    p.add_argument("--day", required=True)
    p.add_argument("--head", required=True)
    p.add_argument("--output", required=True, type=Path)
    a = p.parse_args()
    cycle(a.state, a.semantic, a.day, a.head, a.output)


if __name__ == "__main__":
    main()
