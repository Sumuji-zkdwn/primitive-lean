"""Proof-gated extensions after the original unary/difference search stalls.

The original certificate generator remains byte-identical for its two
historical invariant kinds. No new ledger schema, executable recipes or
trusted Python verdicts: a new receipt still requires the Lean kernel.
"""
from tools.autonomy import forge_lean_certificate as cert
from tools.autonomy import forge_lean_feedback as fb
from tools.autonomy import forge_lean_reentry as reentry

KINDS = ("affine", "even")
N = 256


def require(ok, message):
    if not ok:
        raise ValueError(message)


def affine_witness(v):
    """First failed affine basis reconstruction gives a four-point witness."""
    columns = [v[1 << i] ^ v[0] for i in range(8)]
    predicted = [v[0]] * N
    for i, col in enumerate(columns):
        for x in range(1 << i, 1 << (i + 1)):
            predicted[x] = predicted[x ^ (1 << i)] ^ col
    for x in range(N):
        if v[x] != predicted[x]:
            a = x & -x
            b = x ^ a
            require(v[0] ^ v[a] ^ v[b] ^ v[x] != 0, "affine witness drift")
            return [0, a, b, x]
    return None


def swaps(v):
    """Cycle decomposition as a product of transpositions, rightmost first."""
    require(len(v) == N and len(set(v)) == N, "not a permutation")
    seen = set()
    result = []
    for x in range(N):
        if x in seen:
            continue
        cycle = [x]
        seen.add(x)
        y = v[x]
        while y != x:
            require(y not in seen, "invalid cycle")
            seen.add(y)
            cycle.append(y)
            y = v[y]
        result.extend((x, y) for y in reversed(cycle[1:]))
    return result


def witness(v, kind):
    if kind == "affine":
        return affine_witness(v)
    if kind == "even":
        n = len(swaps(v))
        return [n] if n % 2 else None
    raise ValueError("unknown extension invariant")


def search(tables, productions, evaluate, invariants, legacy_counts):
    perms = [v for v in tables.values() if len(set(v)) == N]
    # These tests are exact for membership in AGL and Alt, but do not
    # assert that the current generated subgroup equals either supergroup.
    kinds = [kind for kind in KINDS if all(witness(v, kind) is None for v in perms)]
    report = dict(legacy_counts)
    ext = {"available_invariants": kinds, "all_parents": len(tables),
           "generated": 0, "distinct": 0, "separating": 0,
           "membership_scope": "certified_affine_or_even_supergroup_only"}
    report["group_extension"] = ext
    invs = invariants + [{"kind": k, "members": []} for k in kinds]
    if not kinds:
        return None, invs, report
    known = {tuple(v) for v in tables.values()}
    best = None
    toffoli = tuple(x ^ int((x & 6) == 6) for x in range(N))
    for recipe in productions(tables, all_parents=True):
        ext["generated"] += 1
        values = evaluate(recipe, tables)
        key = tuple(values)
        if key in known:
            continue
        known.add(key)
        ext["distinct"] += 1
        # Prefer the affine separator first, and preserve evenness where
        # possible. A canonical Toffoli is available in the pinned fixture.
        kind = kinds[0]
        pair = witness(values, kind)
        if pair is None:
            continue
        ext["separating"] += 1
        priority = (kind == "affine" and witness(values, "even") is not None,
                    kind == "affine" and key != toffoli,
                    recipe)
        if best is None or priority < best[0]:
            best = (priority, recipe, values, {"kind": kind, "members": []}, pair)
    if best is None:
        return None, invs, report
    _, recipe, values, invariant, pair = best
    require(values == evaluate(recipe, tables, independent=True)
            and all(values[values[x]] == x for x in range(N)), "extension evaluator drift")
    return (recipe, values, invariant, pair), invs, report


PROPERTY_CORE = r"""
def GoodP (P : (Signal → Signal) → Prop) (f : Signal → Signal) : Prop :=
  P f ∨ ¬ Function.Injective f

theorem goodP_comp (P : (Signal → Signal) → Prop)
    (closed : ∀ f g : Signal → Signal, P f → P g → P (fun x => g (f x)))
    {f g : Signal → Signal} (hf : GoodP P f) (hg : GoodP P g) :
    GoodP P (fun x => g (f x)) := by
  rcases hf with hf | hf
  · rcases hg with hg | hg
    · exact Or.inl (closed f g hf hg)
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

theorem goodP_word (P : (Signal → Signal) → Prop)
    (unit : P (fun x => x))
    (closed : ∀ f g : Signal → Signal, P f → P g → P (fun x => g (f x)))
    {ι : Type*} (step : ι → Signal → Signal)
    (hstep : ∀ i, GoodP P (step i)) (word : List ι) :
    GoodP P (run step word) := by
  induction word with
  | nil => exact Or.inl unit
  | cons i rest ih =>
    change GoodP P (fun x => run step rest (step i x))
    exact goodP_comp P closed (hstep i) ih
"""

AFFINE_CORE = r"""
def bit (x : Signal) (i : Fin 8) : Bool := x.val.testBit i.val

def rel (a b c d : Bool) : Prop := (a != b) = (c != d)

def Quad (a b c d : Signal) : Prop :=
  ∀ i : Fin 8, rel (bit a i) (bit b i) (bit c i) (bit d i)

def linearBit : List (Fin 8) → Bool → Signal → Bool
  | [], b, _ => b
  | i :: rest, b, x => bit x i != linearBit rest b x

theorem rel_xor : ∀ a b c d e f g h : Bool,
    rel a b c d → rel e f g h →
    rel (a != e) (b != f) (c != g) (d != h) := by decide

theorem linearBit_preserves (mask : List (Fin 8)) (z : Bool)
    (a b c d : Signal) (h : Quad a b c d) :
    rel (linearBit mask z a) (linearBit mask z b)
        (linearBit mask z c) (linearBit mask z d) := by
  induction mask with
  | nil => rfl
  | cons i rest ih =>
    exact rel_xor _ _ _ _ _ _ _ _ (h i) ih

def Property (f : Signal → Signal) : Prop :=
  ∀ a b c d : Signal, Quad a b c d → Quad (f a) (f b) (f c) (f d)

theorem property_id : Property (fun x => x) := by
  intro a b c d h
  exact h

theorem property_comp (f g : Signal → Signal) (hf : Property f) (hg : Property g) :
    Property (fun x => g (f x)) := by
  intro a b c d h
  exact hg _ _ _ _ (hf _ _ _ _ h)
"""

EVEN_CORE = r"""
def swapProduct : List (Signal × Signal) → Equiv.Perm Signal
  | [] => 1
  | p :: rest => Equiv.swap p.1 p.2 * swapProduct rest

theorem swapProduct_sign (l : List (Signal × Signal))
    (h : ∀ p ∈ l, p.1 ≠ p.2) :
    Equiv.Perm.sign (swapProduct l) = (-1) ^ l.length := by
  induction l with
  | nil => simp [swapProduct]
  | cons p rest ih =>
    have hp : p.1 ≠ p.2 := h p (by simp)
    have hr : ∀ q ∈ rest, q.1 ≠ q.2 := by
      intro q hq
      exact h q (List.mem_cons_of_mem _ hq)
    rw [swapProduct, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hp,
        ih hr, List.length_cons, pow_succ] <;> exact mul_comm _ _

def Property (f : Signal → Signal) : Prop :=
  ∃ p : Equiv.Perm Signal, (∀ x, p x = f x) ∧ Equiv.Perm.sign p = 1

theorem property_id : Property (fun x => x) :=
  ⟨1, fun _ => rfl, by simp⟩

theorem property_comp (f g : Signal → Signal) (hf : Property f) (hg : Property g) :
    Property (fun x => g (f x)) := by
  obtain ⟨p, hp, hs⟩ := hf
  obtain ⟨q, hq, ht⟩ := hg
  refine ⟨q * p, ?_, ?_⟩
  · intro x
    change q (p x) = g (f x)
    rw [hq, hp]
  · simp [Equiv.Perm.sign_mul, hs, ht]
"""


def affine_letter(i, v):
    name = f"op_{i}"
    lines = []
    for j in range(8):
        mask = [k for k in range(8) if ((v[1 << k] ^ v[0]) >> j) & 1]
        z = "true" if (v[0] >> j) & 1 else "false"
        lines.append(f"theorem bit_{i}_{j} : ∀ x : Signal, bit ({name} x) {j} = linearBit {mask} {z} x := by decide\n")
    lines.append(f"""
theorem letter_{i} : GoodP Property {name} := by
  refine Or.inl ?_
  intro a b c d h j
  fin_cases j
""")
    for j in range(8):
        lines.append(f"""  · change rel (bit ({name} a) {j}) (bit ({name} b) {j})
        (bit ({name} c) {j}) (bit ({name} d) {j})
    rw [bit_{i}_{j} a, bit_{i}_{j} b, bit_{i}_{j} c, bit_{i}_{j} d]
    exact linearBit_preserves _ _ _ _ _ _ h
""")
    return "".join(lines)


def permutation_code(name, v, odd):
    pairs = swaps(v)
    literal = "[" + ", ".join(f"({a}, {b})" for a, b in pairs) + "]"
    sign = "-1" if odd else "1"
    require(len(pairs) % 2 == int(odd), "sign witness drift")
    return f"""
def {name}_swaps : List (Signal × Signal) := {literal}
def {name}_perm : Equiv.Perm Signal := swapProduct {name}_swaps
theorem {name}_correct : ∀ x : Signal, {name}_perm x = {name} x := by decide
theorem {name}_sign : Equiv.Perm.sign {name}_perm = {sign} := by
  change Equiv.Perm.sign (swapProduct {name}_swaps) = {sign}
  rw [swapProduct_sign {name}_swaps (by decide)] <;> decide
"""


def certificate(tables, values, invariant, pair, out, legacy_core):
    kind = invariant["kind"]
    require(invariant == {"kind": kind, "members": []} and kind in KINDS
            and witness(values, kind) == pair, "bad group invariant witness")
    require(all(witness(v, kind) is None for v in tables.values() if len(set(v)) == N),
            "group invariant not closed")
    source = ["import Mathlib\nset_option maxRecDepth 16384\n"
              "set_option maxHeartbeats 50000000\n", cert.WORDS.read_text(),
              legacy_core, PROPERTY_CORE, AFFINE_CORE if kind == "affine" else EVEN_CORE]
    names = ["goodP_comp", "goodP_word", "property_id", "property_comp"]
    names += ["rel_xor", "linearBit_preserves"] if kind == "affine" else ["swapProduct_sign"]
    for i, v in enumerate(tables.values()):
        name = f"op_{i}"
        source.append(f"\ndef {name} : Signal → Signal := tableStep {cert.literal(v)}\n")
        if len(set(v)) != N:
            a, b = reentry.collision(v)
            source.append(f"""
theorem letter_{i} : GoodP Property {name} :=
  Or.inr (noninjective_of_collision {name} {a} {b} (by decide) (by decide))
""")
        elif kind == "affine":
            source.append(affine_letter(i, v))
        else:
            source.append(permutation_code(name, v, False))
            source.append(f"""
theorem letter_{i} : GoodP Property {name} :=
  Or.inl ⟨{name}_perm, {name}_correct, {name}_sign⟩
""")
        names.append(f"letter_{i}")
    n = len(tables)
    source.append(f"\ndef alphabet (i : Fin {n}) : Signal → Signal := match i.val with\n")
    source.extend(f"  | {i} => op_{i}\n" for i in range(n))
    source.append("  | _ => op_0\n")
    source.append(f"""
theorem alphabet_good (i : Fin {n}) : GoodP Property (alphabet i) := by
  fin_cases i <;> first
""")
    source.extend(f"    | exact letter_{i}\n" for i in range(n))
    source.append(f"""
theorem alphabet_word_good (word : List (Fin {n})) :
    GoodP Property (run alphabet word) :=
  goodP_word Property property_id property_comp alphabet alphabet_good word

def candidate : Signal → Signal := tableStep {cert.literal(values)}

theorem candidate_involution : ∀ x : Signal, candidate (candidate x) = x := by decide

theorem candidate_injective : Function.Injective candidate := by
  intro a b h
  calc
    a = candidate (candidate a) := (candidate_involution a).symm
    _ = candidate (candidate b) := congrArg candidate h
    _ = b := candidate_involution b
""")
    if kind == "affine":
        a, b, c, d = pair
        source.append(f"""
theorem candidate_witness : ¬ Property candidate := by
  have hin : Quad {a} {b} {c} {d} := by decide
  have hout : ¬ Quad (candidate {a}) (candidate {b}) (candidate {c}) (candidate {d}) := by decide
  exact fun h => hout (h _ _ _ _ hin)
""")
    else:
        source.append(permutation_code("candidate", values, True))
        source.append(r"""
theorem candidate_witness : ¬ Property candidate := by
  intro h
  obtain ⟨p, hp, hs⟩ := h
  have he : p = candidate_perm := by
    apply Equiv.ext
    intro x
    exact (hp x).trans (candidate_correct x).symm
  rw [he, candidate_sign] at hs
  exact (by decide : (-1 : ℤˣ) ≠ 1) hs
""")
    source.append(f"""
theorem candidate_not_word (word : List (Fin {n})) :
    candidate ≠ run alphabet word := by
  intro h
  have hg := alphabet_word_good word
  rw [← h] at hg
  rcases hg with hp | hn
  · exact candidate_witness hp
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
              "candidate_injective", "candidate_witness", "candidate_not_word", "candidate_not_macros"]
    source.extend(f"#print axioms ForgeEvolution.{name}\n" for name in names)
    out.mkdir(parents=True, exist_ok=True)
    path = out / "Certificate.lean"
    path.write_text("".join(source), encoding="utf-8")
    import hashlib
    fb.write(out / "mapping.json", {"status": "GENERATED_PENDING_KERNEL_VERIFICATION",
             "receipt_count": 1, "theorem_count": len(names), "theorems": names,
             "alphabet": [{"id": k, "behavior_sha256": hashlib.sha256(bytes(v)).hexdigest()}
                          for k, v in tables.items()],
             "invariant": invariant, "witness": pair,
             "behavior_sha256": hashlib.sha256(bytes(values)).hexdigest(),
             "certificate_sha256": fb.sha(path)})
    return fb.sha(path)
