import Mathlib.Data.Fintype.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Cycles of a pair of idempotent buttons

One beat means first applying `A` and then `B`. An intermediate state leading
to a moving point in the image of the beat map lies outside its entire image.
This gives a sharp lower bound on the size of an exact periodic orbit's ambient
state space. The final theorem records the corresponding factorization criterion
for arbitrary self-maps, allowing either idempotent to be the identity.
-/

namespace IdempotentButtonCycles

open Function

variable {X I : Type*}

def Idempotent (button : X → X) : Prop := ∀ x, button (button x) = button x

/-- An intermediate state leading to a moving image point cannot end any beat. -/
theorem intermediate_outside_image {A B : X → X} (hA : Idempotent A)
    (hB : Idempotent B) (s : X)
    (hm : (B ∘ A) ((B ∘ A) s) ≠ (B ∘ A) s) :
    A s ∉ Set.range (B ∘ A) := by
  rintro ⟨t, ht⟩
  change B (A t) = A s at ht
  have hfix : B (A s) = A s := by
    calc B (A s) = B (B (A t)) := congrArg B ht.symm
         _ = B (A t) := hB (A t)
         _ = A s := ht
  apply hm
  change B (A (B (A s))) = B (A s)
  simp only [hfix, hA s]

/-- Lower bound for the actual least period of a point, with no assumed partition
of the states and no assumed behavior away from the orbit. -/
theorem twice_minimalPeriod_le_card [Fintype X] {A B : X → X}
    (hA : Idempotent A) (hB : Idempotent B) (x : X)
    (hk : 1 < minimalPeriod (B ∘ A) x) :
    2 * minimalPeriod (B ∘ A) x ≤ Fintype.card X := by
  let T := B ∘ A
  let k := minimalPeriod T x
  have hpos : 0 < minimalPeriod T x := lt_trans Nat.zero_lt_one hk
  have hx := minimalPeriod_pos_iff_mem_periodicPts.mp hpos
  have hTx : T x ∈ periodicPts T :=
    minimalPeriod_pos_iff_mem_periodicPts.mp (by rwa [minimalPeriod_apply hx])
  let prev (i : Fin k) := T^[i.val] x
  let front (i : Fin k) := T^[i.val] (T x)
  let back (i : Fin k) := A (prev i)
  have step (i : Fin k) : T (prev i) = front i :=
    (iterate_succ_apply' T i.val x).symm.trans (iterate_succ_apply T i.val x)
  have front_inj : Injective front := by
    intro i j hij
    apply Fin.ext
    apply (iterate_eq_iterate_iff_of_lt_minimalPeriod (f := T) (x := T x) ?_ ?_).mp hij
    · simpa only [minimalPeriod_apply hx] using i.isLt
    · simpa only [minimalPeriod_apply hx] using j.isLt
  have back_inj : Injective back := by
    intro i j hij
    apply front_inj
    exact (step i).symm.trans ((congrArg B hij).trans (step j))
  have moved (i : Fin k) : T (front i) ≠ front i := by
    intro hfix
    have heq : minimalPeriod T (front i) = 1 := minimalPeriod_eq_one_iff_isFixedPt.mpr hfix
    dsimp only [front] at heq
    rw [minimalPeriod_apply_iterate hTx, minimalPeriod_apply hx] at heq
    exact (Nat.ne_of_gt hk) heq
  have separate (i j : Fin k) : front i ≠ back j := by
    intro heq
    have hm : T (T (prev j)) ≠ T (prev j) := by
      rw [step j]
      exact moved j
    exact (intermediate_outside_image hA hB (prev j) hm) ⟨prev i, (step i).trans heq⟩
  simpa [two_mul, k, T] using Fintype.card_le_of_injective _ (front_inj.sumElim back_inj separate)

theorem six_le_card_of_period_three [Fintype X] {A B : X → X}
    (hA : Idempotent A) (hB : Idempotent B) (x : X) (h : minimalPeriod (B ∘ A) x = 3) :
    6 ≤ Fintype.card X := by
  have bound := twice_minimalPeriod_le_card hA hB x (by rw [h]; decide)
  simpa only [h] using bound

/-- In the two-copy model, left states are the fronts and right states are the backs. -/
def pressA : I ⊕ I → I ⊕ I
  | .inl i => .inr i
  | .inr i => .inr i

def pressB (next : I → I) : I ⊕ I → I ⊕ I
  | .inl i => .inl i
  | .inr i => .inl (next i)

theorem pressA_idempotent : Idempotent (pressA (I := I)) := by
  intro s
  cases s <;> rfl

theorem pressB_idempotent (next : I → I) : Idempotent (pressB next) := by
  intro s
  cases s <;> rfl

theorem period_on_front (next : I → I) (i : I) :
    minimalPeriod (pressB next ∘ pressA) (Sum.inl i) = minimalPeriod next i := by
  have h : Semiconj (Sum.inl : I → I ⊕ I) next (pressB next ∘ pressA) := fun _ => rfl
  apply minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change (pressB next ∘ pressA)^[n] (Sum.inl i) = Sum.inl i ↔ next^[n] i = i
  rw [← h.iterate_right n i, Sum.inl.injEq]

/-- The bound is attained for every period k ≥ 2. This construction also works for k = 1. -/
theorem realizes_on_twice (k : ℕ) [NeZero k] :
    ∃ (A B : (ZMod k ⊕ ZMod k) → (ZMod k ⊕ ZMod k)) (x : ZMod k ⊕ ZMod k),
      Idempotent A ∧ Idempotent B ∧ minimalPeriod (B ∘ A) x = k ∧
        Fintype.card (ZMod k ⊕ ZMod k) = 2 * k := by
  refine ⟨pressA, pressB (1 + ·), .inl 0, pressA_idempotent, pressB_idempotent _, ?_, ?_⟩
  · rw [period_on_front]
    exact ZMod.addOrderOf_one k
  · simp [two_mul, ZMod.card]

/-- At the lower bound, the prescribed front permutation determines both buttons
on every state up to a relabeling. This also covers several disjoint moving cycles. -/
theorem canonical_at_equality [Fintype I] [Fintype X] {A B : X → X}
    (hA : Idempotent A) (hB : Idempotent B) (next : Equiv.Perm I)
    (moved : ∀ i, next i ≠ i) (front : I → X) (hf : Injective front)
    (step : ∀ i, B (A (front i)) = front (next i))
    (hc : Fintype.card X = 2 * Fintype.card I) :
    ∃ e : (I ⊕ I) ≃ X, (∀ i, e (.inl i) = front i) ∧
      (∀ s, A (e s) = e (pressA s)) ∧ (∀ s, B (e s) = e (pressB next s)) := by
  have fixB (i : I) : B (front i) = front i := by
    obtain ⟨j, rfl⟩ := next.surjective i
    rw [← step j]
    exact hB _
  have back_inj : Injective (A ∘ front) := by
    intro i j hij
    exact next.injective (hf ((step i).symm.trans ((congrArg B hij).trans (step j))))
  have separate (i j : I) : front i ≠ A (front j) := by
    intro heq
    have fixA : A (front i) = front i := (congrArg A heq).trans ((hA _).trans heq.symm)
    exact moved i (hf ((step i).symm.trans ((congrArg B fixA).trans (fixB i))))
  let label := Sum.elim front (A ∘ front)
  have hinj : Injective label := hf.sumElim back_inj separate
  have hcard : Fintype.card (I ⊕ I) = Fintype.card X := by simpa [two_mul] using hc.symm
  let e := Equiv.ofBijective label ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩)
  refine ⟨e, fun _ => rfl, ?_, ?_⟩
  · rintro (i | i)
    · rfl
    · exact hA (front i)
  · rintro (i | i)
    · exact fixB i
    · exact step i

/-- Finite singular case: Howie–Robertson–Schein (1988). Arbitrary sets and proper
idempotents: Thomas (1998), Theorem 2. Here the identity is allowed as a button. -/
theorem factor_iff_outside_preimages (T : X → X) :
    (∃ A B : X → X, Idempotent A ∧ Idempotent B ∧ T = B ∘ A) ↔
      ∀ y ∈ Set.range T, T y ≠ y → ∃ u, u ∉ Set.range T ∧ T u = y := by
  constructor
  · rintro ⟨A, B, hA, hB, rfl⟩ _ ⟨s, rfl⟩ hm
    exact ⟨A s, intermediate_outside_image hA hB s hm, congrArg B (hA s)⟩
  · intro h
    classical
    let repr (y : Set.range T) : X :=
      if hy : T y.val = y.val then y.val else (h y.val y.property hy).choose
    have target (y : Set.range T) : T (repr y) = y.val := by
      by_cases hy : T y.val = y.val
      · simpa only [repr, dite_eq_left hy] using hy
      · simpa only [repr, dite_eq_right hy] using (h y.val y.property hy).choose_spec.2
    have in_image (y : Set.range T) (hm : repr y ∈ Set.range T) : repr y = y.val := by
      by_cases hy : T y.val = y.val
      · simp [repr, hy]
      · exact False.elim ((h y.val y.property hy).choose_spec.1 (by
          simpa only [repr, dite_eq_right hy] using hm))
    let A (x : X) := repr ⟨T x, x, rfl⟩
    let B (x : X) := if x ∈ Set.range T then x else T x
    refine ⟨A, B, ?_, ?_, ?_⟩
    · intro x
      apply congrArg repr
      exact Subtype.ext (target ⟨T x, x, rfl⟩)
    · intro x
      have hx : T x ∈ Set.range T := ⟨x, rfl⟩
      by_cases hm : x ∈ Set.range T
      · simp only [B, ite_eq_left hm]
      · simp only [B, ite_eq_right hm, ite_eq_left hx]
    · funext x
      change T x = (if A x ∈ Set.range T then A x else T (A x))
      split
      next hm => exact (in_image ⟨T x, x, rfl⟩ hm).symm
      next _ => exact (target ⟨T x, x, rfl⟩).symm

end IdempotentButtonCycles
