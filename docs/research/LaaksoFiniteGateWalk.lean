import Mathlib.Tactic

/-!
# The finite gate necessity lemma: one changed bit forces a gate visit

States carry a real height and a Boolean vector. The only moves are
horizontal motion without changing bits, and a free toggle of a single
bit at an allowed gate. Every move remains within [l,u].

This proves the first model-specific direction needed to identify graph
walks with admissible gate intervals. It does NOT assert that the
continuous inverse-limit distance is already characterized by these walks.
-/

namespace LaaksoFiniteGateWalk

universe u

variable {ι : Type u} [DecidableEq ι]

abbrev State (ι : Type u) := ℝ × (ι → Bool)

def flipBit (b : ι → Bool) (k : ι) : ι → Bool :=
  fun i => if i = k then !(b i) else b i

@[simp] theorem flipBit_same (b : ι → Bool) (k : ι) :
    flipBit b k k = !(b k) := by
  simp [flipBit]

theorem flipBit_other (b : ι → Bool) (k i : ι) (h : i ≠ k) :
    flipBit b k i = b i := by
  simp [flipBit, h]

/-- Walk on a finite-indexed gate system. Each intermediate height is
contained in [l,u]. The gate restriction is an *actual premise* of flip. -/
inductive Walk (G : ι → ℝ → Prop) (l u : ℝ) :
    State ι → State ι → Prop where
  | stop (x : State ι) (hl : l ≤ x.1) (hu : x.1 ≤ u) :
      Walk G l u x x
  | horizontal (s t : ℝ) (b : ι → Bool) (z : State ι)
      (hls : l ≤ s) (hsu : s ≤ u)
      (hlt : l ≤ t) (htu : t ≤ u)
      (tail : Walk G l u (t,b) z) :
      Walk G l u (s,b) z
  | gate (s : ℝ) (b : ι → Bool) (k : ι) (z : State ι)
      (hls : l ≤ s) (hsu : s ≤ u) (hk : G k s)
      (tail : Walk G l u (s,flipBit b k) z) :
      Walk G l u (s,b) z

/-- If a bit differs at the start and end, the walk must have visited
a gate for that bit. No finite-search or unspecified transition axiom. -/
theorem differing_bit_requires_gate
    (G : ι → ℝ → Prop) (l u : ℝ)
    {x y : State ι} (walk : Walk G l u x y)
    (i : ι) (hdiff : x.2 i ≠ y.2 i) :
    ∃ s : ℝ, l ≤ s ∧ s ≤ u ∧ G i s := by
  induction walk with
  | stop x hl hu =>
      exact False.elim (hdiff rfl)
  | horizontal s t b z hls hsu hlt htu tail ih =>
      exact ih hdiff
  | gate s b k z hls hsu hk tail ih =>
      by_cases hi : i = k
      · refine ⟨s, hls, hsu, ?_⟩
        simpa [hi] using hk
      · have heq : flipBit b k i = b i := flipBit_other b k i hi
        apply ih
        simpa only [heq] using hdiff

/-- The interval visited by any legal finite walk contains a usable
gate for every label on which the initial and final states differ. -/
theorem path_interval_admissible
    (G : ι → ℝ → Prop) (l u : ℝ)
    {x y : State ι} (walk : Walk G l u x y) :
    ∀ i : ι, x.2 i ≠ y.2 i →
      ∃ s : ℝ, l ≤ s ∧ s ≤ u ∧ G i s := by
  intro i h
  exact differing_bit_requires_gate G l u walk i h

#print axioms differing_bit_requires_gate
#print axioms path_interval_admissible

end LaaksoFiniteGateWalk
