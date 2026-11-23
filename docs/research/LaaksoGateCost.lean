import Mathlib.Tactic

/-!
# A quantitative gate-crossing lower bound for arbitrary finite walks

A step of the finite graph either changes height without changing bits
and costs |F(s)-F(t)|, or flips one bit at its allowed gate at cost 0.
All walks use finitely many steps, but the bit index type may be arbitrary.

Unlike the earlier Boolean-only necessity lemma, this file proves a
positive lower bound on the cost of *any* legal walk that changes a bit.
It is an exact soundness theorem, not a claim of geodesic existence or
the converse optimal construction for several bits.
-/

namespace LaaksoGateCost

universe u
variable {ι : Type u} [DecidableEq ι]

abbrev State (ι : Type u) := ℝ × (ι → Bool)

def flipBit (b : ι → Bool) (k : ι) : ι → Bool :=
  fun i => if i = k then !(b i) else b i

/-- Legal costed walks; horizontal steps may be in either direction. -/
inductive WeightedWalk (G : ι → ℝ → Prop) (F : ℝ → ℝ) :
    State ι → State ι → ℝ → Prop where
  | stop (x : State ι) : WeightedWalk G F x x 0
  | horiz (s t : ℝ) (b : ι → Bool) (z : State ι) (c : ℝ)
      (tail : WeightedWalk G F (t,b) z c) :
      WeightedWalk G F (s,b) z (|F s - F t| + c)
  | gate (s : ℝ) (b : ι → Bool) (k : ι)
      (z : State ι) (c : ℝ)
      (hk : G k s) (tail : WeightedWalk G F (s,flipBit b k) z c) :
      WeightedWalk G F (s,b) z c

/-- Every legal walk costs at least the absolute displacement of its
calibrated height, without any monotonicity assumption on F. -/
theorem height_displacement_le_cost
    (G : ι → ℝ → Prop) (F : ℝ → ℝ)
    {x y : State ι} {c : ℝ}
    (walk : WeightedWalk G F x y c) :
    |F x.1 - F y.1| ≤ c := by
  induction walk with
  | stop x =>
      simp
  | horiz s t b z c tail ih =>
      change |F s - F z.1| ≤ |F s - F t| + c
      calc
        |F s - F z.1| =
            |(F s - F t) + (F t - F z.1)| := by
              congr 1
              ring
        _ ≤ |F s - F t| + |F t - F z.1| := abs_add_le _ _
        _ ≤ |F s - F t| + c := add_le_add_left ih _
  | gate s b k z c hk tail ih =>
      simpa using ih

/-- If bit i changes, *some actual i-gate* w is visited, and the
whole walk has cost at least the detour from start to w to finish. -/
theorem changed_bit_detour_lower
    (G : ι → ℝ → Prop) (F : ℝ → ℝ)
    {x y : State ι} {c : ℝ}
    (walk : WeightedWalk G F x y c)
    (i : ι) (hdiff : x.2 i ≠ y.2 i) :
    ∃ w : ℝ, G i w ∧
      |F x.1 - F w| + |F w - F y.1| ≤ c := by
  induction walk with
  | stop x =>
      exact False.elim (hdiff rfl)
  | horiz s t b z c tail ih =>
      obtain ⟨w, hw, hcost⟩ := ih hdiff
      refine ⟨w, hw, ?_⟩
      change |F s - F w| + |F w - F z.1| ≤ |F s - F t| + c
      have htri : |F s - F w| ≤ |F s - F t| + |F t - F w| := by
        calc
          |F s - F w| = |(F s - F t) + (F t - F w)| := by
            congr 1
            ring
          _ ≤ |F s - F t| + |F t - F w| := abs_add_le _ _
      linarith
  | gate s b k z c hk tail ih =>
      by_cases hi : i = k
      · refine ⟨s, ?_, ?_⟩
        · simpa [hi] using hk
        · have hheight := height_displacement_le_cost G F tail
          change |F s - F s| + |F s - F z.1| ≤ c
          simpa using hheight
      · have hsame : flipBit b k i = b i := by
          simp [flipBit, hi]
        obtain ⟨w, hw, hcost⟩ := ih (by simpa only [hsame] using hdiff)
        exact ⟨w, hw, hcost⟩

/-- A round trip that changes a bit must reach an allowed gate and return.
This is the lower bound needed for sharp finite observation-fibre diameters. -/
theorem roundtrip_changed_bit_lower
    (G : ι → ℝ → Prop) (F : ℝ → ℝ)
    {x y : State ι} {c : ℝ}
    (walk : WeightedWalk G F x y c)
    (i : ι) (hdiff : x.2 i ≠ y.2 i)
    (hsame : x.1 = y.1) :
    ∃ w : ℝ, G i w ∧ 2 * |F x.1 - F w| ≤ c := by
  obtain ⟨w, hw, hcost⟩ := changed_bit_detour_lower G F walk i hdiff
  refine ⟨w, hw, ?_⟩
  have heq : F x.1 = F y.1 := congrArg F hsame
  rw [← heq, abs_sub_comm (F w) (F x.1)] at hcost
  linarith

/-- Uniform gate separation yields a uniform lower bound on every
round-trip walk; no minimizing path is assumed to exist. -/
theorem roundtrip_lower_of_gate_separation
    (G : ι → ℝ → Prop) (F : ℝ → ℝ)
    {x y : State ι} {c δ : ℝ}
    (walk : WeightedWalk G F x y c)
    (i : ι) (hdiff : x.2 i ≠ y.2 i)
    (hsame : x.1 = y.1)
    (hsep : ∀ w : ℝ, G i w → δ ≤ |F x.1 - F w|) :
    2 * δ ≤ c := by
  obtain ⟨w, hw, hbound⟩ :=
    roundtrip_changed_bit_lower G F walk i hdiff hsame
  have hδ := hsep w hw
  linarith

#print axioms height_displacement_le_cost
#print axioms changed_bit_detour_lower
#print axioms roundtrip_changed_bit_lower
#print axioms roundtrip_lower_of_gate_separation

end LaaksoGateCost
