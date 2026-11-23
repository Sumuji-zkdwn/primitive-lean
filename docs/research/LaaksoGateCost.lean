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


/-- A concrete route goes from s to a chosen k-gate w, flips the k-bit,
and goes on to t. It uses exactly two horizontal legs, so its total
cost is the desired detour upper bound. -/
theorem one_bit_detour_realizable
    (G : ι → ℝ → Prop) (F : ℝ → ℝ)
    (s t : ℝ) (b : ι → Bool) (k : ι) (w : ℝ)
    (hw : G k w) :
    WeightedWalk G F (s,b) (t,flipBit b k)
      (|F s - F w| + |F w - F t|) := by
  have hfinish :
      WeightedWalk G F (w,flipBit b k) (t,flipBit b k)
        (|F w - F t|) := by
    simpa only [add_zero] using
      (WeightedWalk.horiz w t (flipBit b k)
        (t,flipBit b k) 0 (WeightedWalk.stop (t,flipBit b k)))
  have hflip :
      WeightedWalk G F (w,b) (t,flipBit b k)
        (|F w - F t|) :=
    WeightedWalk.gate w b k (t,flipBit b k)
      (|F w - F t|) hw hfinish
  exact WeightedWalk.horiz s w b (t,flipBit b k)
    (|F w - F t|) hflip

/-- Sharp one-bit roundtrip cost for a chosen nearest calibrated gate.
Other-bit flips and arbitrary detours cannot reduce the infimum. -/
theorem exact_one_bit_roundtrip_infimum
    (G : ι → ℝ → Prop) (F : ℝ → ℝ)
    (s : ℝ) (b : ι → Bool) (k : ι) (w₀ : ℝ)
    (hw₀ : G k w₀)
    (hnearest : ∀ w : ℝ, G k w →
      |F s - F w₀| ≤ |F s - F w|) :
    sInf {c : ℝ | WeightedWalk G F (s,b) (s,flipBit b k) c} =
      2 * |F s - F w₀| := by
  let S : Set ℝ := {c | WeightedWalk G F (s,b) (s,flipBit b k) c}
  have hdiff : b k ≠ flipBit b k k := by
    simp [flipBit]
  have hlow : ∀ c ∈ S, 2 * |F s - F w₀| ≤ c := by
    intro c hc
    obtain ⟨w, hw, hcost⟩ :=
      roundtrip_changed_bit_lower G F hc k hdiff rfl
    have hmin := hnearest w hw
    linarith
  have hwitness : 2 * |F s - F w₀| ∈ S := by
    have hr := one_bit_detour_realizable G F s s b k w₀ hw₀
    have hval :
        |F s - F w₀| + |F w₀ - F s| =
          2 * |F s - F w₀| := by
      rw [abs_sub_comm (F w₀) (F s)]
      ring
    change WeightedWalk G F (s,b) (s,flipBit b k)
      (2 * |F s - F w₀|)
    rw [← hval]
    exact hr
  have hS : S.Nonempty := ⟨_, hwitness⟩
  have hbdd : BddBelow S := ⟨_, hlow⟩
  change sInf S = 2 * |F s - F w₀|
  apply le_antisymm
  · exact csInf_le hbdd hwitness
  · exact le_csInf hS hlow

#print axioms one_bit_detour_realizable
#print axioms exact_one_bit_roundtrip_infimum

#print axioms height_displacement_le_cost
#print axioms changed_bit_detour_lower
#print axioms roundtrip_changed_bit_lower
#print axioms roundtrip_lower_of_gate_separation

end LaaksoGateCost
