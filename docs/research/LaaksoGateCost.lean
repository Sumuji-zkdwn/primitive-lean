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
      change |F t - F z.1| ≤ c at ih
      change |F s - F z.1| ≤ |F s - F t| + c
      calc
        |F s - F z.1| =
            |(F s - F t) + (F t - F z.1)| := by
              congr 1
              ring
        _ ≤ |F s - F t| + |F t - F z.1| := abs_add_le _ _
        _ ≤ |F s - F t| + c := by linarith
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


/-- If an entire walk travels via a point b in the calibrated real line,
the sum of the two legs and the direct displacement dominates twice
the distance to b. -/
private theorem via_point_twice (a b c total : ℝ)
    (h : |a - b| + |b - c| ≤ total) :
    2 * |a - b| ≤ total + |a - c| := by
  have ht : |a - b| ≤ |a - c| + |c - b| := by
    calc
      |a - b| = |(a - c) + (c - b)| := by congr 1 <;> ring
      _ ≤ |a - c| + |c - b| := abs_add_le _ _
  rw [abs_sub_comm c b] at ht
  linarith

/-- The first genuine two-bit lower bound. Every finite walk that changes
two distinct bits must visit one gate for each. The total horizontal
variation, plus the start-to-end calibrated displacement, is at least
twice the separation between these two actual visited gate heights.

Crucially, this cannot be inferred by taking the maximum of two
single-bit detour bounds. The proof follows the *first occurrence*
of either bit and then uses the remaining other-bit detour.
-/
theorem two_changed_bits_span_lower
    (G : ι → ℝ → Prop) (F : ℝ → ℝ)
    {x y : State ι} {c : ℝ}
    (walk : WeightedWalk G F x y c)
    (i j : ι) (hij : i ≠ j)
    (hi : x.2 i ≠ y.2 i) (hj : x.2 j ≠ y.2 j) :
    ∃ u v : ℝ, G i u ∧ G j v ∧
      2 * |F u - F v| ≤ c + |F x.1 - F y.1| := by
  induction walk with
  | stop x =>
      exact False.elim (hi rfl)
  | horiz s t b z c tail ih =>
      obtain ⟨u, v, hu, hv, hbound⟩ := ih hi hj
      refine ⟨u, v, hu, hv, ?_⟩
      change 2 * |F u - F v| ≤
        (|F s - F t| + c) + |F s - F z.1|
      have ht : |F t - F z.1| ≤
          |F s - F t| + |F s - F z.1| := by
        calc
          |F t - F z.1| = |(F t - F s) + (F s - F z.1)| := by
            congr 1
            ring
          _ ≤ |F t - F s| + |F s - F z.1| := abs_add_le _ _
          _ = |F s - F t| + |F s - F z.1| := by
            rw [abs_sub_comm (F t) (F s)]
      linarith
  | gate s b k z c hk tail ih =>
      by_cases hki : k = i
      · have hjk : j ≠ k := by simpa [hki] using hij.symm
        have hjtail : (flipBit b k) j ≠ z.2 j := by
          simpa [flipBit, hjk] using hj
        obtain ⟨v, hv, hcost⟩ :=
          changed_bit_detour_lower G F tail j hjtail
        refine ⟨s, v, by simpa [hki] using hk, hv, ?_⟩
        change 2 * |F s - F v| ≤ c + |F s - F z.1|
        exact via_point_twice (F s) (F v) (F z.1) c hcost
      · by_cases hkj : k = j
        · have hik : i ≠ k := by simpa [hkj] using hij
          have hitail : (flipBit b k) i ≠ z.2 i := by
            simpa [flipBit, hik] using hi
          obtain ⟨u, hu, hcost⟩ :=
            changed_bit_detour_lower G F tail i hitail
          refine ⟨u, s, hu, by simpa [hkj] using hk, ?_⟩
          change 2 * |F u - F s| ≤ c + |F s - F z.1|
          have hv := via_point_twice (F s) (F u) (F z.1) c hcost
          rwa [abs_sub_comm (F u) (F s)]
        · have hik : i ≠ k := Ne.symm hki
          have hjk : j ≠ k := Ne.symm hkj
          have hitail : (flipBit b k) i ≠ z.2 i := by
            simpa [flipBit, hik] using hi
          have hjtail : (flipBit b k) j ≠ z.2 j := by
            simpa [flipBit, hjk] using hj
          simpa using ih hitail hjtail

#print axioms two_changed_bits_span_lower


/-- Two prescribed gate visits (first i, then j) admit a concrete
three-leg horizontal walk with exactly the displayed cost. -/
theorem two_gate_sweep_realizable
    (G : ι → ℝ → Prop) (F : ℝ → ℝ)
    (s t : ℝ) (b : ι → Bool) (i j : ι)
    (u v : ℝ) (hui : G i u) (hvj : G j v) :
    WeightedWalk G F (s,b) (t,flipBit (flipBit b i) j)
      (|F s - F u| + |F u - F v| + |F v - F t|) := by
  let b1 := flipBit b i
  let b2 := flipBit b1 j
  have hlast : WeightedWalk G F (v,b2) (t,b2)
      (|F v - F t|) := by
    simpa only [add_zero] using
      (WeightedWalk.horiz v t b2 (t,b2) 0 (WeightedWalk.stop (t,b2)))
  have hj : WeightedWalk G F (v,b1) (t,b2)
      (|F v - F t|) :=
    WeightedWalk.gate v b1 j (t,b2) (|F v - F t|) hvj hlast
  have hmiddle : WeightedWalk G F (u,b1) (t,b2)
      (|F u - F v| + |F v - F t|) :=
    WeightedWalk.horiz u v b1 (t,b2) (|F v - F t|) hj
  have hi : WeightedWalk G F (u,b) (t,b2)
      (|F u - F v| + |F v - F t|) :=
    WeightedWalk.gate u b i (t,b2) _ hui hmiddle
  have hstart : WeightedWalk G F (s,b) (t,b2)
      (|F s - F u| + (|F u - F v| + |F v - F t|)) :=
    WeightedWalk.horiz s u b (t,b2) _ hi
  simpa only [b1,b2, add_assoc] using hstart

/-- For distinct i,j with respective *unique* gates at a<b and
s between them, the exact roundtrip cost to change both bits is the
full left-to-right excursion 2*(F b-F a). This is the first
multi-bit equality certified on all finite legal costed walks. -/
theorem exact_two_unique_gate_roundtrip_infimum
    (G : ι → ℝ → Prop) (F : ℝ → ℝ) (hF : Monotone F)
    (s a b : ℝ) (has : a ≤ s) (hsb : s ≤ b)
    (bits : ι → Bool) (i j : ι) (hij : i ≠ j)
    (ha : G i a) (hb : G j b)
    (huni : ∀ w, G i w → w = a)
    (hunj : ∀ w, G j w → w = b) :
    sInf {c : ℝ |
      WeightedWalk G F (s,bits)
        (s,flipBit (flipBit bits i) j) c} =
      2 * (F b - F a) := by
  let bits2 := flipBit (flipBit bits i) j
  let S : Set ℝ :=
    {c | WeightedWalk G F (s,bits) (s,bits2) c}
  have hdiffi : bits i ≠ bits2 i := by
    simp [bits2, flipBit, hij, hij.symm]
  have hdiffj : bits j ≠ bits2 j := by
    simp [bits2, flipBit, hij, hij.symm]
  have hFa : F a ≤ F s := hF has
  have hFb : F s ≤ F b := hF hsb
  have hFab : F a ≤ F b := le_trans hFa hFb
  have hlow : ∀ c ∈ S, 2 * (F b - F a) ≤ c := by
    intro c hc
    obtain ⟨u,v,hu,hv,hbound⟩ :=
      two_changed_bits_span_lower G F hc i j hij hdiffi hdiffj
    have hua : u = a := huni u hu
    have hvb : v = b := hunj v hv
    subst u
    subst v
    change 2 * |F a - F b| ≤ c + |F s - F s| at hbound
    rw [abs_of_nonpos (sub_nonpos.mpr hFab)] at hbound
    simp only [sub_self, abs_zero, add_zero] at hbound
    exact hbound
  have hcost :
      |F s - F a| + |F a - F b| + |F b - F s| =
        2 * (F b - F a) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hFa),
        abs_of_nonpos (sub_nonpos.mpr hFab),
        abs_of_nonneg (sub_nonneg.mpr hFb)]
    ring
  have hwitness : 2 * (F b - F a) ∈ S := by
    have hw := two_gate_sweep_realizable G F s s bits i j a b ha hb
    change WeightedWalk G F (s,bits) (s,bits2)
      (2 * (F b - F a))
    rw [← hcost]
    exact hw
  have hne : S.Nonempty := ⟨_, hwitness⟩
  have hbounded : BddBelow S := ⟨_, hlow⟩
  change sInf S = 2 * (F b - F a)
  apply le_antisymm
  · exact csInf_le hbounded hwitness
  · exact le_csInf hne hlow

#print axioms two_gate_sweep_realizable
#print axioms exact_two_unique_gate_roundtrip_infimum

#print axioms one_bit_detour_realizable
#print axioms exact_one_bit_roundtrip_infimum

#print axioms height_displacement_le_cost
#print axioms changed_bit_detour_lower
#print axioms roundtrip_changed_bit_lower
#print axioms roundtrip_lower_of_gate_separation

end LaaksoGateCost
