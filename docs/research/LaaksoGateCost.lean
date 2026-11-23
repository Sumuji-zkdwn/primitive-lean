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
    linarith
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


/-- Two explicit singleton gates in the interval [0,1], at 1/3 and 2/3. -/
def exampleTwoGates (k : Fin 2) (w : ℝ) : Prop :=
  if k = 0 then w = 1/3 else w = 2/3

def exampleBits : Fin 2 → Bool := fun _ => false

/-- A complete numeric Lean witness: the shortest cost to flip both bits
from the midpoint and return is 2/3. For either one-bit flip alone the
optimal cost is only 1/3, illustrating why max(single-bit costs) is not
a valid multi-bit distance formula. -/
theorem exact_two_bit_midpoint_example :
    sInf {c : ℝ |
      WeightedWalk exampleTwoGates id ((1/2 : ℝ), exampleBits)
        ((1/2 : ℝ), flipBit (flipBit exampleBits (0 : Fin 2)) (1 : Fin 2)) c}
      = (2/3 : ℝ) := by
  have h := exact_two_unique_gate_roundtrip_infimum
    exampleTwoGates id (monotone_id : Monotone (id : ℝ → ℝ))
    (1/2) (1/3) (2/3)
    (by norm_num) (by norm_num)
    exampleBits (0 : Fin 2) (1 : Fin 2)
    (by decide)
    (by simp [exampleTwoGates])
    (by simp [exampleTwoGates])
    (by
      intro w hw
      simpa [exampleTwoGates] using hw)
    (by
      intro w hw
      simpa [exampleTwoGates] using hw)
  simpa only [id_eq] using (show
    sInf {c : ℝ |
      WeightedWalk exampleTwoGates id ((1/2 : ℝ), exampleBits)
        ((1/2 : ℝ), flipBit (flipBit exampleBits (0 : Fin 2)) (1 : Fin 2)) c}
      = (2/3 : ℝ) from by
        convert h using 1 <;> norm_num)


/-- Exact one-bit cost for the left gate, matching the standard
two-gate counterexample. -/
theorem exact_left_bit_midpoint_example :
    sInf {c : ℝ |
      WeightedWalk exampleTwoGates id ((1/2 : ℝ), exampleBits)
        ((1/2 : ℝ), flipBit exampleBits (0 : Fin 2)) c}
      = (1/3 : ℝ) := by
  have h := exact_one_bit_roundtrip_infimum exampleTwoGates id
    (1/2) exampleBits (0 : Fin 2) (1/3)
    (by simp [exampleTwoGates])
    (by
      intro w hw
      have eqw : w = (1/3 : ℝ) := by
        simpa [exampleTwoGates] using hw
      subst w
      exact le_refl _)
  convert h using 1 <;> norm_num

/-- Exact one-bit cost for the right gate. -/
theorem exact_right_bit_midpoint_example :
    sInf {c : ℝ |
      WeightedWalk exampleTwoGates id ((1/2 : ℝ), exampleBits)
        ((1/2 : ℝ), flipBit exampleBits (1 : Fin 2)) c}
      = (1/3 : ℝ) := by
  have h := exact_one_bit_roundtrip_infimum exampleTwoGates id
    (1/2) exampleBits (1 : Fin 2) (2/3)
    (by simp [exampleTwoGates])
    (by
      intro w hw
      have eqw : w = (2/3 : ℝ) := by
        simpa [exampleTwoGates] using hw
      subst w
      exact le_refl _)
  convert h using 1 <;> norm_num


/-! ### A constructive sweep for an arbitrarily long list of gate flips

Unlike the previous one-bit and two-bit examples, no cardinality bound
is imposed on the event list. The explicit prerequisite is that its
gate heights are ordered from left to right. Producing such a list
from an arbitrary finite admissible bit-difference set is separate. -/

def flipEvents (b : ι → Bool) : List (ι × ℝ) → (ι → Bool)
  | [] => b
  | (k, _) :: tail => flipEvents (flipBit b k) tail

/-- A list of allowed gate events in nondecreasing height order,
starting at s, staying below right endpoint u. -/
inductive AscendingEvents (G : ι → ℝ → Prop) (u : ℝ) :
    ℝ → List (ι × ℝ) → Prop where
  | nil (s : ℝ) (hs : s ≤ u) :
      AscendingEvents G u s []
  | cons (s w : ℝ) (k : ι) (rest : List (ι × ℝ))
      (hs : s ≤ w) (hk : G k w)
      (htail : AscendingEvents G u w rest) :
      AscendingEvents G u s ((k,w)::rest)

/-- Arbitrarily many *ordered* free gate events can be realized
by a single horizontal traversal. Its cost depends only on endpoints,
not the number of flipped labels. -/
theorem ascending_events_route
    (G : ι → ℝ → Prop) (F : ℝ → ℝ) (hF : Monotone F)
    (u : ℝ) {s : ℝ} {events : List (ι × ℝ)}
    (hordered : AscendingEvents G u s events)
    (bits : ι → Bool) :
    WeightedWalk G F (s,bits) (u,flipEvents bits events) (F u - F s) := by
  induction hordered generalizing bits with
  | nil s hs =>
      have hpath : WeightedWalk G F (s,bits) (u,bits)
          (|F s - F u| + 0) :=
        WeightedWalk.horiz s u bits (u,bits) 0 (WeightedWalk.stop (u,bits))
      have hval : |F s - F u| + 0 = F u - F s := by
        rw [abs_of_nonpos (sub_nonpos.mpr (hF hs))]
        ring
      change WeightedWalk G F (s,bits) (u,flipEvents bits []) (F u - F s)
      simpa only [flipEvents, hval] using hpath
  | cons s w k rest hs hk htail ih =>
      have htailwalk := ih (bits := flipBit bits k)
      have hgate : WeightedWalk G F (w,bits)
          (u,flipEvents (flipBit bits k) rest) (F u - F w) :=
        WeightedWalk.gate w bits k _ _ hk htailwalk
      have hpath : WeightedWalk G F (s,bits)
          (u,flipEvents bits ((k,w)::rest))
          (|F s - F w| + (F u - F w)) :=
        WeightedWalk.horiz s w bits _ _ hgate
      have hval : |F s - F w| + (F u - F w) = F u - F s := by
        rw [abs_of_nonpos (sub_nonpos.mpr (hF hs))]
        ring
      rw [← hval]
      exact hpath

/-- Concatenating two legal costed walks adds their exact costs. -/
theorem weighted_walk_append
    (G : ι → ℝ → Prop) (F : ℝ → ℝ)
    {x y z : State ι} {c d : ℝ}
    (hxy : WeightedWalk G F x y c)
    (hyz : WeightedWalk G F y z d) :
    WeightedWalk G F x z (c + d) := by
  induction hxy with
  | stop x =>
      simpa only [zero_add] using hyz
  | horiz s t bits z c tail ih =>
      have h := WeightedWalk.horiz s t bits _ _ ih
      simpa only [add_assoc] using h
  | gate s bits k z c hk tail ih =>
      exact WeightedWalk.gate s bits k _ _ hk ih

/-- For s ≤ t, the full left-right sweep of ANY finite number of
sorted gate events achieves the exact interval normal-form cost.
This is the constructive half of the arbitrary-bit path formula. -/
theorem ascending_sweep_upper
    (G : ι → ℝ → Prop) (F : ℝ → ℝ) (hF : Monotone F)
    (l s t u : ℝ) (hl : l ≤ s) (hst : s ≤ t) (hu : t ≤ u)
    (bits : ι → Bool) (events : List (ι × ℝ))
    (hordered : AscendingEvents G u l events) :
    WeightedWalk G F (s,bits) (t,flipEvents bits events)
      (2*(F u - F l) - |F s - F t|) := by
  let b2 := flipEvents bits events
  have hroute : WeightedWalk G F (l,bits) (u,b2) (F u - F l) := by
    exact ascending_events_route G F hF u hordered bits
  have hlast : WeightedWalk G F (u,b2) (t,b2) (|F u - F t|) := by
    simpa only [add_zero] using
      (WeightedWalk.horiz u t b2 (t,b2) 0 (WeightedWalk.stop (t,b2)))
  have hmiddle : WeightedWalk G F (l,bits) (t,b2)
      ((F u - F l) + |F u - F t|) :=
    weighted_walk_append G F hroute hlast
  have hstart : WeightedWalk G F (s,bits) (t,b2)
      (|F s - F l| + ((F u - F l) + |F u - F t|)) :=
    WeightedWalk.horiz s l bits (t,b2) _ hmiddle
  have hval : |F s - F l| + ((F u - F l) + |F u - F t|) =
      2*(F u - F l) - |F s - F t| := by
    have hls := hF hl
    have hst := hF hst
    have htu := hF hu
    rw [abs_of_nonneg (sub_nonneg.mpr hls),
        abs_of_nonneg (sub_nonneg.mpr htu),
        abs_of_nonpos (sub_nonpos.mpr hst)]
    ring
  change WeightedWalk G F (s,bits) (t,b2)
    (2*(F u - F l) - |F s - F t|)
  rw [← hval]
  exact hstart


/-! ### Lower sweep inequality for ANY number of changed bits

The proof computes an interval containing all heights visited by a
finite walk, without assuming that the bit index type is finite. The
interval has the gate-admissibility property for *all* changed labels
and its sweep cost is at most the actual total walk cost. -/

/-- Elementary total-variation update: adding one endpoint a to a
path whose visited values lie between L and U does not underpay the
sweep of the enlarged interval. This is a pure real inequality. -/
private theorem extend_sweep_variation
    (a b c L U : ℝ)
    (hLb : L ≤ b) (hbU : b ≤ U)
    (hLc : L ≤ c) (hcU : c ≤ U) :
    2*(max a U - min a L) - |a-c| ≤
      |a-b| + (2*(U-L) - |b-c|) := by
  have hLU : L ≤ U := hLb.trans hbU
  by_cases haL : a ≤ L
  · have haU : a ≤ U := haL.trans hLU
    rw [max_eq_right haU, min_eq_left haL]
    have hba : |a-b| = b-a := abs_of_nonpos (sub_nonpos.mpr (haL.trans hLb))
    have hca : |a-c| = c-a := abs_of_nonpos (sub_nonpos.mpr (haL.trans hLc))
    have hbclow : |b-c| ≤ b+c-2*L := by
      apply abs_le.mpr
      constructor <;> linarith
    rw [hba, hca]
    linarith
  · have hLa : L ≤ a := le_of_not_ge haL
    by_cases haU : a ≤ U
    · rw [max_eq_right haU, min_eq_right hLa]
      have htri : |b-c| ≤ |a-b| + |a-c| := by
        calc
          |b-c| = |(b-a)+(a-c)| := by congr 1 <;> ring
          _ ≤ |b-a| + |a-c| := abs_add_le _ _
          _ = |a-b| + |a-c| := by rw [abs_sub_comm b a]
      linarith
    · have hUa : U ≤ a := le_of_not_ge haU
      rw [max_eq_left hUa, min_eq_right hLa]
      have hab : |a-b| = a-b := abs_of_nonneg (sub_nonneg.mpr (hbU.trans hUa))
      have hac : |a-c| = a-c := abs_of_nonneg (sub_nonneg.mpr (hcU.trans hUa))
      have hbc : |b-c| ≤ 2*U-b-c := by
        apply abs_le.mpr
        constructor <;> linarith
      rw [hab, hac]
      linarith

/-- Every finite legal costed walk admits an interval [l,u]
containing both endpoints and at least one actual gate of every
bit changed between its endpoints; the walk pays at least the exact
sweep cost of that interval. No number-of-bits assumption. -/
theorem arbitrary_multibit_sweep_lower
    (G : ι → ℝ → Prop) (F : ℝ → ℝ) (hF : Monotone F)
    {x y : State ι} {c : ℝ} (walk : WeightedWalk G F x y c) :
    ∃ l u : ℝ,
      l ≤ x.1 ∧ x.1 ≤ u ∧ l ≤ y.1 ∧ y.1 ≤ u ∧
      (∀ k, x.2 k ≠ y.2 k →
        ∃ w : ℝ, l ≤ w ∧ w ≤ u ∧ G k w) ∧
      2*(F u-F l) - |F x.1-F y.1| ≤ c := by
  induction walk with
  | stop x =>
      refine ⟨x.1,x.1,le_refl _,le_refl _,le_refl _,le_refl _,?_,?_⟩
      · intro k hdiff
        exact False.elim (hdiff rfl)
      · simp
  | horiz s t bits z c tail ih =>
      obtain ⟨l,u,hlt,htu,hlz,hzu,hgates,hcost⟩ := ih
      let l' : ℝ := min s l
      let u' : ℝ := max s u
      have hls : l' ≤ s := min_le_left _ _
      have hsu : s ≤ u' := le_max_left _ _
      have hlz' : l' ≤ z.1 := (min_le_right s l).trans hlz
      have hzu' : z.1 ≤ u' := hzu.trans (le_max_right s u)
      refine ⟨l',u',hls,hsu,hlz',hzu',?_,?_⟩
      · intro k hdiff
        obtain ⟨w,hwlow,hwhigh,hg⟩ := hgates k hdiff
        exact ⟨w,(min_le_right s l).trans hwlow,
          hwhigh.trans (le_max_right s u),hg⟩
      · have hFmin : F (min s l) = min (F s) (F l) := by
          by_cases hs : s ≤ l
          · rw [min_eq_left hs, min_eq_left (hF hs)]
          · have hs' : l ≤ s := le_of_not_ge hs
            rw [min_eq_right hs', min_eq_right (hF hs')]
        have hFmax : F (max s u) = max (F s) (F u) := by
          by_cases hs : s ≤ u
          · rw [max_eq_right hs, max_eq_right (hF hs)]
          · have hs' : u ≤ s := le_of_not_ge hs
            rw [max_eq_left hs', max_eq_left (hF hs')]
        have hex := extend_sweep_variation
          (F s) (F t) (F z.1) (F l) (F u)
          (hF hlt) (hF htu) (hF hlz) (hF hzu)
        change 2*(F (max s u)-F (min s l)) - |F s-F z.1| ≤
          |F s-F t|+c
        rw [hFmax,hFmin]
        linarith
  | gate s bits k z c hk tail ih =>
      obtain ⟨l,u,hls,hsu,hlz,hzu,hgates,hcost⟩ := ih
      refine ⟨l,u,hls,hsu,hlz,hzu,?_,?_⟩
      · intro i hdiff
        by_cases hik : i = k
        · exact ⟨s,hls,hsu,by simpa [hik] using hk⟩
        · have hkeep : flipBit bits k i = bits i := by
            simp [flipBit, hik]
          exact hgates i (by simpa only [hkeep] using hdiff)
      · simpa using hcost

#print axioms arbitrary_multibit_sweep_lower


#print axioms ascending_events_route
#print axioms weighted_walk_append
#print axioms ascending_sweep_upper


#print axioms exact_left_bit_midpoint_example
#print axioms exact_right_bit_midpoint_example
#print axioms exact_two_bit_midpoint_example

#print axioms two_gate_sweep_realizable
#print axioms exact_two_unique_gate_roundtrip_infimum

#print axioms one_bit_detour_realizable
#print axioms exact_one_bit_roundtrip_infimum

#print axioms height_displacement_le_cost
#print axioms changed_bit_detour_lower
#print axioms roundtrip_changed_bit_lower
#print axioms roundtrip_lower_of_gate_separation

end LaaksoGateCost
