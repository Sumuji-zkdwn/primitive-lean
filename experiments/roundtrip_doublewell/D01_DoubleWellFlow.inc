/-!
# The GPT-side flow in the double-well regime `λ > 0 > r`

Flow (baseline `LinearInputRegularBand.IsTrajectory`):
`x' = -γ e gx - b gy`, `y' = -γ e gy + b gx`, `e = E - T`.
Neither the GPT probe (which used `r = 1 > 0`) nor rounds R01–R13 ran this flow for `r < 0`.
Everything here depends only on the initial baseline and on R03/R04.
-/

noncomputable section
namespace RoundTripDoubleWell
open Real Set LinearInputDesign LinearInputGradient LinearInputRegularBand

/-! ## A. Stationary points of the flow = cusp equilibrium surface (∪ target shell) -/

theorem field_norm_sq (lam r u gamma T b x y : ℝ) :
    (-gamma * (E lam r u x y - T) * gx lam r u x y - b * gy x y) ^ 2 +
      (-gamma * (E lam r u x y - T) * gy x y + b * gx lam r u x y) ^ 2 =
    (gamma ^ 2 * (E lam r u x y - T) ^ 2 + b ^ 2) * gSq lam r u x y := by
  unfold gSq; ring

/-- With circulation `b ≠ 0`, the flow is at rest exactly on R03's equilibrium surface. -/
theorem rest_iff_of_b_ne {b : ℝ} (hb : b ≠ 0) (lam r u gamma T x y : ℝ) :
    ((-gamma * (E lam r u x y - T) * gx lam r u x y - b * gy x y) = 0 ∧
      (-gamma * (E lam r u x y - T) * gy x y + b * gx lam r u x y) = 0) ↔
      y = Real.sqrt 2 * x ∧ u = input lam r x := by
  have hcoef : 0 < gamma ^ 2 * (E lam r u x y - T) ^ 2 + b ^ 2 := by positivity
  have key : gx lam r u x y = 0 ∧ gy x y = 0 ↔ y = Real.sqrt 2 * x ∧ u = input lam r x := by
    rw [stationary_iff]; unfold input; rfl
  rw [← key]
  constructor
  · rintro ⟨h1, h2⟩
    have hn := field_norm_sq lam r u gamma T b x y
    rw [h1, h2] at hn
    have hz : (gamma ^ 2 * (E lam r u x y - T) ^ 2 + b ^ 2) * gSq lam r u x y = 0 := by
      rw [← hn]; ring
    have hg : gSq lam r u x y = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hcoef.ne'
      · exact h
    exact (gSq_eq_zero_iff lam r u x y).1 hg
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; ring_nf; simp

/-- Energy of a rest point: the baseline critical value. -/
theorem rest_energy {lam r u x y : ℝ} (hy : y = Real.sqrt 2 * x) (hu : u = input lam r x) :
    E lam r u x y = -3 * lam * x ^ 4 / 4 - r * x ^ 2 / 2 := by
  subst hy hu
  unfold E f input
  ring

/-- Constant trajectories at rest points, for every `γ`, target `T` and circulation `b`. -/
theorem const_isTrajectory {lam r u gamma T x₀ y₀ : ℝ} (b : ℝ → ℝ)
    (hy : y₀ = Real.sqrt 2 * x₀) (hu : u = input lam r x₀) :
    IsTrajectory lam r u gamma T (fun _ => x₀) (fun _ => y₀) b := by
  have hg : gx lam r u x₀ y₀ = 0 ∧ gy x₀ y₀ = 0 := by
    rw [stationary_iff]; unfold input at hu; exact ⟨hy, hu⟩
  intro t _
  refine ⟨?_, ?_⟩ <;> simpa [hg.1, hg.2] using hasDerivAt_const t _

/-- Without the band hypothesis the target is not reached: for `λ > 0 > r`, `u = 0`, the
saddle `(0,0)` and the well bottom `(a₀, √2 a₀)` are trajectories whose energy gap stays
`-T` and `-r²/(4λ) - T`. -/
theorem stuck_at_saddle_and_well {lam r : ℝ} (hlam : 0 < lam) (hr : r < 0)
    (gamma T : ℝ) (b : ℝ → ℝ) :
    let a := Real.sqrt (-r / lam)
    IsTrajectory lam r 0 gamma T (fun _ => 0) (fun _ => 0) b ∧
      E lam r 0 0 0 - T = -T ∧
      IsTrajectory lam r 0 gamma T (fun _ => a) (fun _ => Real.sqrt 2 * a) b ∧
      E lam r 0 a (Real.sqrt 2 * a) - T = -r ^ 2 / (4 * lam) - T := by
  intro a
  have hq : 0 < -r / lam := div_pos (neg_pos.mpr hr) hlam
  have ha2 : a ^ 2 = -r / lam := Real.sq_sqrt hq.le
  have hin : (0 : ℝ) = input lam r a := by
    rw [RoundTrip03.input_eq_mul_margin, ha2]; field_simp; ring
  refine ⟨const_isTrajectory b (by simp) (by simp [input]), by simp [E, f],
    const_isTrajectory b rfl hin, ?_⟩
  rw [rest_energy rfl hin, show a ^ 4 = (a ^ 2) ^ 2 by ring, ha2]
  field_simp
  ring

/-! ## B. Energy stays between its start and the target (baseline `energy_gap_exact`) -/

theorem energy_between {lam r u gamma T : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r u gamma T x y b) (hgamma : 0 ≤ gamma) {t : ℝ} (ht : 0 ≤ t) :
    min (E lam r u (x 0) (y 0)) T ≤ E lam r u (x t) (y t) ∧
      E lam r u (x t) (y t) ≤ max (E lam r u (x 0) (y 0)) T := by
  have h := LinearInputStrictEnergy.energy_gap_exact htraj ht
  set k := Real.exp (-gamma * (∫ s in 0..t, gSq lam r u (x s) (y s)))
  have hI : 0 ≤ ∫ s in 0..t, gSq lam r u (x s) (y s) :=
    intervalIntegral.integral_nonneg ht (fun s _ => gSq_nonneg lam r u _ _)
  have hk0 : 0 < k := Real.exp_pos _
  have hk1 : k ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set e0 := E lam r u (x 0) (y 0) - T
  have hE : E lam r u (x t) (y t) = T + e0 * k := by linarith
  rw [hE]
  rcases le_total 0 e0 with h0 | h0
  · constructor
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact (show T + e0 * k ≤ E lam r u (x 0) (y 0) by nlinarith).trans (le_max_left _ _)
  · constructor
    · exact (min_le_left _ _).trans (by nlinarith)
    · exact (show T + e0 * k ≤ T by nlinarith).trans (le_max_right _ _)

/-! ## C. Barriers, confinement and trapping (any `u`) -/

/-- Along the vertical line `x = c` the energy is at least the scalar potential value `f(c)`. -/
theorem barrier (lam r u c y : ℝ) : f lam r u c ≤ E lam r u c y := by
  unfold E; nlinarith [sq_nonneg (y - Real.sqrt 2 * c)]

/-- Confinement: if start and target lie below the barrier `f(c)`, the trajectory never
crosses the line `x = c`. -/
theorem confined {lam r u gamma T c : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r u gamma T x y b) (hgamma : 0 ≤ gamma)
    (hbar : max (E lam r u (x 0) (y 0)) T < f lam r u c) (hx0 : x 0 < c) :
    ∀ t, 0 ≤ t → x t < c := by
  intro t ht
  by_contra hn
  have hn : c ≤ x t := le_of_not_gt hn
  have hcont : ContinuousOn x (Icc 0 t) := fun s hs =>
    (htraj s hs.1).1.continuousAt.continuousWithinAt
  obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc ht hcont ⟨hx0.le, hn⟩
  have h1 := (energy_between htraj hgamma hs.1).2
  have h2 := barrier lam r u c (y s)
  rw [hxs] at h1
  linarith

theorem confined_right {lam r u gamma T c : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r u gamma T x y b) (hgamma : 0 ≤ gamma)
    (hbar : max (E lam r u (x 0) (y 0)) T < f lam r u c) (hx0 : c < x 0) :
    ∀ t, 0 ≤ t → c < x t := by
  intro t ht
  by_contra hn
  have hn : x t ≤ c := le_of_not_gt hn
  have hcont : ContinuousOn x (Icc 0 t) := fun s hs =>
    (htraj s hs.1).1.continuousAt.continuousWithinAt
  obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc' ht hcont ⟨hn, hx0.le⟩
  have h1 := (energy_between htraj hgamma hs.1).2
  have h2 := barrier lam r u c (y s)
  rw [hxs] at h1
  linarith

/-- Trapping: if the potential on the starting side of the barrier never drops below `m`
and `m > T`, the energy gap stays at least `m - T > 0`: the target is never reached. -/
theorem trapped {lam r u gamma T c m : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r u gamma T x y b) (hgamma : 0 ≤ gamma)
    (hbar : max (E lam r u (x 0) (y 0)) T < f lam r u c) (hx0 : x 0 < c)
    (hm : ∀ z, z < c → m ≤ f lam r u z) :
    ∀ t, 0 ≤ t → m - T ≤ E lam r u (x t) (y t) - T := by
  intro t ht
  have hx := confined htraj hgamma hbar hx0 t ht
  have := barrier lam r u (x t) (y t)
  linarith [hm (x t) hx]

/-! ## D. The symmetric case `u = 0`: two shells and well selection -/

theorem f_zero_input_zero (lam r : ℝ) : f lam r 0 0 = 0 := by unfold f; ring

/-- Below the saddle value `0`, every state lies off the axis `x = 0`. -/
theorem neg_energy_x_ne_zero {lam r x y : ℝ} (h : E lam r 0 x y < 0) : x ≠ 0 := by
  rintro rfl
  have := barrier lam r 0 0 y
  rw [f_zero_input_zero] at this
  linarith

/-- Well selection: with `T < 0` and a start below the saddle, the sign of `x` never changes;
the shell component reached (if any) is fixed by the starting well. -/
theorem well_selection {lam r gamma T : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r 0 gamma T x y b) (hgamma : 0 ≤ gamma) (hT : T < 0)
    (hE0 : E lam r 0 (x 0) (y 0) < 0) :
    (0 < x 0 → ∀ t, 0 ≤ t → 0 < x t) ∧ (x 0 < 0 → ∀ t, 0 ≤ t → x t < 0) := by
  have hbar : max (E lam r 0 (x 0) (y 0)) T < f lam r 0 0 := by
    rw [f_zero_input_zero]; exact max_lt hE0 hT
  exact ⟨confined_right htraj hgamma hbar, confined htraj hgamma hbar⟩

/-- Mirror symmetry of the flow at `u = 0` (any circulation `b`). -/
theorem mirror {lam r gamma T : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r 0 gamma T x y b) :
    IsTrajectory lam r 0 gamma T (fun t => -x t) (fun t => -y t) b := by
  intro t ht
  obtain ⟨hx, hy⟩ := htraj t ht
  have hE : E lam r 0 (-x t) (-y t) = E lam r 0 (x t) (y t) := by unfold E f; ring
  have hgx : gx lam r 0 (-x t) (-y t) = -gx lam r 0 (x t) (y t) := by unfold gx; ring
  have hgy : gy (-x t) (-y t) = -gy (x t) (y t) := by unfold gy; ring
  refine ⟨?_, ?_⟩
  · convert hx.neg using 1; rw [hE, hgx, hgy]; ring
  · convert hy.neg using 1; rw [hE, hgx, hgy]; ring

/-- Global lower bound at `u = 0`: `E ≥ -r²/(4λ)`. -/
theorem energy_lower_bound {lam : ℝ} (hlam : 0 < lam) (r x y : ℝ) :
    -r ^ 2 / (4 * lam) ≤ E lam r 0 x y := by
  have h : E lam r 0 x y + r ^ 2 / (4 * lam) =
      (lam * x ^ 2 + r) ^ 2 / (4 * lam) + (y - Real.sqrt 2 * x) ^ 2 / 2 := by
    unfold E f; field_simp; ring
  have : 0 ≤ (lam * x ^ 2 + r) ^ 2 / (4 * lam) + (y - Real.sqrt 2 * x) ^ 2 / 2 := by positivity
  have : -r ^ 2 / (4 * lam) = -(r ^ 2 / (4 * lam)) := by ring
  linarith

/-- Targets below the well bottoms are never reached, from any start. -/
theorem unreachable_below_bottom {lam r gamma T : ℝ} {x y b : ℝ → ℝ} (hlam : 0 < lam)
    (_htraj : IsTrajectory lam r 0 gamma T x y b) (hT : T < -r ^ 2 / (4 * lam)) (t : ℝ) :
    0 < -r ^ 2 / (4 * lam) - T ∧ -r ^ 2 / (4 * lam) - T ≤ E lam r 0 (x t) (y t) - T :=
  ⟨by linarith, by linarith [energy_lower_bound hlam r (x t) (y t)]⟩

/-- For `-r²/(4λ) < T < 0` the target level has points in both half-planes and none on
`x = 0`: two shells, one around each well. -/
theorem two_shells {lam r T : ℝ} (hlam : 0 < lam) (hr : r < 0)
    (hlow : -r ^ 2 / (4 * lam) < T) (hT : T < 0) :
    (∃ x, 0 < x ∧ E lam r 0 x (Real.sqrt 2 * x) = T) ∧
      (∃ x, x < 0 ∧ E lam r 0 x (Real.sqrt 2 * x) = T) ∧
      ∀ x y, E lam r 0 x y = T → x ≠ 0 := by
  set a := Real.sqrt (-r / lam)
  have hq : 0 < -r / lam := div_pos (neg_pos.mpr hr) hlam
  have ha : 0 < a := Real.sqrt_pos.2 hq
  have ha2 : a ^ 2 = -r / lam := Real.sq_sqrt hq.le
  have hline : ∀ x, E lam r 0 x (Real.sqrt 2 * x) = lam * x ^ 4 / 4 + r * x ^ 2 / 2 := by
    intro x; unfold E f; ring
  have hfa : lam * a ^ 4 / 4 + r * a ^ 2 / 2 = -r ^ 2 / (4 * lam) := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ha2]; field_simp; ring
  have hc : Continuous fun x : ℝ => lam * x ^ 4 / 4 + r * x ^ 2 / 2 := by fun_prop
  obtain ⟨xp, hxp, hxpT⟩ := intermediate_value_Icc' ha.le hc.continuousOn
    (show T ∈ Icc (lam * a ^ 4 / 4 + r * a ^ 2 / 2) (lam * 0 ^ 4 / 4 + r * 0 ^ 2 / 2) by
      rw [hfa]; exact ⟨hlow.le, by norm_num; linarith⟩)
  have hxp0 : xp ≠ 0 := by rintro rfl; simp at hxpT; linarith
  refine ⟨⟨xp, lt_of_le_of_ne hxp.1 (Ne.symm hxp0), by rw [hline]; exact hxpT⟩,
    ⟨-xp, by linarith [lt_of_le_of_ne hxp.1 (Ne.symm hxp0)], by
      rw [hline, show (-xp) ^ 4 = xp ^ 4 by ring, show (-xp) ^ 2 = xp ^ 2 by ring]; exact hxpT⟩,
    fun x y h => neg_energy_x_ne_zero (by linarith)⟩

/-! ## E. Link with R03/R04: metastable rest points and the Maxwell point -/

/-- R03's metastable points are local minima of the planar energy and rest points of the flow,
lying strictly above some reachable energy. -/
theorem metastable_rest_point {lam r a : ℝ} (hlam : 0 < lam)
    (hloc : 0 < 3 * lam * a ^ 2 + r) (hglob : lam * a ^ 2 + r < 0) (gamma T : ℝ) (b : ℝ → ℝ) :
    IsLocalMin (fun p : ℝ × ℝ => E lam r (input lam r a) p.1 p.2) (a, Real.sqrt 2 * a) ∧
      IsTrajectory lam r (input lam r a) gamma T (fun _ => a) (fun _ => Real.sqrt 2 * a) b ∧
      ∃ x y, E lam r (input lam r a) x y < E lam r (input lam r a) a (Real.sqrt 2 * a) := by
  obtain ⟨hmin, hng⟩ := RoundTrip03.metastable_local_not_global hlam hloc hglob
  refine ⟨?_, const_isTrajectory b rfl rfl, ?_⟩
  · have hc : ContinuousAt (fun p : ℝ × ℝ => p.1) (a, Real.sqrt 2 * a) :=
      continuous_fst.continuousAt
    have h1 : IsLocalMin (f lam r (input lam r a) ∘ fun p : ℝ × ℝ => p.1) (a, Real.sqrt 2 * a) :=
      IsLocalMin.comp_continuous hmin hc
    filter_upwards [h1] with p hp
    have hval : E lam r (input lam r a) a (Real.sqrt 2 * a) = f lam r (input lam r a) a := by
      unfold E; simp
    simp only [Function.comp] at hp
    rw [hval]
    exact hp.trans (barrier lam r _ p.1 p.2)
  · by_contra h
    push Not at h
    exact hng fun x y => h x y

/-- At the Maxwell point both well bottoms carry the global value (R04), so a target just
above it is (energetically) available from both wells; this is the only input where the two
wells are equivalent (R03: the margin-zero locus is `u = 0`). -/
theorem maxwell_wells_equal {lam r : ℝ} (hlam : 0 < lam) (hr : r < 0) :
    let a := Real.sqrt (-r / lam)
    E lam r 0 a (Real.sqrt 2 * a) = RoundTrip04.value lam r 0 ∧
      E lam r 0 (-a) (Real.sqrt 2 * (-a)) = RoundTrip04.value lam r 0 ∧
      RoundTrip04.value lam r 0 = -r ^ 2 / (4 * lam) := by
  intro a
  have hq : 0 < -r / lam := div_pos (neg_pos.mpr hr) hlam
  have ha2 : a ^ 2 = -r / lam := Real.sq_sqrt hq.le
  have hmargin : lam * a ^ 2 + r = 0 := by rw [ha2]; field_simp; ring
  obtain ⟨hP, hM, -⟩ := RoundTrip03.maxwell_two_global_minimizers hlam hmargin
  have eP := RoundTrip04.value_eq_of_globalMin hlam hP
  have eM := RoundTrip04.value_eq_of_globalMin hlam hM
  rw [RoundTrip03.maxwell_input_zero hmargin] at eP
  rw [RoundTrip04.input_neg_of_margin hmargin] at eM
  refine ⟨eP.symm, eM.symm, ?_⟩
  rw [eP]
  have hin : (0 : ℝ) = input lam r a := (RoundTrip03.maxwell_input_zero hmargin).symm
  rw [rest_energy rfl hin, show a ^ 4 = (a ^ 2) ^ 2 by ring, ha2]
  field_simp
  ring

end RoundTripDoubleWell
