import TwoMotionEmission

/-!
Consequences of the explicit reduced model. Positive emission is equivalent to
nonzero two-motion drive under zero initial boundary displacement and positive
parameters. Outgoing profiles solve the classical wave equation on each branch;
this is not a distributional theorem at the source. A separate closed oscillator
counterexample prevents promoting this result to unrestricted emission.
-/

noncomputable section
open Set MeasureTheory
namespace TwoMotionEmission

/-- Zero force leaves the initially zero boundary fixed on the interval. -/
theorem boundary_zero_of_force_zero (κ g ω₁ ω₂ c T : ℝ) (z : Path)
    (hy₀ : z.y 0 = 0)
    (hz : ∀ t ∈ Icc 0 T, SolvesAt κ g ω₁ ω₂ c z t)
    (hF : ∀ t ∈ Icc 0 T, forceAlong κ g z t = 0) :
    ∀ t ∈ Icc 0 T, z.y t = 0 := by
  intro t ht
  have hd : ∀ u ∈ uIcc 0 t, HasDerivAt z.y 0 u := by
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    have huT : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
    simpa [hF u huT] using (hz u huT).dy
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 t)
  have he : (0 : ℝ) = z.y t - z.y 0 := by simpa using hi
  linarith

/-- A zero drive cannot excite the boundary from rest; proved by monotonicity
of its square, rather than by assuming uniqueness of an ODE solution. -/
theorem boundary_zero_of_drive_zero {κ c T : ℝ} (hκ : 0 ≤ κ) (hc : 0 < c)
    (hT : 0 ≤ T) (g ω₁ ω₂ : ℝ) (z : Path) (hy₀ : z.y 0 = 0)
    (hz : ∀ t ∈ Icc 0 T, SolvesAt κ g ω₁ ω₂ c z t)
    (hd : ∀ t ∈ Icc 0 T, g*z.x₁ t*z.x₂ t = 0) :
    ∀ t ∈ Icc 0 T, z.y t = 0 := by
  have hF : ∀ t ∈ Icc 0 T, forceAlong κ g z t = -κ*z.y t := by
    intro t ht
    dsimp [forceAlong, force]
    rw [hd t ht]
    ring
  have hs : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun u => (z.y u)^2) (-(κ/c)*(z.y t)^2) t := by
    intro t ht
    convert ((hz t ht).dy.pow 2) using 1
    rw [hF t ht]
    field_simp [ne_of_gt hc]
    ring
  have hcont : ContinuousOn (fun t => (z.y t)^2) (Icc 0 T) :=
    fun t ht => (hs t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (fun t => (z.y t)^2) (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hcont
      (fun t ht => (hs t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact neg_nonpos.mpr (mul_nonneg (div_nonneg hκ hc.le) (sq_nonneg (z.y t)))
  intro t ht
  have he := hanti (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht ht.1
  have he' : (z.y t)^2 = 0 := le_antisymm (by simpa [hy₀] using he) (sq_nonneg _)
  exact sq_eq_zero_iff.mp he'

/-- For the selected coupling, zero force throughout is exactly zero product. -/
theorem force_zero_iff_product_zero {κ c T : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hT : 0 ≤ T) {g : ℝ} (hg : g ≠ 0) (ω₁ ω₂ : ℝ) (z : Path)
    (hy₀ : z.y 0 = 0) (hz : ∀ t ∈ Icc 0 T, SolvesAt κ g ω₁ ω₂ c z t) :
    (∀ t ∈ Icc 0 T, forceAlong κ g z t = 0) ↔
      (∀ t ∈ Icc 0 T, z.x₁ t*z.x₂ t = 0) := by
  constructor
  · intro hF
    have hy := boundary_zero_of_force_zero κ g ω₁ ω₂ c T z hy₀ hz hF
    intro t ht
    have hf : κ * (g * (z.x₁ t*z.x₂ t)) = 0 := by
      simpa [forceAlong, force, hy t ht, mul_assoc] using hF t ht
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (ne_of_gt hκ))).resolve_left hg
  · intro hp
    have hd : ∀ t ∈ Icc 0 T, g*z.x₁ t*z.x₂ t = 0 := by
      intro t ht
      rw [mul_assoc, hp t ht, mul_zero]
    have hy := boundary_zero_of_drive_zero hκ.le hc hT g ω₁ ω₂ z hy₀ hz hd
    intro t ht
    simp [forceAlong, force, hd t ht, hy t ht]

/-- The precise conditional version of 'two motions necessarily emit'. -/
theorem emitted_pos_iff_product_nonzero {κ c T : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hT : 0 < T) {g : ℝ} (hg : g ≠ 0) (ω₁ ω₂ : ℝ) (z : Path)
    (hy₀ : z.y 0 = 0) (hz : ∀ t ∈ Icc 0 T, SolvesAt κ g ω₁ ω₂ c z t) :
    0 < emitted c (forceAlong κ g z) T ↔
      ∃ t ∈ Icc 0 T, z.x₁ t*z.x₂ t ≠ 0 := by
  rw [emitted_pos_iff hc hT _ (forceAlong_continuousOn κ g ω₁ ω₂ c z _ hz)]
  have hzero := force_zero_iff_product_zero hκ hc hT.le hg ω₁ ω₂ z hy₀ hz
  constructor
  · rintro ⟨t, ht, hn⟩
    by_contra h
    push Not at h
    exact hn ((hzero.mpr h) t ht)
  · rintro ⟨t, ht, hn⟩
    by_contra h
    push Not at h
    exact hn ((hzero.mp h) t ht)

/-- Actual second derivatives of the right branch obey the wave equation. -/
theorem rightWave_equation {c : ℝ} (hc : c ≠ 0) (y dy ddy : ℝ → ℝ)
    (hy : ∀ r, HasDerivAt y (dy r) r) (hdy : ∀ r, HasDerivAt dy (ddy r) r)
    (s t : ℝ) :
    deriv (fun u => deriv (fun v => rightWave c y s v) u) t =
      c^2 * deriv (fun u => deriv (fun v => rightWave c y v t) u) s := by
  have ht : (fun u => deriv (fun v => rightWave c y s v) u) =
      (fun u => dy (u-s/c)) := funext fun u => (rightWave_time c s u _ y (hy _)).deriv
  have hs : (fun u => deriv (fun v => rightWave c y v t) u) =
      (fun u => -dy (t-u/c)/c) := funext fun u => (rightWave_space c u t _ y (hy _)).deriv
  rw [ht, hs]
  have htt := rightWave_time c s t _ dy (hdy (t-s/c))
  have hss := (rightWave_space c s t _ dy (hdy (t-s/c))).neg.div_const c
  rw [htt.deriv, hss.deriv]
  field_simp [hc]
  ring

theorem leftWave_equation {c : ℝ} (hc : c ≠ 0) (y dy ddy : ℝ → ℝ)
    (hy : ∀ r, HasDerivAt y (dy r) r) (hdy : ∀ r, HasDerivAt dy (ddy r) r)
    (s t : ℝ) :
    deriv (fun u => deriv (fun v => leftWave c y s v) u) t =
      c^2 * deriv (fun u => deriv (fun v => leftWave c y v t) u) s := by
  have ht : (fun u => deriv (fun v => leftWave c y s v) u) =
      (fun u => dy (u+s/c)) := funext fun u => (leftWave_time c s u _ y (hy _)).deriv
  have hs : (fun u => deriv (fun v => leftWave c y v t) u) =
      (fun u => dy (t+u/c)/c) := funext fun u => (leftWave_space c u t _ y (hy _)).deriv
  rw [ht, hs]
  have htt := leftWave_time c s t _ dy (hdy (t+s/c))
  have hss := (leftWave_space c s t _ dy (hdy (t+s/c))).div_const c
  rw [htt.deriv, hss.deriv]
  field_simp [hc]
  ring

/-- A smooth, nontrivial excursion of a separate closed unit-frequency oscillator. -/
def cancelPosition (t : ℝ) : ℝ := t^2 - 2*t^3 + t^4
def cancelVelocity (t : ℝ) : ℝ := 2*t - 6*t^2 + 4*t^3
def cancelAcceleration (t : ℝ) : ℝ := 2 - 12*t + 12*t^2
def cancelDrive (t : ℝ) : ℝ := cancelAcceleration t + cancelPosition t

theorem cancelPosition_hasDerivAt (t : ℝ) :
    HasDerivAt cancelPosition (cancelVelocity t) t := by
  convert (((hasDerivAt_id t).pow 2).sub (((hasDerivAt_id t).pow 3).const_mul 2)).add
    ((hasDerivAt_id t).pow 4) using 1
  dsimp [cancelPosition, cancelVelocity]
  ring

theorem cancelVelocity_hasDerivAt (t : ℝ) :
    HasDerivAt cancelVelocity (cancelAcceleration t) t := by
  convert (((hasDerivAt_id t).const_mul 2).sub (((hasDerivAt_id t).pow 2).const_mul 6)).add
    (((hasDerivAt_id t).pow 3).const_mul 4) using 1
  dsimp [cancelVelocity, cancelAcceleration]
  ring

theorem closed_mode_equation (t : ℝ) :
    deriv (deriv cancelPosition) t + cancelPosition t = cancelDrive t := by
  have h : deriv cancelPosition = cancelVelocity := funext fun u => (cancelPosition_hasDerivAt u).deriv
  rw [h, (cancelVelocity_hasDerivAt t).deriv]
  rfl

/-- Nonzero forcing need not leave residual excitation in a closed channel. -/
theorem closed_mode_returns_to_rest :
    cancelPosition 0 = 0 ∧ cancelVelocity 0 = 0 ∧
    cancelPosition 1 = 0 ∧ cancelVelocity 1 = 0 ∧
    cancelPosition (1/2) = 1/16 ∧ cancelDrive 0 = 2 := by
  norm_num [cancelPosition, cancelVelocity, cancelDrive, cancelAcceleration]

end TwoMotionEmission
