/-!
An explicit positive gradient bound on a regular energy band. The number is
calculated from the input and energy endpoints, without choosing a compact-set
minimum. Its consequences concern a supplied actual coordinate trajectory.
-/
noncomputable section
namespace LinearInputGradientBound

open LinearInputDesign LinearInputGradient LinearInputCoercivity
open LinearInputRegularBand LinearInputInvariance

/-- The quartic remainder in the energy-gradient identity has the same bound
as the already proved critical values, without a stationarity assumption. -/
theorem reduced_energy_bound {lam : ℝ} (hlam : 0 < lam) (r x : ℝ) :
    -3 * lam * x ^ 4 / 4 - r * x ^ 2 / 2 ≤ (max (-r) 0) ^ 2 / (12 * lam) := by
  have h := LinearInputCalculus.critical_value_le
    (r := r) (u := lam * x ^ 3 + r * x) (x := x) hlam rfl
  rw [LinearInputCalculus.critical_value rfl] at h
  exact h

/-- Energy is its bounded quartic remainder plus an actual-gradient term. -/
theorem energy_gradient_identity (lam r u x y : ℝ) :
    E lam r u x y = -3 * lam * x ^ 4 / 4 - r * x ^ 2 / 2 +
      x * gx lam r u x y + Real.sqrt 2 * x * gy x y + (gy x y) ^ 2 / 2 := by
  unfold E f gx gy
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The exact two-dimensional Cauchy estimate uses sqrt(2)^2 = 2. -/
theorem gradient_linear_term_sq (x a b : ℝ) :
    (x * a + Real.sqrt 2 * x * b) ^ 2 ≤ 3 * x ^ 2 * (a ^ 2 + b ^ 2) := by
  have hi : 3 * x ^ 2 * (a ^ 2 + b ^ 2) -
      (x * a + Real.sqrt 2 * x * b) ^ 2 = x ^ 2 * (Real.sqrt 2 * a - b) ^ 2 := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hn : 0 ≤ x ^ 2 * (Real.sqrt 2 * a - b) ^ 2 := by positivity
  linarith

/-- If delta is the margin above the critical-value bound and S bounds x^2,
the explicit gradient bound is delta^2/(3S+delta). -/
def gradientLowerBound (lam r u target upper : ℝ) : ℝ :=
  let delta := target - (max (-r) 0) ^ 2 / (12 * lam)
  delta ^ 2 / (3 * max (upper + lowerBoundConstant lam r u) 0 + delta)

theorem explicit_gradient_bound_pos {lam r u target upper : ℝ}
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target) :
    0 < gradientLowerBound lam r u target upper := by
  have hd : 0 < target - (max (-r) 0) ^ 2 / (12 * lam) := sub_pos.mpr htarget
  have hS : 0 ≤ max (upper + lowerBoundConstant lam r u) 0 := le_max_right _ _
  unfold gradientLowerBound
  exact div_pos (sq_pos_of_pos hd) (by positivity)

/-- A fully explicit lower bound for the squared actual gradient on the band. -/
theorem explicit_gradient_bound {lam r u target upper x y : ℝ}
    (hlam : 0 < lam)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (hlo : target ≤ E lam r u x y) (hhi : E lam r u x y ≤ upper) :
    gradientLowerBound lam r u target upper ≤ gSq lam r u x y := by
  let delta := target - (max (-r) 0) ^ 2 / (12 * lam)
  let S := max (upper + lowerBoundConstant lam r u) 0
  let g := gSq lam r u x y
  let L := x * gx lam r u x y + Real.sqrt 2 * x * gy x y
  have hd : 0 < delta := sub_pos.mpr htarget
  have hS : 0 ≤ S := le_max_right _ _
  have hg : 0 ≤ g := gSq_nonneg lam r u x y
  have hx : x ^ 2 ≤ S := by
    have hc := coercive_lower_bound hlam r u x y
    have hs : upper + lowerBoundConstant lam r u ≤ S := le_max_left _ _
    nlinarith [sq_nonneg (y - Real.sqrt 2 * x)]
  have he : delta ≤ L + g / 2 := by
    have hi := energy_gradient_identity lam r u x y
    have hb := reduced_energy_bound hlam r x
    have hgy : (gy x y) ^ 2 ≤ g := by
      dsimp [g, gSq]
      nlinarith [sq_nonneg (gx lam r u x y)]
    dsimp only [delta, L]
    linarith
  have hL : L ^ 2 ≤ 3 * S * g := by
    have hc := gradient_linear_term_sq x (gx lam r u x y) (gy x y)
    change L ^ 2 ≤ 3 * x ^ 2 * g at hc
    have hm := mul_nonneg (sub_nonneg.mpr hx) hg
    nlinarith
  have hy : 2 * delta * L ≤ delta ^ 2 + 3 * S * g := by
    nlinarith [sq_nonneg (L - delta)]
  have hm : delta ^ 2 ≤ (3 * S + delta) * g := by
    have he' := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * delta)
    nlinarith
  change delta ^ 2 / (3 * S + delta) ≤ g
  apply (div_le_iff₀ (by positivity : 0 < 3 * S + delta)).2
  nlinarith

/-- The computed band constant applies for all nonnegative times, with band
invariance derived from the initial condition and actual trajectory equations. -/
theorem gradient_bound_of_initial {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (hlam : 0 < lam) (hgamma : 0 ≤ gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target ≤ E lam r u (x 0) (y 0)) :
    ∀ t ∈ Set.Ici (0 : ℝ),
      gradientLowerBound lam r u target (E lam r u (x 0) (y 0)) ≤
        gSq lam r u (x t) (y t) := by
  intro t ht
  have hb := energy_band_of_trajectory hgamma htraj hinit t ht
  exact explicit_gradient_bound hlam htarget hb.1 hb.2

/-- Explicit exponential decay of the energy error itself, not only its square.
No global trajectory existence is asserted. -/
theorem energy_error_exponential_of_initial {lam r u gamma target : ℝ}
    (hlam : 0 < lam) (hgamma : 0 ≤ gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    {x y b : ℝ → ℝ} (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target ≤ E lam r u (x 0) (y 0)) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ E lam r u (x t) (y t) - target ∧
      E lam r u (x t) (y t) - target ≤
        (E lam r u (x 0) (y 0) - target) * Real.exp
          (-(gamma * gradientLowerBound lam r u target (E lam r u (x 0) (y 0))) * t) := by
  have hband := energy_band_of_trajectory hgamma htraj hinit
  have hg := gradient_bound_of_initial hlam hgamma htarget htraj hinit
  refine ⟨sub_nonneg.mpr (hband t ht).1, ?_⟩
  apply LinearInputDissipation.exponential_bound
    (v := fun s => E lam r u (x s) (y s) - target)
    (q := fun s => -gamma * (E lam r u (x s) (y s) - target) *
      gSq lam r u (x s) (y s))
    (k := gamma * gradientLowerBound lam r u target (E lam r u (x 0) (y 0)))
  · intro s hs
    exact hasDerivAt_gap_of_trajectory htraj hs
  · intro s hs
    have hn := mul_nonneg (mul_nonneg hgamma (sub_nonneg.mpr (hband s hs).1))
      (sub_nonneg.mpr (hg s hs))
    nlinarith
  · exact ht

/-- The same explicit positive constant gives the square-error estimate. -/
theorem squared_error_exponential_of_initial {lam r u gamma target : ℝ}
    (hlam : 0 < lam) (hgamma : 0 ≤ gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    {x y b : ℝ → ℝ} (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target ≤ E lam r u (x 0) (y 0)) {t : ℝ} (ht : 0 ≤ t) :
    (E lam r u (x t) (y t) - target) ^ 2 ≤
      (E lam r u (x 0) (y 0) - target) ^ 2 * Real.exp
        (-(2 * gamma * gradientLowerBound lam r u target (E lam r u (x 0) (y 0))) * t) := by
  exact LinearInputDissipation.squared_error_exponential hgamma
    (fun _ hs => hasDerivAt_gap_of_trajectory htraj hs)
    (gradient_bound_of_initial hlam hgamma htarget htraj hinit) ht

end LinearInputGradientBound
