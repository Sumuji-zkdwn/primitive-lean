/-!
# Round trip 7: double-well particle → separatrix (soliton) → elastica curvature

Input: round 6 (curvature is a particle in `potential (1/2) (-σ/k) 0`). For `σ/k = c² > 0`
the potential is a double well with a hilltop at `κ = 0`.
Translation (integrable systems): the separatrix through the hilltop is the soliton
`κ(s) = 2c sech(cs)` (the profile of the mKdV soliton; this identification is an
interpretation and is not formalized). Back-translation: it solves the baseline curvature
equation exactly and carries phase energy `0`, the hilltop value.
-/

noncomputable section
namespace RoundTrip07
open Real LinearInputDesign

/-- Soliton curvature profile. -/
def soliton (c s : ℝ) : ℝ := 2 * c / cosh (c * s)

/-- Its derivative. -/
def solitonDeriv (c s : ℝ) : ℝ := -2 * c ^ 2 * sinh (c * s) / cosh (c * s) ^ 2

theorem hasDerivAt_soliton (c s : ℝ) : HasDerivAt (soliton c) (solitonDeriv c s) s := by
  have hc : HasDerivAt (fun t => cosh (c * t)) (sinh (c * s) * c) s :=
    (hasDerivAt_cosh (c * s)).comp s ((hasDerivAt_id s).const_mul c |>.congr_deriv (by simp))
  have h := (hasDerivAt_const s (2 * c)).div hc (cosh_pos _).ne'
  unfold soliton solitonDeriv
  convert h using 1
  ring

theorem deriv_soliton (c : ℝ) : deriv (soliton c) = solitonDeriv c :=
  funext fun s => (hasDerivAt_soliton c s).deriv

theorem hasDerivAt_solitonDeriv (c s : ℝ) :
    HasDerivAt (solitonDeriv c)
      (-2 * c ^ 3 * (cosh (c * s) ^ 2 - 2 * sinh (c * s) ^ 2) / cosh (c * s) ^ 3) s := by
  have hl : HasDerivAt (fun t => c * t) c s := (hasDerivAt_id s).const_mul c |>.congr_deriv (by simp)
  have hs : HasDerivAt (fun t => sinh (c * t)) (cosh (c * s) * c) s := (hasDerivAt_sinh _).comp s hl
  have h1 : HasDerivAt (fun t => cosh (c * t)) (sinh (c * s) * c) s :=
    (hasDerivAt_cosh _).comp s hl
  have hc : HasDerivAt (fun t => cosh (c * t) ^ 2) (2 * cosh (c * s) * (sinh (c * s) * c)) s := by
    convert h1.pow 2 using 1
    norm_num
  have hcne : cosh (c * s) ^ 2 ≠ 0 := by positivity
  have h := (hs.const_mul (-2 * c ^ 2)).div hc hcne
  unfold solitonDeriv
  convert h using 1
  have hc0 : cosh (c * s) ≠ 0 := (cosh_pos _).ne'
  field_simp
  ring

theorem contDiff_soliton (c : ℝ) : ContDiff ℝ 2 (soliton c) := by
  unfold soliton
  exact contDiff_const.div (contDiff_cosh.comp (contDiff_const.mul contDiff_id))
    fun s => (cosh_pos _).ne'

/-- The soliton solves the baseline (unforced) curvature equation with `σ = k c²`. -/
theorem soliton_curvature_equation (k c s : ℝ) :
    k * deriv (deriv (soliton c)) s + k * (soliton c s) ^ 3 / 2 - (k * c ^ 2) * soliton c s = 0 := by
  rw [deriv_soliton, (hasDerivAt_solitonDeriv c s).deriv]
  unfold soliton
  have hc0 : cosh (c * s) ≠ 0 := (cosh_pos _).ne'
  have hs2 : sinh (c * s) ^ 2 = cosh (c * s) ^ 2 - 1 := by linarith [cosh_sq (c * s)]
  rw [hs2]
  field_simp
  ring

/-- Its phase energy vanishes identically: it is the separatrix through the hilltop. -/
theorem soliton_phase_energy (k c s : ℝ) (hk : k ≠ 0) :
    E (1 / 2) (-(k * c ^ 2) / k) 0 (soliton c s)
      (deriv (soliton c) s + Real.sqrt 2 * soliton c s) = 0 := by
  rw [LinearInputCurvatureBridge.energy_shear, deriv_soliton]
  unfold soliton solitonDeriv
  have hc0 : cosh (c * s) ≠ 0 := (cosh_pos _).ne'
  have hs2 : sinh (c * s) ^ 2 = cosh (c * s) ^ 2 - 1 := by linarith [cosh_sq (c * s)]
  rw [show (-2 * c ^ 2 * sinh (c * s) / cosh (c * s) ^ 2) ^ 2 =
      4 * c ^ 4 * sinh (c * s) ^ 2 / cosh (c * s) ^ 4 by ring, hs2]
  field_simp
  ring

/-- The baseline phase flow applies verbatim to the soliton (for `k ≠ 0`). -/
theorem soliton_phase_flow {k : ℝ} (hk : k ≠ 0) (c s : ℝ) :
    HasDerivAt (soliton c)
      (LinearInputGradient.gy (soliton c s) (deriv (soliton c) s + Real.sqrt 2 * soliton c s)) s ∧
    HasDerivAt (fun t => deriv (soliton c) t + Real.sqrt 2 * soliton c t)
      (-LinearInputGradient.gx (1 / 2) (-(k * c ^ 2) / k) 0 (soliton c s)
        (deriv (soliton c) s + Real.sqrt 2 * soliton c s)) s :=
  LinearInputCurvatureBridge.phase_hasDerivAt hk (contDiff_soliton c)
    (soliton_curvature_equation k c s)

/-- The hilltop: the phase potential at `κ = 0` is `0`, and the soliton decays to it. -/
theorem soliton_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (soliton c) Filter.atTop (nhds 0) := by
  unfold soliton
  have h : Filter.Tendsto (fun s => cosh (c * s)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun s => ?_) ((tendsto_exp_atTop.comp
      (Filter.tendsto_id.const_mul_atTop hc)).atTop_div_const (by norm_num : (0 : ℝ) < 2))
    rw [cosh_eq]
    simp only [Function.comp, id]
    linarith [exp_pos (-(c * s))]
  exact h.const_div_atTop (2 * c) |>.congr fun _ => rfl

end RoundTrip07
