import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Round trip 9: kink angle → planar curve → moment law and a self-crossing loop

Input: round 8 (`θ = 4 arctan e^{cs}` solves the baseline angle equation with `μ = 0`).
Translation (differential geometry / statics): reconstruct the curve with the baseline
`xCoord`, `yCoord`. Back-translation: (i) a general moment balance — for ANY solution of
the baseline angle equation, `k κ + λ y - μ x` is constant (bending moment equals the
moment of the end force); (ii) for the kink, explicitly
`x = s - (2/c) tanh(cs)`, `y = (2/c) sech(cs)`, so `κ = c² y`; (iii) the curve crosses
itself: it is an immersion, not an embedding.
-/

noncomputable section
namespace RoundTrip09
open Real Set RoundTrip07 RoundTrip08

/-- Moment balance from the baseline angle equation and the baseline coordinate derivatives. -/
theorem moment_balance {θ κ : ℝ → ℝ} {k lam μ a b x₀ y₀ : ℝ} (hθ : Continuous θ)
    (hM : ∀ s ∈ Ioo a b, HasDerivAt (fun t => k * κ t) (-lam * sin (θ s) + μ * cos (θ s)) s) :
    ∃ C : ℝ, ∀ s ∈ Ioo a b,
      k * κ s + lam * Elastica.yCoord θ y₀ s - μ * Elastica.xCoord θ x₀ s = C := by
  have hd : ∀ s ∈ Ioo a b, HasDerivAt
      (fun t => k * κ t + lam * Elastica.yCoord θ y₀ t - μ * Elastica.xCoord θ x₀ t) 0 s := by
    intro s hs
    have h := ((hM s hs).add ((Elastica.hasDerivAt_yCoord hθ y₀ s).const_mul lam)).sub
      ((Elastica.hasDerivAt_xCoord hθ x₀ s).const_mul μ)
    convert h using 1
    ring
  apply isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
  · intro s hs; exact (hd s hs).differentiableAt.differentiableWithinAt
  · intro s hs; exact (hd s hs).deriv

theorem hasDerivAt_xAntideriv {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (fun t => t - 2 / c * (sinh (c * t) / cosh (c * t))) (cos (kink c u)) u := by
  have hl : HasDerivAt (fun t => c * t) c u := (hasDerivAt_id u).const_mul c |>.congr_deriv (by simp)
  have hs := (hasDerivAt_sinh (c * u)).comp u hl
  have hch := (hasDerivAt_cosh (c * u)).comp u hl
  have h := (hasDerivAt_id u).sub ((hs.div hch (cosh_pos _).ne').const_mul (2 / c))
  rw [cos_kink]
  convert h using 1
  have hc0 : cosh (c * u) ≠ 0 := (cosh_pos _).ne'
  simp only [Function.comp]
  have h1 : cosh (c * u) * c * cosh (c * u) - sinh (c * u) * (sinh (c * u) * c) = c := by
    linear_combination c * cosh_sq (c * u)
  rw [h1]
  field_simp

theorem hasDerivAt_yAntideriv {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (fun t => 2 / (c * cosh (c * t))) (sin (kink c u)) u := by
  have hl : HasDerivAt (fun t => c * t) c u := (hasDerivAt_id u).const_mul c |>.congr_deriv (by simp)
  have hch := ((hasDerivAt_cosh (c * u)).comp u hl).const_mul c
  have h := (hasDerivAt_const u (2 : ℝ)).div hch (mul_ne_zero hc (cosh_pos _).ne')
  rw [sin_kink]
  convert h using 1
  have hc0 : cosh (c * u) ≠ 0 := (cosh_pos _).ne'
  simp only [Function.comp]
  field_simp
  ring

theorem xCoord_kink {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    Elastica.xCoord (kink c) 0 s = s - 2 / c * (sinh (c * s) / cosh (c * s)) := by
  unfold Elastica.xCoord
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_xAntideriv hc u)
    ((continuous_cos.comp (contDiff_kink c (n := 0)).continuous).intervalIntegrable _ _)]
  simp

theorem yCoord_kink {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    Elastica.yCoord (kink c) (2 / c) s = 2 / (c * cosh (c * s)) := by
  unfold Elastica.yCoord
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_yAntideriv hc u)
    ((continuous_sin.comp (contDiff_kink c (n := 0)).continuous).intervalIntegrable _ _)]
  simp

/-- Curvature is proportional to the height above the force line: `κ = c² y`. -/
theorem soliton_eq_height {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    soliton c s = c ^ 2 * Elastica.yCoord (kink c) (2 / c) s := by
  rw [yCoord_kink hc]
  unfold soliton
  have hc0 : cosh (c * s) ≠ 0 := (cosh_pos _).ne'
  field_simp

/-- The same law from the general moment balance (consistency of two routes). -/
theorem moment_constant_kink (k c : ℝ) (hc : c ≠ 0) (s : ℝ) :
    k * soliton c s + (-(k * c ^ 2)) * Elastica.yCoord (kink c) (2 / c) s -
      0 * Elastica.xCoord (kink c) 0 s = 0 := by
  rw [soliton_eq_height hc]
  ring

theorem tanh_one_gt_half : 1 / 2 < sinh 1 / cosh 1 := by
  rw [lt_div_iff₀ (cosh_pos 1), cosh_eq, sinh_eq, exp_neg]
  have he := Real.exp_one_gt_d9
  have hpos := exp_pos 1
  rw [show (1 : ℝ) / 2 * ((exp 1 + (exp 1)⁻¹) / 2) = (exp 1 ^ 2 + 1) / (4 * exp 1) by
    field_simp; ring,
    show (exp 1 - (exp 1)⁻¹) / 2 = (exp 1 ^ 2 - 1) / (2 * exp 1) by field_simp]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- A double point of the unit loop: two distinct parameters with the same point. -/
theorem kink_self_intersection :
    ∃ s ∈ Ioo (1 : ℝ) 2,
      Elastica.xCoord (kink 1) 0 s = Elastica.xCoord (kink 1) 0 (-s) ∧
      Elastica.yCoord (kink 1) (2 / 1) s = Elastica.yCoord (kink 1) (2 / 1) (-s) ∧ s ≠ -s := by
  let g : ℝ → ℝ := fun s => s - 2 / 1 * (sinh (1 * s) / cosh (1 * s))
  have hg : ContinuousOn g (Icc 1 2) := by
    apply Continuous.continuousOn
    have : Continuous fun s : ℝ => sinh (1 * s) / cosh (1 * s) :=
      (continuous_sinh.comp (continuous_const.mul continuous_id)).div
        (continuous_cosh.comp (continuous_const.mul continuous_id)) fun s => (cosh_pos _).ne'
    exact continuous_id.sub (continuous_const.mul this)
  have h1 : g 1 < 0 := by
    simp only [g, one_mul, div_one]; linarith [tanh_one_gt_half]
  have h2 : 0 < g 2 := by
    simp only [g, one_mul, div_one]
    have := div_lt_one (cosh_pos 2) |>.2 (sinh_lt_cosh 2)
    linarith
  obtain ⟨s, hs, hgs⟩ := intermediate_value_Ioo (by norm_num) hg ⟨h1, h2⟩
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · rw [xCoord_kink one_ne_zero, xCoord_kink one_ne_zero]
    simp only [g] at hgs
    simp only [mul_neg, sinh_neg, cosh_neg, neg_div]
    linarith
  · rw [yCoord_kink one_ne_zero, yCoord_kink one_ne_zero]
    simp [cosh_neg]
  · linarith [hs.1]

end RoundTrip09
