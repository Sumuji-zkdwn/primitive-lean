import Elastica

/-! Bounds for supplied damped internal-coordinate updates driven by a confined
spatial trajectory. No existence or global continuation is asserted here. -/
noncomputable section
namespace LinearInputInternalUpdate
open Real Set Filter MeasureTheory
open LinearInputDesign LinearInputGradient LinearInputRegularBand
open scoped Topology

/-- A bounded forcing gives an explicit estimate for the actual square of a
supplied internal coordinate. -/
theorem square_bound {θ f : ℝ → ℝ} {κ ρ M : ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M)
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt θ (-κ * θ t + ρ * f t) t)
    (hf : ∀ t ∈ Ici (0 : ℝ), |f t| ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    (θ t)^2 ≤ (θ 0)^2 * exp (-κ*t) + (ρ*M/κ)^2 * (1-exp (-κ*t)) := by
  let C : ℝ := (ρ*M/κ)^2
  have hC : κ^2 * C = ρ^2 * M^2 := by
    dsimp [C]
    field_simp
  have hv : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt (fun s => (θ s)^2-C) (2*θ s*(-κ*θ s+ρ*f s)) s := by
    intro s hs
    convert ((hd s hs).pow 2).sub_const C using 1; ring
  have hi : ∀ s ∈ Ici (0 : ℝ),
      2*θ s*(-κ*θ s+ρ*f s) ≤ -κ*((θ s)^2-C) := by
    intro s hs
    have hf2 : (f s)^2 ≤ M^2 := by
      nlinarith [sq_abs (f s), hf s hs, abs_nonneg (f s)]
    have hforce : ρ^2*(f s)^2 ≤ ρ^2*M^2 :=
      mul_le_mul_of_nonneg_left hf2 (sq_nonneg ρ)
    have hscaled : κ*(2*θ s*(-κ*θ s+ρ*f s)+κ*((θ s)^2-C)) ≤ 0 := by
      nlinarith [sq_nonneg (κ*θ s-ρ*f s)]
    have hsum : 2*θ s*(-κ*θ s+ρ*f s)+κ*((θ s)^2-C) ≤ 0 := by
      nlinarith
    linarith
  have hb := LinearInputDissipation.exponential_bound hv hi ht
  dsimp [C] at *
  nlinarith

/-- Uniform square bound, including the initial transient. -/
theorem square_le_max {θ f : ℝ → ℝ} {κ ρ M : ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M)
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt θ (-κ * θ t + ρ * f t) t)
    (hf : ∀ t ∈ Ici (0 : ℝ), |f t| ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    (θ t)^2 ≤ max ((θ 0)^2) ((ρ*M/κ)^2) := by
  have hb := square_bound hκ hM hd hf ht
  have he0 : 0 ≤ exp (-κ*t) := (exp_pos _).le
  have he1 : exp (-κ*t) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have h₁ := mul_le_mul_of_nonneg_right
    (le_max_left ((θ 0)^2) ((ρ*M/κ)^2)) he0
  have h₂ := mul_le_mul_of_nonneg_right
    (le_max_right ((θ 0)^2) ((ρ*M/κ)^2)) (sub_nonneg.mpr he1)
  nlinarith

/-- Continuity of a forcing on the plane gives a uniform bound along the
supplied trajectory, using its derived compact energy confinement. -/
theorem exists_forcing_bound {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (hlam : 0 < lam) (hgamma : 0 ≤ gamma)
    (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target ≤ E lam r u (x 0) (y 0))
    {Φ : ℝ × ℝ → ℝ} (hΦ : Continuous Φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Ici (0 : ℝ), |Φ (x t,y t)| ≤ M := by
  have hcompact := LinearInputCoercivity.isCompact_band hlam r u target
    (E lam r u (x 0) (y 0))
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  have hz := LinearInputInvariance.energy_band_of_trajectory hgamma htraj hinit t ht
  have hb := hC (x t,y t) hz
  exact (show |Φ (x t,y t)| ≤ C by simpa only [Real.norm_eq_abs] using hb).trans
    (le_max_left _ _)

/-- The damped internal coordinate is bounded whenever it is driven by a
continuous observable of a confined supplied spatial trajectory. -/
theorem internal_update_bounded {lam r u gamma target κ ρ : ℝ}
    {x y b θ : ℝ → ℝ} {Φ : ℝ × ℝ → ℝ}
    (hlam : 0 < lam) (hgamma : 0 ≤ gamma) (hκ : 0 < κ)
    (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target ≤ E lam r u (x 0) (y 0)) (hΦ : Continuous Φ)
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt θ (-κ*θ t+ρ*Φ (x t,y t)) t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ici (0 : ℝ), (θ t)^2 ≤ C := by
  obtain ⟨M,hM,hf⟩ := exists_forcing_bound hlam hgamma htraj hinit hΦ
  refine ⟨max ((θ 0)^2) ((ρ*M/κ)^2), (sq_nonneg _).trans (le_max_left _ _), ?_⟩
  exact fun t ht => square_le_max hκ hM hd hf ht

end LinearInputInternalUpdate
