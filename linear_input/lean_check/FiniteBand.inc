/-! Finite-interval confinement, suitable for extending actual local solutions. -/
noncomputable section
namespace LinearInputFiniteBand
open Real Set MeasureTheory
open LinearInputDesign LinearInputGradient LinearInputTrajectoryExistence

/-- A nonnegative coefficient preserves the initial error interval on [0,T]. -/
theorem error_band_on_Icc {e g : ℝ → ℝ} {gamma T : ℝ}
    (hgamma : 0 ≤ gamma) (hT : 0 ≤ T)
    (hg : ContinuousOn g (Icc (0 : ℝ) T))
    (hd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt e (-gamma * e s * g s) s)
    (hgn : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ g s) (hinit : 0 ≤ e 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ e t ∧ e t ≤ e 0 := by
  rw [LinearInputStrictEnergy.error_eq_initial_mul_exp_integral_on_Icc hg hT hd ht]
  have hi : 0 ≤ ∫ s in 0..t, g s :=
    intervalIntegral.integral_nonneg ht.1 (fun s hs => hgn s ⟨hs.1, hs.2.trans ht.2⟩)
  have he : Real.exp (-gamma * (∫ s in 0..t, g s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  exact ⟨mul_nonneg hinit (Real.exp_pos _).le,
    (mul_le_mul_of_nonneg_left he hinit).trans_eq (mul_one _)⟩

/-- The actual vector ODE on a finite interval implies energy-band confinement. -/
theorem energy_band_on_Icc {lam r u gamma target T : ℝ} {b : ℝ × ℝ → ℝ}
    {z : ℝ → ℝ × ℝ} (hgamma : 0 ≤ gamma) (hT : 0 ≤ T)
    (hode : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt z (vectorField lam r u gamma target b (z s)) s)
    (hinit : target ≤ E lam r u (z 0).1 (z 0).2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    target ≤ E lam r u (z t).1 (z t).2 ∧
      E lam r u (z t).1 (z t).2 ≤ E lam r u (z 0).1 (z 0).2 := by
  have hg : ContinuousOn (fun s => gSq lam r u (z s).1 (z s).2) (Icc (0 : ℝ) T) := by
    intro s hs
    exact ((continuous_gSq lam r u).continuousAt.comp (hode s hs).continuousAt).continuousWithinAt
  have h := error_band_on_Icc hgamma hT hg
    (fun s hs => (hasDerivAt_energy_of_solution (hode s hs)).sub_const target)
    (fun s _ => gSq_nonneg lam r u (z s).1 (z s).2) (sub_nonneg.mpr hinit) ht
  constructor <;> linarith [h.1, h.2]

/-- The same confinement holds in the nonnegative part of an open solution interval. -/
theorem energy_band_on_Ioo {lam r u gamma target eps a : ℝ} {b : ℝ × ℝ → ℝ}
    {z : ℝ → ℝ × ℝ} (hgamma : 0 ≤ gamma) (heps : 0 < eps)
    (hode : ∀ s ∈ Ioo (-eps) a,
      HasDerivAt z (vectorField lam r u gamma target b (z s)) s)
    (hinit : target ≤ E lam r u (z 0).1 (z 0).2)
    {t : ℝ} (ht : 0 ≤ t) (hta : t < a) :
    target ≤ E lam r u (z t).1 (z t).2 ∧
      E lam r u (z t).1 (z t).2 ≤ E lam r u (z 0).1 (z 0).2 := by
  apply energy_band_on_Icc (b := b) (z := z) hgamma ht (T := t) ?_ hinit ⟨ht, le_rfl⟩
  intro s hs
  exact hode s ⟨by linarith [hs.1], hs.2.trans_lt hta⟩

end LinearInputFiniteBand
