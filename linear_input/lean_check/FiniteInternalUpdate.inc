/-! Finite-interval damping estimates for compact continuation of coupled systems. -/
noncomputable section
namespace LinearInputFiniteInternalUpdate
open Real Set

/-- Integrating-factor estimate requiring the differential inequality only on [0,T]. -/
theorem exponential_bound_on_Icc {v q : ℝ → ℝ} {k T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt v (q t) t)
    (hi : ∀ t ∈ Icc (0 : ℝ) T, q t ≤ -k * v t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    v t ≤ v 0 * Real.exp (-k * t) := by
  let w : ℝ → ℝ := fun s => Real.exp (k * s) * v s
  let dw : ℝ → ℝ := fun s => Real.exp (k * s) * (k * v s + q s)
  have hw : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt w (dw s) s := by
    intro s hs
    convert (((hasDerivAt_id s).const_mul k).exp.mul (hd s hs)) using 1
    dsimp [w, dw]
    ring
  have hc : ContinuousOn w (Icc (0 : ℝ) T) :=
    fun s hs => (hw s hs).continuousAt.continuousWithinAt
  have ha : AntitoneOn w (Icc (0 : ℝ) T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) T) hc
      (fun s hs => (hw s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => by
        dsimp [dw]
        apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        have h := hi s (interior_subset hs)
        linarith)
  have hvalue : Real.exp (k * t) * v t ≤ v 0 := by
    simpa [w] using ha ⟨le_rfl, hT⟩ ht ht.1
  have hdiv : v t ≤ v 0 / Real.exp (k * t) := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    simpa only [mul_comm] using hvalue
  simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hdiv

/-- The explicit square bound is valid on every finite interval of existence. -/
theorem square_bound_on_Icc {θ f : ℝ → ℝ} {κ ρ M T : ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt θ (-κ * θ t + ρ * f t) t)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, |f t| ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (θ t)^2 ≤ (θ 0)^2 * exp (-κ*t) + (ρ*M/κ)^2 * (1-exp (-κ*t)) := by
  let C : ℝ := (ρ*M/κ)^2
  have hC : κ^2 * C = ρ^2 * M^2 := by
    dsimp [C]
    field_simp
  have hv : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s => (θ s)^2-C) (2*θ s*(-κ*θ s+ρ*f s)) s := by
    intro s hs
    convert ((hd s hs).pow 2).sub_const C using 1; ring
  have hi : ∀ s ∈ Icc (0 : ℝ) T,
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
  have hb := exponential_bound_on_Icc hT hv hi ht
  dsimp [C] at *
  nlinarith

/-- A forcing below κM preserves the interval [-M,M] for the damped coordinate. -/
theorem abs_le_on_Icc {θ f : ℝ → ℝ} {κ M T : ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt θ (-κ * θ t + f t) t)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, |f t| ≤ κ * M)
    (hinit : |θ 0| ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : |θ t| ≤ M := by
  have hb := square_bound_on_Icc (ρ := 1) hκ (mul_nonneg hκ.le hM) hT
    (fun s hs => by simpa only [one_mul] using hd s hs) hf ht
  have hc : (1 * (κ*M) / κ)^2 = M^2 := by field_simp
  rw [hc] at hb
  have hstart : (θ 0)^2 ≤ M^2 := by
    nlinarith [sq_abs (θ 0), abs_nonneg (θ 0)]
  have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hstart)
    (exp_pos (-κ*t)).le
  have ht2 : (θ t)^2 ≤ M^2 := by nlinarith
  nlinarith [sq_abs (θ t), abs_nonneg (θ t)]

end LinearInputFiniteInternalUpdate
