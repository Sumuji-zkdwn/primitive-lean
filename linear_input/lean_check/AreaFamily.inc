import Elastica

/-! Actual finite-parameter families for area-constrained local minima. -/
noncomputable section
namespace LinearInputAreaFamily
open Real Set MeasureTheory Filter Elastica
open scoped Topology

private theorem abs_four_term_bound {t a b c u v w z C : ℝ}
    (hu : |u| ≤ C) (hv : |v| ≤ C) (hw : |w| ≤ C) (hz : |z| ≤ C) :
    |t*u+a*v+b*w+c*z| ≤ (|t| + |a| + |b| + |c|)*C := by
  calc
    _ ≤ |t*u+a*v+b*w| + |c*z| := abs_add_le _ _
    _ ≤ (|t*u+a*v| + |b*w|) + |c*z| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((|t*u| + |a*v|) + |b*w|) + |c*z| :=
      add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ = |t| * |u| + |a| * |v| + |b| * |w| + |c| * |z| := by simp only [abs_mul]
    _ ≤ |t| * C + |a| * C + |b| * C + |c| * C := by
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hv (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hw (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hz (abs_nonneg _))
    _ = _ := by ring

/-- A continuous finite-parameter correction tending to zero tends to the base
angle in the C¹ neighborhood on the fixed compact interval. -/
theorem corrected_family_C1_close {θ : ℝ → ℝ} {ℓ : ℝ}
    (hθ : ContDiff ℝ 1 θ) (η ξ₁ ξ₂ ξ₃ : variationSpace ℓ)
    {a b c : ℝ → ℝ} (ha : ContinuousAt a 0) (hb : ContinuousAt b 0) (hc : ContinuousAt c 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (hc0 : c 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s ∈ Icc 0 ℓ,
      |(θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s) - θ s| < r ∧
      |deriv (fun u => θ u + t * η.val u + a t * ξ₁.val u + b t * ξ₂.val u + c t * ξ₃.val u) s -
        deriv θ s| < r := by
  let G : ℝ → ℝ := fun s =>
    |η.val s| + |deriv η.val s| + |ξ₁.val s| + |deriv ξ₁.val s| +
      |ξ₂.val s| + |deriv ξ₂.val s| + |ξ₃.val s| + |deriv ξ₃.val s|
  have hG : Continuous G :=
    ((((((η.property.1.continuous.abs.add η.property.1.continuous_deriv_one.abs).add
      ξ₁.property.1.continuous.abs).add ξ₁.property.1.continuous_deriv_one.abs).add
        ξ₂.property.1.continuous.abs).add ξ₂.property.1.continuous_deriv_one.abs).add ξ₃.property.1.continuous.abs).add
      ξ₃.property.1.continuous_deriv_one.abs
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) ℓ)).exists_bound_of_continuousOn
    hG.continuousOn
  have hbounds (s : ℝ) (hs : s ∈ Icc 0 ℓ) :
      |η.val s| ≤ C ∧ |deriv η.val s| ≤ C ∧
      |ξ₁.val s| ≤ C ∧ |deriv ξ₁.val s| ≤ C ∧
      |ξ₂.val s| ≤ C ∧ |deriv ξ₂.val s| ≤ C ∧
      |ξ₃.val s| ≤ C ∧ |deriv ξ₃.val s| ≤ C := by
    have hg : G s ≤ C := (le_abs_self (G s)).trans (by
      simpa only [Real.norm_eq_abs] using hC s hs)
    dsimp [G] at hg
    have h₁ := abs_nonneg (η.val s)
    have h₂ := abs_nonneg (deriv η.val s)
    have h₃ := abs_nonneg (ξ₁.val s)
    have h₄ := abs_nonneg (deriv ξ₁.val s)
    have h₅ := abs_nonneg (ξ₂.val s)
    have h₆ := abs_nonneg (deriv ξ₂.val s)
    have h₇ := abs_nonneg (ξ₃.val s)
    have h₈ := abs_nonneg (deriv ξ₃.val s)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hcont : ContinuousAt (fun t : ℝ => (|t| + |a t| + |b t| + |c t|) * C) 0 :=
    (((continuousAt_id.abs.add ha.abs).add hb.abs).add hc.abs).mul continuousAt_const
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), (|t| + |a t| + |b t| + |c t|) * C < r :=
    hcont.eventually (Iio_mem_nhds (by simpa [ha0, hb0, hc0] using hr))
  filter_upwards [hsmall] with t ht
  intro s hs
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hbounds s hs
  have hd : deriv (fun u => θ u + t * η.val u + a t * ξ₁.val u + b t * ξ₂.val u + c t * ξ₃.val u) s =
      deriv θ s + t * deriv η.val s + a t * deriv ξ₁.val s + b t * deriv ξ₂.val s + c t * deriv ξ₃.val s :=
    (((((hθ.differentiable one_ne_zero s).hasDerivAt.add
      ((η.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul t)).add
        ((ξ₁.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (a t))).add
          ((ξ₂.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (b t))).add
            ((ξ₃.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (c t))).deriv
  constructor
  · have he : θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s - θ s =
        t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s := by ring
    rw [he]
    exact (abs_four_term_bound h₁ h₃ h₅ h₇).trans_lt ht
  · rw [hd]
    have he : deriv θ s + t * deriv η.val s + a t * deriv ξ₁.val s +
        b t * deriv ξ₂.val s + c t * deriv ξ₃.val s - deriv θ s =
        t * deriv η.val s + a t * deriv ξ₁.val s + b t * deriv ξ₂.val s + c t * deriv ξ₃.val s := by ring
    rw [he]
    exact (abs_four_term_bound h₂ h₄ h₆ h₈).trans_lt ht


/-- The bending energy is differentiated along the actual corrected family.
The three correction coefficients have zero value and zero first derivative. -/
theorem hasDerivAt_corrected_energy_feasible {k ℓ : ℝ} {θ : ℝ → ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : ContDiff ℝ 1 θ) (η ξ₁ ξ₂ ξ₃ : variationSpace ℓ)
    {a b c : ℝ → ℝ} (ha : HasDerivAt a 0 0) (hb : HasDerivAt b 0 0)
    (hc : HasDerivAt c 0 0) (ha0 : a 0 = 0) (hb0 : b 0 = 0) (hc0 : c 0 = 0) :
    HasDerivAt (fun t => energy (fun q => k*q^2/2)
      (fun s => θ s + t*η.val s + a t*ξ₁.val s + b t*ξ₂.val s + c t*ξ₃.val s) ℓ)
      (∫ s in 0..ℓ, k * deriv θ s * deriv η.val s) 0 := by
  let B := LinearInputAreaParameters.parameterLinear
    (deriv η.val) (deriv ξ₁.val) (deriv ξ₂.val) (deriv ξ₃.val)
  have hB : Continuous B := LinearInputAreaParameters.continuous_parameterLinear
    η.property.1.continuous_deriv_one ξ₁.property.1.continuous_deriv_one
    ξ₂.property.1.continuous_deriv_one ξ₃.property.1.continuous_deriv_one
  have hf := LinearInputAreaParameters.hasFDerivAt_integral_linear_parameters
    hℓ (show ContDiff ℝ 1 (fun q : ℝ => k*q^2/2) by fun_prop)
      hθ.continuous_deriv_one hB (0 : LinearInputAreaParameters.Parameters)
  have hden (q : ℝ) : deriv (fun q : ℝ => k*q^2/2) q = k*q :=
    (quadratic_density_hasDerivAt k q).deriv
  have hf' : HasFDerivAt
      (fun p : LinearInputAreaParameters.Parameters => ∫ s in 0..ℓ, k*(deriv θ s+B s p)^2/2)
      (∫ s in 0..ℓ, (k*deriv θ s) • B s) (0, (a 0, (b 0, c 0))) := by
    convert hf using 1 <;> simp only [map_zero, add_zero, hden, ha0, hb0, hc0]
    rfl
  have hp : HasDerivAt (fun t : ℝ => (t, (a t, (b t, c t))))
      (1, (0, (0, 0))) 0 := (hasDerivAt_id 0).prodMk (ha.prodMk (hb.prodMk hc))
  have hd := hf'.comp_hasDerivAt 0 hp
  have hint : IntervalIntegrable (fun s => (k*deriv θ s) • B s) volume 0 ℓ :=
    ((continuous_const.mul hθ.continuous_deriv_one).smul hB).intervalIntegrable _ _
  rw [ContinuousLinearMap.intervalIntegral_apply hint] at hd
  have he : (fun t => ∫ s in 0..ℓ, k*(deriv θ s+B s (t,(a t,(b t,c t))))^2/2) =
      (fun t => energy (fun q => k*q^2/2)
        (fun s => θ s+t*η.val s+a t*ξ₁.val s+b t*ξ₂.val s+c t*ξ₃.val s) ℓ) := by
    funext t
    unfold energy
    apply intervalIntegral.integral_congr
    intro s _
    have hds := (((((hθ.differentiable one_ne_zero s).hasDerivAt.add
      ((η.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul t)).add
      ((ξ₁.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (a t))).add
      ((ξ₂.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (b t))).add
      ((ξ₃.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (c t))).deriv
    change deriv (fun u => θ u+t*η.val u+a t*ξ₁.val u+b t*ξ₂.val u+c t*ξ₃.val u) s =
      deriv θ s+t*deriv η.val s+a t*deriv ξ₁.val s+b t*deriv ξ₂.val s+c t*deriv ξ₃.val s at hds
    dsimp only
    rw [hds]
    dsimp [B]
    rw [LinearInputAreaParameters.parameterLinear_apply]
    congr 2; ring
  simp only [Function.comp_def] at hd
  rw [he] at hd
  simpa only [smul_apply, smul_eq_mul, B,
    LinearInputAreaParameters.parameterLinear_apply, one_mul, zero_mul, add_zero] using hd

end LinearInputAreaFamily
