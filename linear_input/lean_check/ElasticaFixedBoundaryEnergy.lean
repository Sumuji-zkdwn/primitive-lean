import ElasticaFixedBoundaryWitness

noncomputable section
open scoped Interval
namespace FixedBoundaryExactEnergy
open FixedBoundaryWitness

theorem trig_identity (x : ℝ) :
    (Real.cos x - Real.cos (2 * x))^2 =
      1 + Real.cos (2 * x) / 2 + Real.cos (4 * x) / 2 -
        Real.cos x - Real.cos (3 * x) := by
  have h₄ : Real.cos (4 * x) = 2 * (2 * Real.cos x^2 - 1)^2 - 1 := by
    have h := Real.cos_two_mul (2 * x)
    have he : 2 * (2 * x) = 4 * x := by ring
    rw [he] at h
    rw [Real.cos_two_mul x] at h
    exact h
  simp only [h₄, Real.cos_three_mul, Real.cos_two_mul]
  ring

theorem cos_integral_nat (n : ℕ) (hn : n ≠ 0) :
    (∫ s in (0 : ℝ)..1, Real.cos (((n : ℝ) * (2 * Real.pi)) * s)) = 0 := by
  have hc : (n : ℝ) * (2 * Real.pi) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hn) (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hc]
  have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    have he : (n : ℝ) * (2 * Real.pi) = ((2 * n : ℕ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [he, Real.sin_nat_mul_pi]
  simp [integral_cos, hs]

theorem deriv_f_sq (s : ℝ) :
    (deriv f s)^2 = Real.pi^2 *
      (1 + Real.cos (4 * Real.pi * s) / 2 +
        Real.cos (8 * Real.pi * s) / 2 -
        Real.cos (2 * Real.pi * s) - Real.cos (6 * Real.pi * s)) := by
  rw [(hasDeriv_f s).deriv]
  have h := trig_identity (2 * Real.pi * s)
  have h₂ : 2 * (2 * Real.pi * s) = 4 * Real.pi * s := by ring
  have h₃ : 3 * (2 * Real.pi * s) = 6 * Real.pi * s := by ring
  have h₄ : 4 * (2 * Real.pi * s) = 8 * Real.pi * s := by ring
  rw [h₂, h₃, h₄] at h
  calc
    _ = Real.pi^2 * (Real.cos (2 * Real.pi * s) -
          Real.cos (4 * Real.pi * s))^2 := by ring
    _ = _ := by rw [h]

theorem trig_combo_integral :
    (∫ s in (0 : ℝ)..1,
      (1 + Real.cos (4 * Real.pi * s) / 2 +
        Real.cos (8 * Real.pi * s) / 2 -
        Real.cos (2 * Real.pi * s) - Real.cos (6 * Real.pi * s))) = 1 := by
  have h₁ : (∫ s in (0 : ℝ)..1, Real.cos (2 * Real.pi * s)) = 0 := by
    simp
  have h₂ : (∫ s in (0 : ℝ)..1, Real.cos (4 * Real.pi * s)) = 0 := by
    have h := cos_integral_nat 2 (by norm_num)
    norm_num only [Nat.cast_ofNat, ← mul_assoc] at h
    exact h
  have h₃ : (∫ s in (0 : ℝ)..1, Real.cos (6 * Real.pi * s)) = 0 := by
    have h := cos_integral_nat 3 (by norm_num)
    norm_num only [Nat.cast_ofNat, ← mul_assoc] at h
    exact h
  have h₄ : (∫ s in (0 : ℝ)..1, Real.cos (8 * Real.pi * s)) = 0 := by
    have h := cos_integral_nat 4 (by norm_num)
    norm_num only [Nat.cast_ofNat, ← mul_assoc] at h
    exact h
  simp (disch := apply Continuous.intervalIntegrable <;> fun_prop)
    [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_div, h₁, h₂, h₃, h₄]

theorem quadratic_bending_value (i : Fin 3) :
    quadraticBending i = Real.pi^2 := by
  rw [quadratic_bending_equal i]
  change (∫ s in (0 : ℝ)..1, (deriv f s)^2) = Real.pi^2
  simp_rw [deriv_f_sq, intervalIntegral.integral_const_mul, trig_combo_integral, mul_one]

theorem represented_curve_energy (θ : RepresentedCurve) :
    (∫ s in (0 : ℝ)..1, (Elastica.curvature θ.val s)^2) = Real.pi^2 := by
  obtain ⟨i, hi⟩ := θ.property
  rw [← hi]
  exact quadratic_bending_value i

/-- Combined geometric realization with its exact quadratic bending value. -/
theorem exact_represented_realization :
    (∀ θ : RepresentedCurve, ContDiff ℝ ⊤ θ.val) ∧
    (∀ (θ : RepresentedCurve) (s : ℝ),
      (deriv (Elastica.xCoord θ.val 0) s)^2 +
        (deriv (Elastica.yCoord θ.val 0) s)^2 = 1) ∧
    (∀ θ φ : RepresentedCurve,
      θ.val 0 = φ.val 0 ∧ θ.val 1 = φ.val 1 ∧
      Elastica.xCoord θ.val 0 1 = Elastica.xCoord φ.val 0 1 ∧
      Elastica.yCoord θ.val 0 1 = Elastica.yCoord φ.val 0 1) ∧
    (∀ θ : RepresentedCurve,
      (∫ s in (0 : ℝ)..1, (Elastica.curvature θ.val s)^2) = Real.pi^2) ∧
    (∃ q r : LinearInputOperatorWords.State curveObserver
        (LinearInputOperatorRefinement.sumStep curveOld curveFresh),
      q ≠ r ∧ LinearInputOperatorRefinement.forget curveObserver curveOld curveFresh q =
        LinearInputOperatorRefinement.forget curveObserver curveOld curveFresh r) :=
  ⟨represented_curve_smooth, represented_unit_speed, represented_curve_boundary,
    represented_curve_energy, represented_curve_split⟩

#print axioms quadratic_bending_value
#print axioms exact_represented_realization

end FixedBoundaryExactEnergy
