
/-!
# Actual derivatives and uniform bounds of finite real Fourier sums

These are functions of a real spatial coordinate, not a coefficient-only
model. Arbitrary finite real frequencies are allowed; integer frequencies
give the periodic Fourier polynomials used by the interval evaluator.
-/

namespace KerrKoopman.FourierSupBounds

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def polynomial (a0 : ℝ) (ω a b : ι → ℝ) (x : ℝ) : ℝ :=
  a0 + ∑ k, (a k * Real.cos (ω k * x) + b k * Real.sin (ω k * x))

def firstRate (ω a b : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ k, ω k * (b k * Real.cos (ω k * x) - a k * Real.sin (ω k * x))

def secondRate (ω a b : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ k, -(ω k) ^ 2 * (a k * Real.cos (ω k * x) + b k * Real.sin (ω k * x))

theorem sincos_term_bound (a b θ : ℝ) :
    |a * Real.cos θ + b * Real.sin θ| ≤ |a| + |b| := by
  calc
    _ ≤ |a * Real.cos θ| + |b * Real.sin θ| := abs_add_le _ _
    _ = |a| * |Real.cos θ| + |b| * |Real.sin θ| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * 1 + |b| * 1 := add_le_add
      (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg a))
      (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg b))
    _ = _ := by ring

theorem sincos_term_hasDerivAt (a b ω x : ℝ) :
    HasDerivAt (fun y => a * Real.cos (ω * y) + b * Real.sin (ω * y))
      (ω * (b * Real.cos (ω * x) - a * Real.sin (ω * x))) x := by
  have hx : HasDerivAt (fun y : ℝ => ω * y) ω x := by
    simpa using (hasDerivAt_id x).const_mul ω
  convert (hx.cos.const_mul a).add (hx.sin.const_mul b) using 1
  ring

theorem first_term_hasDerivAt (a b ω x : ℝ) :
    HasDerivAt (fun y => ω * (b * Real.cos (ω * y) - a * Real.sin (ω * y)))
      (-ω ^ 2 * (a * Real.cos (ω * x) + b * Real.sin (ω * x))) x := by
  have hx : HasDerivAt (fun y : ℝ => ω * y) ω x := by
    simpa using (hasDerivAt_id x).const_mul ω
  convert ((hx.cos.const_mul b).sub (hx.sin.const_mul a)).const_mul ω using 1
  ring

theorem polynomial_hasDerivAt (a0 : ℝ) (ω a b : ι → ℝ) (x : ℝ) :
    HasDerivAt (polynomial a0 ω a b) (firstRate ω a b x) x := by
  exact (HasDerivAt.fun_sum (fun k _ => sincos_term_hasDerivAt (a k) (b k) (ω k) x)).const_add a0

theorem firstRate_hasDerivAt (ω a b : ι → ℝ) (x : ℝ) :
    HasDerivAt (firstRate ω a b) (secondRate ω a b x) x := by
  exact HasDerivAt.fun_sum (fun k _ => first_term_hasDerivAt (a k) (b k) (ω k) x)

theorem polynomial_deriv (a0 : ℝ) (ω a b : ι → ℝ) :
    deriv (polynomial a0 ω a b) = firstRate ω a b := by
  funext x
  exact (polynomial_hasDerivAt a0 ω a b x).deriv

theorem polynomial_second_deriv (a0 : ℝ) (ω a b : ι → ℝ) :
    deriv (deriv (polynomial a0 ω a b)) = secondRate ω a b := by
  rw [polynomial_deriv]
  funext x
  exact (firstRate_hasDerivAt ω a b x).deriv

/-- The constant background does not enter the perturbation amplitude. -/
theorem amplitude_bound (a0 : ℝ) (ω a b : ι → ℝ) (x : ℝ) :
    |polynomial a0 ω a b x - a0| ≤ ∑ k, (|a k| + |b k|) := by
  simp only [polynomial, add_sub_cancel_left]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun k _ => sincos_term_bound (a k) (b k) (ω k * x)))

/-- Actual first spatial derivative bounded by the coefficient slope budget. -/
theorem slope_bound (a0 : ℝ) (ω a b : ι → ℝ) (x : ℝ) :
    |deriv (polynomial a0 ω a b) x| ≤ ∑ k, |ω k| * (|a k| + |b k|) := by
  rw [polynomial_deriv]
  unfold firstRate
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h := sincos_term_bound (b k) (-a k) (ω k * x)
  simpa only [neg_mul, ← sub_eq_add_neg, abs_neg, add_comm] using h

/-- Actual second spatial derivative bounded by the curvature budget. -/
theorem curvature_bound (a0 : ℝ) (ω a b : ι → ℝ) (x : ℝ) :
    |deriv (deriv (polynomial a0 ω a b)) x| ≤ ∑ k, (ω k) ^ 2 * (|a k| + |b k|) := by
  rw [polynomial_second_deriv]
  unfold secondRate
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (sincos_term_bound (a k) (b k) (ω k * x)) (sq_nonneg _)

theorem polynomial_contDiff (a0 : ℝ) (ω a b : ι → ℝ) (n : ℕ∞) :
    ContDiff ℝ n (polynomial a0 ω a b) := by
  unfold polynomial
  fun_prop

theorem iteratedDeriv_two_eq (a0 : ℝ) (ω a b : ι → ℝ) :
    iteratedDeriv 2 (polynomial a0 ω a b) = secondRate ω a b := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact polynomial_second_deriv a0 ω a b

end

end KerrKoopman.FourierSupBounds
