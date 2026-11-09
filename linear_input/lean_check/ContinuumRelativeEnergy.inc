/-!
# Finite Kerr relative-energy rate: the spatial-operator-free cancellation

This is an algebraic bridge, NOT a PDE existence, convergence, or time-derivative
result. All arrays are finite, and Q is any skew real matrix. We use the exact
Kerr relative-energy inequalities already proved in AstraRelativeEnergy.inc.

The central point: the resulting bound contains no operator norm of Q.
For a true relative-energy time derivative, the caller must separately prove
that its derivative equals the rate expression below, with its reference
residuals obtained from an actual differentiable reference trajectory.
-/

namespace KerrKoopman.ContinuumRelativeEnergy

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The skew spatial derivative cancels the paired cross-terms exactly. -/
theorem skew_cross_cancel (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (p b : ι → ℝ) :
    (∑ i, (p i * (-FiniteEnergy.applyQ Q b i) +
      b i * (-FiniteEnergy.applyQ Q p i))) = 0 := by
  rw [Finset.sum_add_distrib]
  simp only [mul_neg, Finset.sum_neg_distrib]
  rw [FiniteEnergy.skew_pairing Q hQ p b]
  ring

/-- Algebraic rate identity before using the Kerr constitutive estimates.
    rD and rH denote residuals of the reference trajectory. -/
theorem skew_rate_identity (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i)
    (p b v c rD rH : ι → ℝ) :
    (∑ i, (p i * (-FiniteEnergy.applyQ Q b i - FiniteEnergy.applyQ Q v i) -
      c i * (-FiniteEnergy.applyQ Q v i + rD i) +
      b i * (-FiniteEnergy.applyQ Q p i - rH i))) =
    (∑ i, ((p i - c i) * (-FiniteEnergy.applyQ Q v i + rD i) -
      p i * rD i - b i * rH i)) := by
  calc
    _ = (∑ i, (p i * (-FiniteEnergy.applyQ Q b i) +
          b i * (-FiniteEnergy.applyQ Q p i))) +
        (∑ i, ((p i - c i) * (-FiniteEnergy.applyQ Q v i + rD i) -
          p i * rD i - b i * rH i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [skew_cross_cancel Q hQ p b, zero_add]

/-- Young's inequality and the two already proved Kerr gap inequalities.
    This is a pointwise estimate; no operator norm or mesh size occurs. -/
theorem pointwise_rate_budget (e a b dt rD rH M : ℝ)
    (hM : 0 ≤ M) (hdt : |dt| ≤ M) :
    ((a - e -
        (Riccati.constitutive a - Riccati.constitutive e) / (1 + e ^ 2)) * dt -
      (a - e) * rD - b * rH) ≤
    (3 * M + 1) * (RelativeEnergy.electricGap e a + b ^ 2 / 2) +
      (rD ^ 2 + rH ^ 2) / 2 := by
  have hg : 0 ≤ RelativeEnergy.electricGap e a :=
    RelativeEnergy.electricGap_nonneg e a
  have hp : (a - e) ^ 2 ≤ 2 * RelativeEnergy.electricGap e a :=
    RelativeEnergy.square_error_le_gap e a
  have hr := RelativeEnergy.constitutive_remainder_le_three_gap e a
  have hrem :
      (a - e -
        (Riccati.constitutive a - Riccati.constitutive e) / (1 + e ^ 2)) * dt ≤
      3 * M * RelativeEnergy.electricGap e a := by
    calc
      _ ≤ |(a - e -
        (Riccati.constitutive a - Riccati.constitutive e) / (1 + e ^ 2)) * dt| :=
          le_abs_self _
      _ = |a - e -
        (Riccati.constitutive a - Riccati.constitutive e) / (1 + e ^ 2)| * |dt| :=
          abs_mul _ _
      _ ≤ (3 * RelativeEnergy.electricGap e a) * |dt| :=
          mul_le_mul_of_nonneg_right hr (abs_nonneg _)
      _ ≤ (3 * RelativeEnergy.electricGap e a) * M :=
          mul_le_mul_of_nonneg_left hdt (mul_nonneg (by norm_num) hg)
      _ = 3 * M * RelativeEnergy.electricGap e a := by ring
  have hyD : -(a - e) * rD ≤ ((a - e) ^ 2 + rD ^ 2) / 2 := by
    nlinarith [sq_nonneg ((a - e) + rD)]
  have hyH : -(b * rH) ≤ (b ^ 2 + rH ^ 2) / 2 := by
    nlinarith [sq_nonneg (b + rH)]
  have hpos : 0 ≤ (3 * M) * (b ^ 2 / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hM)
      (div_nonneg (sq_nonneg b) (by norm_num))
  nlinarith [hrem, hp, hyD, hyH, hpos]

/-- Spatial-operator-free relative-energy rate budget for any finite skew Q.
    This is the crucial algebraic step toward a conditional smooth-PDE limit.
    A separate differentiability theorem is needed before Gronwall applies. -/
theorem finite_skew_rate_budget (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i)
    (e a b v rD rH : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hdt : ∀ i, |-FiniteEnergy.applyQ Q v i + rD i| ≤ M) :
    (∑ i, ((a i - e i) *
        (-FiniteEnergy.applyQ Q b i - FiniteEnergy.applyQ Q v i) -
      ((Riccati.constitutive (a i) - Riccati.constitutive (e i)) /
        (1 + (e i) ^ 2)) * (-FiniteEnergy.applyQ Q v i + rD i) +
      b i * (-FiniteEnergy.applyQ Q (fun j => a j - e j) i - rH i))) ≤
    (∑ i, ((3 * M + 1) *
        (RelativeEnergy.electricGap (e i) (a i) + (b i) ^ 2 / 2) +
        ((rD i) ^ 2 + (rH i) ^ 2) / 2)) := by
  have hbal := skew_rate_identity Q hQ
    (fun i => a i - e i) b v
    (fun i => (Riccati.constitutive (a i) - Riccati.constitutive (e i)) /
      (1 + (e i) ^ 2)) rD rH
  rw [hbal]
  exact Finset.sum_le_sum (fun i _ =>
    pointwise_rate_budget (e i) (a i) (b i)
      (-FiniteEnergy.applyQ Q v i + rD i) (rD i) (rH i) M hM (hdt i))

end

end KerrKoopman.ContinuumRelativeEnergy
