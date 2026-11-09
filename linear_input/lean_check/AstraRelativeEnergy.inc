
/-!
# Kerr relative electric energy and nonlinear remainder

These are pointwise exact identities and inequalities for arbitrary real
electric fields. The base field is `e`, the comparison field is `v`. They
provide coefficients independent of a spatial discretization, but do not
assert PDE existence, a Galerkin limit, or a time-evolution estimate.
-/

namespace KerrKoopman.RelativeEnergy

noncomputable section

open Riccati PrimitiveConstitutive

/-- Physical electric relative energy, expressed in constitutive coordinates. -/
def electricGap (e v : ℝ) : ℝ :=
  FiniteEnergy.density v 0 - FiniteEnergy.density e 0 -
    e * (constitutive v - constitutive e)

/-- The physical relative energy is precisely the reversed primitive
coenergy support gap, using the already proved Legendre identity. -/
theorem electricGap_eq_reverse_primitive (e v : ℝ) :
    electricGap e v = coenergy e - coenergy v - constitutive v * (e - v) := by
  unfold electricGap
  rw [physical_density_legendre, physical_density_legendre]
  ring

/-- Completing the square in the original primitive gap yields a global
quadratic-plus-quartic lower bound, without bounding the comparison field. -/
theorem electricGap_decomposition (e v : ℝ) :
    electricGap e v = (v - e) ^ 2 / 2 + (v - e) ^ 4 / 36 +
      (v - e) ^ 2 * (e + 2 * (v - e) / 3) ^ 2 / 2 := by
  rw [electricGap_eq_reverse_primitive, constitutive_gap]
  ring

theorem electricGap_lower_bound (e v : ℝ) :
    (v - e) ^ 2 / 2 + (v - e) ^ 4 / 36 ≤ electricGap e v := by
  rw [electricGap_decomposition]
  have h : 0 ≤ (v - e) ^ 2 * (e + 2 * (v - e) / 3) ^ 2 / 2 := by positivity
  linarith

theorem electricGap_nonneg (e v : ℝ) : 0 ≤ electricGap e v := by
  have h := electricGap_lower_bound e v
  have hq : 0 ≤ (v - e) ^ 4 := by positivity
  nlinarith [sq_nonneg (v - e)]

theorem square_error_le_gap (e v : ℝ) :
    (v - e) ^ 2 ≤ 2 * electricGap e v := by
  have h := electricGap_lower_bound e v
  have hq : 0 ≤ (v - e) ^ 4 := by positivity
  linarith

/-- The quartic part absorbs cubic error globally, including large fields. -/
theorem cubic_error_le_gap (e v : ℝ) :
    |v - e| ^ 3 / 3 ≤ 2 * electricGap e v := by
  have hl := electricGap_lower_bound e v
  have hs := sq_nonneg ((v - e) ^ 2 / 6 - |v - e|)
  have ha := sq_abs (v - e)
  have hc : (v - e) ^ 2 * |v - e| = |v - e| ^ 3 := by
    rw [← sq_abs (v - e)]
    ring
  have hq : 0 ≤ (v - e) ^ 4 := by positivity
  nlinarith

/-- The nonlinear Taylor numerator is controlled by the relative energy
with a coefficient depending only on the base field. -/
theorem nonlinear_numerator_le_gap (e v : ℝ) :
    |(v - e) ^ 2 * (e + (v - e) / 3)| ≤
      2 * (|e| + 1) * electricGap e v := by
  have hs := square_error_le_gap e v
  have hc := cubic_error_le_gap e v
  have hmul := mul_le_mul_of_nonneg_left hs (abs_nonneg e)
  have htriangle : |e + (v - e) / 3| ≤ |e| + |v - e| / 3 := by
    simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)] using
      abs_add_le e ((v - e) / 3)
  have hp := mul_le_mul_of_nonneg_left htriangle (sq_nonneg (v - e))
  have hcube : (v - e) ^ 2 * |v - e| = |v - e| ^ 3 := by
    rw [← sq_abs (v - e)]
    ring
  rw [abs_mul, abs_of_nonneg (sq_nonneg (v - e))]
  nlinarith

/-- The actual Kerr constitutive Taylor remainder has this exact factorization. -/
theorem constitutive_remainder_identity (e v : ℝ) :
    (v - e) - (constitutive v - constitutive e) / (1 + e ^ 2) =
      -((v - e) ^ 2 * (e + (v - e) / 3)) / (1 + e ^ 2) := by
  have hn : 1 + e ^ 2 ≠ 0 := ne_of_gt (FiniteEnergy.constitutive_denominator_pos e)
  unfold constitutive
  field_simp
  ring

/-- A denominator-retaining pointwise bound, useful when matching the exact
relative-energy derivative before any coarse coefficient estimates. -/
theorem constitutive_remainder_le_gap (e v : ℝ) :
    |(v - e) - (constitutive v - constitutive e) / (1 + e ^ 2)| ≤
      (2 * (|e| + 1) * electricGap e v) / (1 + e ^ 2) := by
  rw [constitutive_remainder_identity, abs_div, abs_neg,
    abs_of_pos (FiniteEnergy.constitutive_denominator_pos e)]
  exact div_le_div_of_nonneg_right (nonlinear_numerator_le_gap e v)
    (le_of_lt (FiniteEnergy.constitutive_denominator_pos e))

/-- Even the base amplitude can be removed from the normalized remainder
bound: the single constant three works on the entire real state space. -/
theorem constitutive_remainder_le_three_gap (e v : ℝ) :
    |(v - e) - (constitutive v - constitutive e) / (1 + e ^ 2)| ≤
      3 * electricGap e v := by
  have hc : 2 * (|e| + 1) ≤ 3 * (1 + e ^ 2) := by
    nlinarith [sq_nonneg (3 * |e| - 1), sq_abs e]
  have hp := mul_le_mul_of_nonneg_right hc (electricGap_nonneg e v)
  apply (constitutive_remainder_le_gap e v).trans
  apply (div_le_iff₀ (FiniteEnergy.constitutive_denominator_pos e)).2
  nlinarith

end

end KerrKoopman.RelativeEnergy
