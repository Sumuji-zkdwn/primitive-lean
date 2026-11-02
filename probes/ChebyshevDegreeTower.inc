/-!
# Rational-function extension degree for the generic Chebyshev quotient

For a natural number m, the rational function (X^(2m)+1)/X^m
is the unnormalised Chebyshev quotient z^m+z^(-m).
The normalized target t differs by a nonzero constant factor 2.

This source is an independent probe, not included in the registered proof
count before Lean verification and full integration audit.
-/
noncomputable section

namespace LinearInputChebyshevTower

open Polynomial
open IntermediateField

def quotientNumerator (m : ℕ) : Polynomial ℂ :=
  X ^ (2 * m) + 1

def quotientDenominator (m : ℕ) : Polynomial ℂ :=
  X ^ m

def genericQuotient (m : ℕ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (quotientNumerator m) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (quotientDenominator m)

/-- Explicit Bezout certificate. -/
theorem numerator_sub_denominator_sq (m : ℕ) :
    quotientNumerator m -
      quotientDenominator m * quotientDenominator m = 1 := by
  unfold quotientNumerator quotientDenominator
  rw [show 2 * m = m * 2 by omega, pow_mul]
  ring

theorem quotientDenominator_ne_zero (m : ℕ) :
    quotientDenominator m ≠ 0 := by
  unfold quotientDenominator
  exact pow_ne_zero _ (by simp)

theorem numerator_denominator_isCoprime (m : ℕ) :
    IsCoprime (quotientNumerator m) (quotientDenominator m) := by
  refine ⟨1, -(quotientDenominator m), ?_⟩
  calc
    (1 : Polynomial ℂ) * quotientNumerator m +
        -(quotientDenominator m) * quotientDenominator m =
      quotientNumerator m - quotientDenominator m * quotientDenominator m := by ring
    _ = 1 := numerator_sub_denominator_sq m

theorem quotient_gcd_one (m : ℕ) :
    GCDMonoid.gcd (quotientNumerator m) (quotientDenominator m) = 1 := by
  have hdiv : GCDMonoid.gcd (quotientNumerator m) (quotientDenominator m) ∣
      (1 : Polynomial ℂ) := by
    rw [← numerator_sub_denominator_sq m]
    exact dvd_sub
      (GCDMonoid.gcd_dvd_left _ _)
      (dvd_mul_of_dvd_left (GCDMonoid.gcd_dvd_right _ _) _)
  have hunit : IsUnit (GCDMonoid.gcd (quotientNumerator m) (quotientDenominator m)) :=
    isUnit_of_dvd_one hdiv
  have hn : normalize (GCDMonoid.gcd (quotientNumerator m) (quotientDenominator m)) = 1 :=
    (normalize_eq_one).2 hunit
  simpa only [NormalizedGCDMonoid.normalize_gcd] using hn

theorem quotient_num (m : ℕ) :
    (genericQuotient m).num = quotientNumerator m := by
  unfold genericQuotient
  rw [RatFunc.num_div, quotient_gcd_one]
  simp [quotientDenominator]

theorem quotient_denom (m : ℕ) :
    (genericQuotient m).denom = quotientDenominator m := by
  unfold genericQuotient
  rw [RatFunc.denom_div _ (quotientDenominator_ne_zero m), quotient_gcd_one]
  simp [quotientDenominator]

theorem finrank_genericQuotient (m : ℕ) :
    Module.finrank ℂ⟮genericQuotient m⟯ (RatFunc ℂ) = 2 * m := by
  calc
    Module.finrank ℂ⟮genericQuotient m⟯ (RatFunc ℂ) =
        max (genericQuotient m).num.natDegree
            (genericQuotient m).denom.natDegree :=
      RatFunc.finrank_eq_max_natDegree (genericQuotient m)
    _ = 2 * m := by
      rw [quotient_num, quotient_denom]
      simp only [quotientNumerator, quotientDenominator,
        natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
      omega

end LinearInputChebyshevTower
