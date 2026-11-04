import OrbitTraceFirstShell
import OrbitTraceLeadingDrop

/-!
# The actual linear transfer on Q[X]

Use the Polynomial.lsum linear map to extend
  X^k |-> canonicalMoment(p,a,k)
to arbitrary polynomials. Its deviation from the identity is a
genuine Q-linear operator, not just a model matrix.

The monomial image is known to lose exactly p+1 degrees for a != 0.
The full all-degree Jordan basis and rank formula still require
a finite-dimensional triangular-basis theorem.
-/

namespace OrbitTrace

open Polynomial

noncomputable def canonicalTransfer (p : ℕ) (a : ℚ) :
    Polynomial ℚ →ₗ[ℚ] Polynomial ℚ :=
  Polynomial.lsum (fun k : ℕ =>
    { toFun := fun c : ℚ => c • canonicalMoment p a k
      map_add' := by
        intro c d
        simp [add_smul]
      map_smul' := by
        intro c d
        simp [smul_eq_mul, mul_smul] })

theorem canonicalTransfer_X_pow (p k : ℕ) (a : ℚ) :
    canonicalTransfer p a ((X : Polynomial ℚ) ^ k) =
      canonicalMoment p a k := by
  classical
  change ((X : Polynomial ℚ) ^ k).sum
    (fun n c => c • canonicalMoment p a n) =
      canonicalMoment p a k
  rw [X_pow_eq_monomial]
  simp

noncomputable def canonicalDelta (p : ℕ) (a : ℚ) :
    Polynomial ℚ →ₗ[ℚ] Polynomial ℚ :=
  canonicalTransfer p a - LinearMap.id

theorem canonicalDelta_X_pow (p k : ℕ) (a : ℚ) :
    canonicalDelta p a ((X : Polynomial ℚ) ^ k) =
      canonicalMoment p a k - X ^ k := by
  simp [canonicalDelta, canonicalTransfer_X_pow]

theorem canonicalDelta_X_pow_exact_degree
    (p k : ℕ) (a : ℚ) (ha : a ≠ 0) (hk : p + 1 ≤ k) :
    (canonicalDelta p a ((X : Polynomial ℚ) ^ k)).degree =
      ((k - (p + 1) : ℕ) : WithBot ℕ) := by
  rw [canonicalDelta_X_pow]
  exact polynomial_moment_exact_degree_drop p a ha
    (canonicalMoment p a)
    (by intro j hj; exact canonicalMoment_initial p j a hj)
    (by intro j; exact canonicalMoment_recurrence p j a)
    k hk

theorem canonicalDelta_X_pow_coeff
    (p k : ℕ) (a : ℚ) (hk : p + 1 ≤ k) :
    (canonicalDelta p a ((X : Polynomial ℚ) ^ k)).coeff
        (k - (p + 1)) = -(((k - p : ℕ) : ℚ) * a) := by
  rw [canonicalDelta_X_pow]
  exact polynomial_moment_gap_coefficient p a
    (canonicalMoment p a)
    (by intro j hj; exact canonicalMoment_initial p j a hj)
    (by intro j; exact canonicalMoment_recurrence p j a)
    k hk

#print axioms OrbitTrace.canonicalTransfer_X_pow
#print axioms OrbitTrace.canonicalDelta_X_pow_exact_degree
#print axioms OrbitTrace.canonicalDelta_X_pow_coeff

end OrbitTrace
