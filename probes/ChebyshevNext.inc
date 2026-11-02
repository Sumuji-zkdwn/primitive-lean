/-!
Rational-function and degree lemmas toward the generic Chebyshev Galois group.
Exploratory probe: only promote claims into registered source after the pinned
Lean compiler verifies them. No `sorry`, new axioms or `native_decide`.
-/
noncomputable section
namespace LinearInputChebyshevNext

open Polynomial
open LinearInputChebyshevDescent

theorem cubicPoly_natDegree :
    (cubicPoly (K := ℂ)).natDegree = 3 := by
  unfold cubicPoly
  compute_degree

theorem chebyPoly_natDegree (k : ℕ) :
    (chebyPoly (K := ℂ) k).natDegree = 3 ^ k := by
  induction k with
  | zero => simp [chebyPoly]
  | succ k ih =>
    change ((cubicPoly (K := ℂ)).comp (chebyPoly k)).natDegree = 3 ^ (k + 1)
    rw [Polynomial.natDegree_comp, cubicPoly_natDegree, ih, pow_succ]

/-- A rational-function indeterminate has square outside the constant field. -/
theorem generic_square_not_constant (c : ℂ) :
    (RatFunc.X : RatFunc ℂ) ^ 2 ≠ RatFunc.C c := by
  intro hc
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℂ).natDegree = 2 := by
    compute_degree
  have hpoly : (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℂ) ≠ 0 := by
    intro hh
    rw [hh] at hdeg
    norm_num at hdeg
  have hzero :
      Polynomial.aeval (RatFunc.X : RatFunc ℂ)
        (Polynomial.X ^ 2 - Polynomial.C c) = 0 := by
    simpa using (sub_eq_zero.mpr hc)
  exact hpoly ((transcendental_iff.mp (RatFunc.transcendental_X (K := ℂ))) _ hzero)

end LinearInputChebyshevNext
