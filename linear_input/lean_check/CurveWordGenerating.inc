/-!
Formal generating functions of finite weighted transition matrices. Their
coefficients are actual matrix powers; the resolvent identity and a polynomial
numerator/denominator certificate follow from coefficient recursion and the
adjugate identity, over any commutative coefficient ring.
-/

noncomputable section

namespace LinearInputCurveWordGenerating

variable {Q R : Type*} [Fintype Q] [DecidableEq Q] [CommRing R]

def matrixSeries (M : Matrix Q Q R) : Matrix Q Q (PowerSeries R) :=
  fun i j => PowerSeries.mk (fun n => (M ^ n) i j)

def resolvent (M : Matrix Q Q R) : Matrix Q Q (PowerSeries R) :=
  1 - Matrix.of (fun i j => PowerSeries.X * PowerSeries.C (M i j))

def polynomialResolvent (M : Matrix Q Q R) : Matrix Q Q (Polynomial R) :=
  1 - Matrix.of (fun i j => Polynomial.X * Polynomial.C (M i j))

theorem matrixSeries_coeff (M : Matrix Q Q R) (i j : Q) (n : ℕ) :
    PowerSeries.coeff n (matrixSeries M i j) = (M ^ n) i j := PowerSeries.coeff_mk _ _

theorem resolvent_mul_series (M : Matrix Q Q R) : resolvent M * matrixSeries M = 1 := by
  unfold resolvent
  rw [Matrix.sub_mul, Matrix.one_mul]
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [matrixSeries, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply]
  | succ n =>
    simp [matrixSeries, Matrix.sub_apply, Matrix.mul_apply,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, Matrix.one_apply,
      pow_succ']
    split_ifs <;> simp [PowerSeries.coeff_one]

theorem polynomialResolvent_to_series (M : Matrix Q Q R) :
    Polynomial.coeToPowerSeries.ringHom.mapMatrix (polynomialResolvent M) = resolvent M := by
  apply Matrix.ext
  intro i j
  simp [polynomialResolvent, resolvent, Matrix.sub_apply, Matrix.one_apply,
    RingHom.mapMatrix_apply]
  split_ifs <;> simp [mul_comm]

theorem denominator_constantCoeff (M : Matrix Q Q R) :
    (polynomialResolvent M).det.coeff 0 = 1 := by
  change Polynomial.constantCoeff ((polynomialResolvent M).det) = 1
  rw [RingHom.map_det]
  have he : Polynomial.constantCoeff.mapMatrix (polynomialResolvent M) = (1 : Matrix Q Q R) := by
    apply Matrix.ext
    intro i j
    simp [polynomialResolvent, RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [he, Matrix.det_one]

theorem determinant_mul_series (M : Matrix Q Q R) :
    (resolvent M).det • matrixSeries M = (resolvent M).adjugate := by
  have he := congrArg (fun A => (resolvent M).adjugate * A) (resolvent_mul_series M)
  dsimp only at he
  rwa [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_one] at he

theorem polynomial_denominator_certificate (M : Matrix Q Q R) (i j : Q) :
    ((polynomialResolvent M).det : PowerSeries R) * matrixSeries M i j =
      ((polynomialResolvent M).adjugate i j : PowerSeries R) := by
  have hd := Polynomial.coeToPowerSeries.ringHom.map_det (polynomialResolvent M)
  have ha := Polynomial.coeToPowerSeries.ringHom.map_adjugate (polynomialResolvent M)
  rw [polynomialResolvent_to_series] at hd ha
  have he := congrArg (fun A : Matrix Q Q (PowerSeries R) => A i j) (determinant_mul_series M)
  change (resolvent M).det * matrixSeries M i j = (resolvent M).adjugate i j at he
  rw [← hd, ← ha] at he
  exact he

def rowSeries (M : Matrix Q Q R) (i : Q) : PowerSeries R := ∑ j, matrixSeries M i j

theorem rowSeries_coeff (M : Matrix Q Q R) (i : Q) (n : ℕ) :
    PowerSeries.coeff n (rowSeries M i) = ∑ j, (M ^ n) i j := by
  simp [rowSeries, matrixSeries_coeff]

/-- Rationality is certified by explicit polynomials with denominator
constant coefficient one. This also applies to Laurent-polynomial weights. -/
theorem row_generating_function_rational (M : Matrix Q Q R) (i : Q) :
    ∃ P D : Polynomial R, D.coeff 0 = 1 ∧
      (D : PowerSeries R) * rowSeries M i = (P : PowerSeries R) := by
  refine ⟨∑ j, (polynomialResolvent M).adjugate i j,
    (polynomialResolvent M).det, denominator_constantCoeff M, ?_⟩
  simp only [rowSeries, Finset.mul_sum, polynomial_denominator_certificate]
  exact (map_sum Polynomial.coeToPowerSeries.ringHom _ _).symm

end LinearInputCurveWordGenerating
