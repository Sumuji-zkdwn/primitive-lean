/-!
Exact multivariable Laurent-polynomial counting for the four-state A/B arc
model. Integer x/y exponents and a natural cost exponent record the actual
integer endpoint and bending cost, retaining the number of colliding words.
-/

noncomputable section

namespace LinearInputCurveWordArcGenerating

open LinearInputCurveWordFinite LinearInputCurveWordFiniteState
open LinearInputCurveWordWordGenerating LinearInputCurveWordGenerating

abbrev Exponent := ℤ × ℤ × ℕ
abbrev LaurentWeights := AddMonoidAlgebra ℤ Exponent

def stateExponent (s : State) : Exponent := (s.1.1, s.1.2, s.2.2.1)

def edgeExponent (q : Fin 4) (a : Bool) : Exponent :=
  let d := rotate (if a then (3, 3) else (-1, 1)) q.val
  (d.1, d.2, if a then 1 else 9)

def monomial (e : Exponent) : LaurentWeights := AddMonoidAlgebra.single e 1

def arcWeight (q : Fin 4) (a : Bool) : LaurentWeights := monomial (edgeExponent q a)

theorem monomial_zero : monomial 0 = 1 := rfl

theorem monomial_add (e f : Exponent) : monomial (e + f) = monomial e * monomial f := by
  simp [monomial, AddMonoidAlgebra.single_mul_single]

theorem stateExponent_step (s : State) (a : Bool) :
    stateExponent (step s a) = stateExponent s + edgeExponent (arcPhase s) a := by
  cases a <;> simp [stateExponent, edgeExponent, step, arcPhase, rotate]

theorem monomial_fold (s : State) (w : List Bool) :
    monomial (stateExponent s) * weightedWord arcNext arcWeight (arcPhase s) w =
      monomial (stateExponent (w.foldl step s)) := by
  induction w generalizing s with
  | nil => simp [weightedWord]
  | cons a w ih =>
    simp only [weightedWord, List.foldl_cons, arcWeight]
    rw [← mul_assoc, ← monomial_add, ← stateExponent_step, ← arcPhase_step, ih]

/-- The monomial assigned to a word is exactly its actual integer endpoint
and its natural bending-cost count, not an unrelated formal word label. -/
theorem arc_word_monomial (w : List Bool) :
    weightedWord arcNext arcWeight 0 w = monomial (stateExponent (state w)) := by
  have he := monomial_fold ((0, 0), 0, 0, 0) w
  change monomial 0 * weightedWord arcNext arcWeight 0 w = monomial (stateExponent (state w)) at he
  simpa only [monomial_zero, one_mul] using he

theorem arc_coefficient_counts_words (n : ℕ) (e : Exponent) :
    (wordSum arcNext arcWeight n 0).coeff e =
      (((words (A := Bool) n).filter (fun w => stateExponent (state w) = e)).card : ℤ) := by
  classical
  change (AddMonoidAlgebra.coeff (wordSum arcNext arcWeight n 0)) e = _
  unfold wordSum
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp [arc_word_monomial, monomial, Finsupp.single_apply]

theorem arc_matrix_coefficients_exact (n : ℕ) (e : Exponent) :
    (∑ r : Fin 4, (weightedMatrix arcNext arcWeight ^ n) 0 r).coeff e =
      (((words (A := Bool) n).filter (fun w => stateExponent (state w) = e)).card : ℤ) := by
  rw [← wordSum_eq_matrix_power]
  exact arc_coefficient_counts_words n e

/-- The actual endpoint/cost counting series has a polynomial numerator and
denominator in the word-length variable, over the Laurent coefficient ring. -/
theorem arc_endpoint_cost_series_rational :
    ∃ P D : Polynomial LaurentWeights, D.coeff 0 = 1 ∧
      (D : PowerSeries LaurentWeights) *
        PowerSeries.mk (fun n => wordSum arcNext arcWeight n 0) = (P : PowerSeries LaurentWeights) :=
  all_word_generating_function_rational arcNext arcWeight 0

end LinearInputCurveWordArcGenerating
