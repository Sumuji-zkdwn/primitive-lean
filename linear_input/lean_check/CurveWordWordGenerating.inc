/-!
Finite word sums over an arbitrary commutative coefficient ring have the
actual finite transfer matrix and a rational formal generating function.
Different letters with the same destination retain their multiplicities.
-/

noncomputable section

namespace LinearInputCurveWordWordGenerating

open LinearInputCurveWordFiniteState LinearInputCurveWordGenerating

variable {Q A R : Type*} [CommRing R]

def weightedWord (next : Q → A → Q) (weight : Q → A → R) (q : Q) : List A → R
  | [] => 1
  | a :: w => weight q a * weightedWord next weight (next q a) w

def wordSum [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (weight : Q → A → R) (n : ℕ) (q : Q) : R :=
  ∑ w ∈ words n, weightedWord next weight q w

def weightedMatrix [Fintype A] [DecidableEq Q]
    (next : Q → A → Q) (weight : Q → A → R) : Matrix Q Q R :=
  Matrix.of (fun q r => ∑ a : A, if next q a = r then weight q a else 0)

theorem wordSum_succ [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (weight : Q → A → R) (n : ℕ) (q : Q) :
    wordSum next weight (n + 1) q = ∑ a : A, weight q a * wordSum next weight n (next q a) := by
  unfold wordSum
  rw [LinearInputCurveWordTransfer.sum_words_succ]
  simp only [weightedWord, Finset.mul_sum]

theorem weightedMatrix_action [Fintype Q] [DecidableEq Q] [Fintype A]
    (next : Q → A → Q) (weight : Q → A → R) (v : Q → R) (q : Q) :
    ∑ r, weightedMatrix next weight q r * v r = ∑ a, weight q a * v (next q a) := by
  simp only [weightedMatrix, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem wordSum_eq_matrix_power [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (weight : Q → A → R) (n : ℕ) (q : Q) :
    wordSum next weight n q = ∑ r, (weightedMatrix next weight ^ n) q r := by
  induction n generalizing q with
  | zero => simp [wordSum, words, weightedWord, Matrix.one_apply]
  | succ n ih =>
    rw [wordSum_succ, pow_succ']
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← ih]
    exact (weightedMatrix_action next weight _ q).symm

theorem wordSum_generating_series [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (weight : Q → A → R) (q : Q) :
    PowerSeries.mk (fun n => wordSum next weight n q) = rowSeries (weightedMatrix next weight) q := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk, rowSeries_coeff, wordSum_eq_matrix_power]

/-- A polynomial quotient certificate for the genuine all-word generating
function, valid also when the edge weights are Laurent polynomials. -/
theorem all_word_generating_function_rational
    [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (weight : Q → A → R) (q : Q) :
    ∃ P D : Polynomial R, D.coeff 0 = 1 ∧
      (D : PowerSeries R) * PowerSeries.mk (fun n => wordSum next weight n q) = (P : PowerSeries R) := by
  rw [wordSum_generating_series]
  exact row_generating_function_rational _ q

end LinearInputCurveWordWordGenerating
