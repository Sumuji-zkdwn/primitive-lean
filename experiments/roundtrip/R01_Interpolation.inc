import Mathlib.LinearAlgebra.Vandermonde

/-!
# Round trip 1: observation pencil → Lagrange interpolation → observation pencil

Input (baseline): `LinearInputObservation.energy A X u z = A z - u * X z`,
`recover_coordinate`, `recover_zero_input_energy`, `two_inputs_iff_pair`.

Translation: for fixed `z`, `u ↦ energy A X u z` is a polynomial of degree ≤ 1 in `u`.
Two observations are evaluations at two nodes; recovering `(A z, X z)` is inverting a
2×2 Vandermonde matrix, and the baseline zero-input formula is Lagrange interpolation
evaluated at the node `0`.
-/

noncomputable section
namespace RoundTrip01
open LinearInputObservation

/-- The observation matrix sending `(A z, X z)` to the two observed energies. -/
def obsMatrix (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, -u; 1, -v]

theorem obsMatrix_mulVec {S : Type*} (A X : S → ℝ) (u v : ℝ) (z : S) :
    (obsMatrix u v).mulVec ![A z, X z] = ![energy A X u z, energy A X v z] := by
  ext i
  fin_cases i <;> simp [obsMatrix, energy, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The observation matrix is the Vandermonde matrix at the nodes `-u, -v`. -/
theorem obsMatrix_eq_vandermonde (u v : ℝ) :
    obsMatrix u v = Matrix.vandermonde ![-u, -v] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [obsMatrix, Matrix.vandermonde]

theorem det_obsMatrix (u v : ℝ) : (obsMatrix u v).det = u - v := by
  rw [Matrix.det_fin_two]
  simp [obsMatrix]
  ring

/-- Invertibility of the observation matrix is exactly the baseline hypothesis `u ≠ v`. -/
theorem obsMatrix_isUnit_iff (u v : ℝ) : IsUnit (obsMatrix u v).det ↔ u ≠ v := by
  rw [det_obsMatrix, isUnit_iff_ne_zero, sub_ne_zero]

/-- Lagrange interpolation: the observation at any third input `w` is an affine
combination of the two observations. -/
theorem energy_interpolate {S : Type*} (A X : S → ℝ) {u v : ℝ} (huv : u ≠ v)
    (w : ℝ) (z : S) :
    energy A X w z =
      ((v - w) * energy A X u z + (w - u) * energy A X v z) / (v - u) := by
  have h : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  unfold energy
  field_simp
  ring

/-- Back-translation: the baseline `recover_zero_input_energy` is interpolation at `w = 0`. -/
theorem recover_zero_input_energy_of_interpolation {S : Type*} (A X : S → ℝ)
    {u v : ℝ} (huv : u ≠ v) (z : S) :
    (v * energy A X u z - u * energy A X v z) / (v - u) = A z := by
  have h := energy_interpolate A X huv 0 z
  have h0 : energy A X 0 z = A z := by simp [energy]
  rw [h0] at h
  rw [h]
  ring_nf

/-- The baseline slope formula is the derivative of the interpolating line. -/
theorem hasDerivAt_energy_input {S : Type*} (A X : S → ℝ) (z : S) (w : ℝ) :
    HasDerivAt (fun t => energy A X t z) (-X z) w := by
  unfold energy
  simpa using ((hasDerivAt_id w).mul_const (X z)).const_sub (A z)

/-- What is lost at a single node: one observation never separates the pair. -/
theorem single_input_not_injective (u : ℝ) :
    ∃ (A X : ℝ → ℝ) (z w : ℝ), energy A X u z = energy A X u w ∧ X z ≠ X w := by
  refine ⟨fun z => u * z, id, 0, 1, ?_, by norm_num⟩
  simp [energy]

/-- The two-observation recovery is exactly the inverse Vandermonde matrix. -/
theorem recover_by_inverse {S : Type*} (A X : S → ℝ) {u v : ℝ} (huv : u ≠ v) (z : S) :
    (obsMatrix u v)⁻¹.mulVec ![energy A X u z, energy A X v z] = ![A z, X z] := by
  have hdet : IsUnit (obsMatrix u v).det := (obsMatrix_isUnit_iff u v).2 huv
  rw [← obsMatrix_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
    Matrix.one_mulVec]

end RoundTrip01
