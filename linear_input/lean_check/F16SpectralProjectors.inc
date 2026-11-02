/-!
Finite spectral projectors for the *actual* signed F16 left pencil.

All matrix identities are evaluated over the rational numbers against the
existing integer Cayley-Dickson sign table; no assumed spectral data.
This establishes the three rational spectral subspaces with multiplicities
4, 4 and 8. Parameter-dependent real pseudoinverses follow separately.
-/

noncomputable section
open scoped Matrix

namespace LinearInputF16Spectral

open LinearInputF16Determinant

abbrev Idx := Fin 16
abbrev QMat := Matrix Idx Idx ℚ

/-- Left actions of the actual basis units, cast from the verified table. -/
abbrev leftThreeQ : QMat := fun i j => (entryThree i j : ℚ)
abbrev leftTenQ : QMat := fun i j => (entryTen i j : ℚ)

/-- The only eight coordinates on which the cross term acts. -/
abbrev active (i : Idx) : Prop :=
  (4 ≤ i.val ∧ i.val < 8) ∨ 12 ≤ i.val

/-- Diagonal of the real-eigenvalue sector, as an exact rational matrix. -/
abbrev realSector : QMat :=
  fun i j => if i = j ∧ ((4 ≤ i.val ∧ i.val < 8) ∨ 12 ≤ i.val) then 1 else 0

/-- Exact symmetric cross matrix L3^T L10 + L10^T L3. -/
abbrev cross : QMat := fun i j =>
  if (i.val = 4 ∧ j.val = 13) ∨ (i.val = 13 ∧ j.val = 4) ∨
     (i.val = 7 ∧ j.val = 14) ∨ (i.val = 14 ∧ j.val = 7) then -2
  else if (i.val = 5 ∧ j.val = 12) ∨ (i.val = 12 ∧ j.val = 5) ∨
          (i.val = 6 ∧ j.val = 15) ∨ (i.val = 15 ∧ j.val = 6) then 2
  else 0

theorem leftThreeQ_orthogonal : leftThreeQᵀ * leftThreeQ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem leftTenQ_orthogonal : leftTenQᵀ * leftTenQ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- No approximating cross operator is used: this is an entrywise equality. -/
theorem cross_from_actual_F16 :
    leftThreeQᵀ * leftTenQ + leftTenQᵀ * leftThreeQ = cross := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Orthogonal spectral projections for cross-term eigenvalues +2, -2, 0. -/
abbrev plus : QMat := ((1 / 2 : ℚ) • realSector) + ((1 / 4 : ℚ) • cross)
abbrev minus : QMat := ((1 / 2 : ℚ) • realSector) - ((1 / 4 : ℚ) • cross)
abbrev zero : QMat := 1 - realSector

theorem projector_sum : plus + minus + zero = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem plus_idempotent : plus * plus = plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem minus_idempotent : minus * minus = minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem zero_idempotent : zero * zero = zero := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem plus_minus_zero : plus * minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem plus_zero_zero : plus * zero = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem minus_zero_zero : minus * zero = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem plus_symmetric : plusᵀ = plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem minus_symmetric : minusᵀ = minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem zero_symmetric : zeroᵀ = zero := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Exact eigenvalues of the cross term, without numerical diagonalization. -/
theorem cross_plus : cross * plus = (2 : ℚ) • plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem cross_minus : cross * minus = (-2 : ℚ) • minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem cross_zero : cross * zero = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Traces: 4 positive, 4 negative and 8 zero cross-term dimensions. -/
theorem plus_trace : (∑ i : Idx, plus i i) = 4 := by decide

theorem minus_trace : (∑ i : Idx, minus i i) = 4 := by decide

theorem zero_trace : (∑ i : Idx, zero i i) = 8 := by decide

end LinearInputF16Spectral
