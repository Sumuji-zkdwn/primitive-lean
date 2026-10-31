/-!
# Complete real-rank classification of the F16 sedenion left pencil

This supplement joins two previously independently certified facts:
(1) the full 16x16 real determinant factorization, and
(2) rank 12 at the two singular parameters using integer certificates.

The real matrix realPencilAll t is the actual signed-basis left action
L_(e3) + t L_(e10), with the original Cayley-Dickson table.

For every real parameter t, its rank is exactly 12 at t = plus or minus one and
exactly 16 everywhere else. The comparison at t = plus or minus one is a matrix
equality with the existing integer-parameter realPencil after casting
to the reals, so the conclusion does not depend on an unproved
identification of two differently defined matrix families.
-/

noncomputable section

namespace LinearInputF16CompleteRank

open LinearInputF16Determinant

/-- At every integer t the real-parameter matrix coincides entrywise
with the earlier integer-parameter pencil after scalar extension to R. -/
theorem realPencilAll_of_int (t : ℤ) :
    realPencilAll (t : ℝ) = LinearInputF16Rank.realPencil t := by
  ext i j
  simp only [realPencilAll, LinearInputF16Rank.realPencil,
    LinearInputF16Rank.intPencil, Matrix.of_apply, Matrix.map_apply,
    entryThree, entryTen, map_add, map_mul]

/-- Transport the previous rank-12 certificate to the real pencil at +1. -/
theorem rank_at_plus_one : (realPencilAll 1).rank = 12 := by
  simpa using
    (congrArg Matrix.rank (realPencilAll_of_int (1 : ℤ))).trans
      LinearInputF16Rank.realPencil_plus_rank

/-- Transport the previous rank-12 certificate to the real pencil at -1. -/
theorem rank_at_minus_one : (realPencilAll (-1)).rank = 12 := by
  simpa using
    (congrArg Matrix.rank (realPencilAll_of_int (-1 : ℤ))).trans
      LinearInputF16Rank.realPencil_minus_rank

/-- The determinant vanishes at exactly two real parameters. -/
theorem det_zero_iff (t : ℝ) :
    (realPencilAll t).det = 0 ↔ t = 1 ∨ t = -1 := by
  rw [realPencilAll_det]
  constructor
  · intro hz
    have hleft : 1 - t ^ 2 = 0 := by
      by_contra hne
      have hl : (1 - t ^ 2) ^ 4 ≠ 0 := pow_ne_zero 4 hne
      have hr : (1 + t ^ 2) ^ 4 ≠ 0 := by positivity
      exact (mul_ne_zero hl hr) hz
    have hfactor : (1 - t) * (1 + t) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with ha | hb
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Singular parameters have rank 12, not merely rank below 16. -/
theorem rank_singular (t : ℝ) (ht : t = 1 ∨ t = -1) :
    (realPencilAll t).rank = 12 := by
  rcases ht with rfl | rfl
  · exact rank_at_plus_one
  · exact rank_at_minus_one

/-- Off the two singular points the determinant is nonzero, so the
actual real matrix has full column rank. -/
theorem rank_regular (t : ℝ) (ht : t ≠ 1 ∧ t ≠ -1) :
    (realPencilAll t).rank = 16 := by
  have hdet : (realPencilAll t).det ≠ 0 := by
    intro hz
    rcases (det_zero_iff t).mp hz with hpos | hneg
    · exact ht.1 hpos
    · exact ht.2 hneg
  have hunitDet : IsUnit (realPencilAll t).det := isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit (realPencilAll t) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hunitDet
  simpa using (Matrix.rank_of_isUnit (realPencilAll t) hunit)

/-- COMPLETE RANK CLASSIFICATION for every real parameter. -/
theorem rank_classification (t : ℝ) :
    (realPencilAll t).rank =
      if t = 1 ∨ t = -1 then 12 else 16 := by
  by_cases ht : t = 1 ∨ t = -1
  · simp only [if_pos ht]
    exact rank_singular t ht
  · simp only [if_neg ht]
    apply rank_regular t
    exact ⟨fun hpos => ht (Or.inl hpos),
      fun hneg => ht (Or.inr hneg)⟩

/-- Rank 12 is equivalent to being at one of the two singular inputs. -/
theorem rank_twelve_iff (t : ℝ) :
    (realPencilAll t).rank = 12 ↔ t = 1 ∨ t = -1 := by
  rw [rank_classification]
  by_cases ht : t = 1 ∨ t = -1
  · simp [ht]
  · simp [ht]

/-- Full rank is equivalent to avoiding both singular inputs. -/
theorem rank_sixteen_iff (t : ℝ) :
    (realPencilAll t).rank = 16 ↔ t ≠ 1 ∧ t ≠ -1 := by
  rw [rank_classification]
  by_cases ht : t = 1 ∨ t = -1
  · rcases ht with hpos | hneg
    · simp [hpos]
    · simp [hneg]
  · have hpair : t ≠ 1 ∧ t ≠ -1 := by
      constructor
      · intro hpos
        exact ht (Or.inl hpos)
      · intro hneg
        exact ht (Or.inr hneg)
    simp [hpair]

end LinearInputF16CompleteRank
