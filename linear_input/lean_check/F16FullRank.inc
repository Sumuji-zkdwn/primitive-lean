/-!
# Rank of the 16-dimensional F16 pencil from explicit block elimination

The preceding F16FullMatrix.inc constructs the actual full real matrix and
proves an eight-block decomposition. This follow-up eliminates each local
2x2 block with determinant-unit left and right elementary matrices. The
result is a diagonal 16x16 matrix, whose nonzero diagonal count is exactly
twelve at t=1 and t=-1.

The proof uses ordinary real linear algebra only; it does not identify
the non-associative sedenion algebra with a field extension.
-/

noncomputable section

namespace LinearInputF16FullRank

open LinearInputF16FullMatrix LinearInputF16Holonomy LinearInputF16Recovery

/-- Upper left unit coefficient of a local block. -/
def alpha (a : Fin 8) : ℝ := (eps (3 : Fin 16) (low a) : ℝ)

/-- Upper right coefficient of a local block. -/
def beta (a : Fin 8) (t : ℝ) : ℝ :=
  t * (eps (10 : Fin 16) (partnerIndex a) : ℝ)

/-- Lower left coefficient of a local block. -/
def gamma (a : Fin 8) (t : ℝ) : ℝ :=
  t * (eps (10 : Fin 16) (low a) : ℝ)

theorem alpha_sq (a : Fin 8) : alpha a ^ 2 = 1 := by
  fin_cases a <;> norm_num [alpha, low, eps, epsTable]

/-- Normalize the first pivot and eliminate the lower-left entry. -/
def localLeft (a : Fin 8) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 then (if j = 0 then alpha a else 0)
    else (if j = 0 then -(alpha a * gamma a t) else 1)

/-- Eliminate the upper-right entry. -/
def localRight (a : Fin 8) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 then (if j = 0 then 1 else -(alpha a * beta a t))
    else (if j = 0 then 0 else 1)

/-- Result of eliminating each 2x2 block: one pivot 1 and one pivot
alpha times its original determinant. -/
def localDiagonal (a : Fin 8) (t : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then 1 else alpha a * (localBlock a t).det

theorem localLeft_det (a : Fin 8) (t : ℝ) :
    (localLeft a t).det = alpha a := by
  rw [Matrix.det_fin_two]
  simp [localLeft]

theorem localRight_det (a : Fin 8) (t : ℝ) :
    (localRight a t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [localRight]

/-- Concrete Gaussian elimination in each of the eight blocks. -/
theorem local_diagonalization (a : Fin 8) (t : ℝ) :
    localLeft a t * localBlock a t * localRight a t =
      Matrix.diagonal (localDiagonal a t) := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [localLeft, localRight, localBlock, localDiagonal,
      Matrix.mul_apply, Matrix.det_fin_two, Matrix.diagonal_apply,
      Fin.sum_univ_two, alpha, beta, gamma, colOrder, low, partnerIndex,
      rightIndex, eps, epsTable] <;> ring

/-- The global elementary operations are block diagonal, hence invertible. -/
def globalLeft (t : ℝ) : Matrix BlockIndex BlockIndex ℝ :=
  Matrix.blockDiagonal (fun a : Fin 8 => localLeft a t)

def globalRight (t : ℝ) : Matrix BlockIndex BlockIndex ℝ :=
  Matrix.blockDiagonal (fun a : Fin 8 => localRight a t)

def globalBlocks (t : ℝ) : Matrix BlockIndex BlockIndex ℝ :=
  Matrix.blockDiagonal (fun a : Fin 8 => localBlock a t)

def globalDiagonal (t : ℝ) (p : BlockIndex) : ℝ :=
  localDiagonal p.2 t p.1

theorem globalLeft_det (t : ℝ) : (globalLeft t).det = 1 := by
  rw [globalLeft, Matrix.det_blockDiagonal]
  simp_rw [localLeft_det]
  norm_num [Fin.prod_univ_succ, alpha, low, eps, epsTable]

theorem globalRight_det (t : ℝ) : (globalRight t).det = 1 := by
  rw [globalRight, Matrix.det_blockDiagonal]
  simp_rw [localRight_det]
  simp

/-- The full (reindexed) 16x16 pencil is brought to diagonal form by
two invertible matrices, not just pointwise block determinants. -/
theorem global_diagonalization (t : ℝ) :
    globalLeft t * globalBlocks t * globalRight t =
      Matrix.diagonal (globalDiagonal t) := by
  calc
    globalLeft t * globalBlocks t * globalRight t =
        Matrix.blockDiagonal (fun a : Fin 8 =>
          localLeft a t * localBlock a t * localRight a t) := by
          simp only [globalLeft, globalBlocks, globalRight,
            ← Matrix.blockDiagonal_mul]
    _ = Matrix.blockDiagonal (fun a : Fin 8 =>
          Matrix.diagonal (localDiagonal a t)) := by
          congr 1
          funext a
          exact local_diagonalization a t
    _ = Matrix.diagonal (globalDiagonal t) := by
          rw [Matrix.blockDiagonal_diagonal]
          rfl

/-- At either real singular input exactly the 8 first pivots and the
4 second pivots of indices 0..3 remain nonzero. -/
theorem globalDiagonal_nonzero_iff (t : ℝ) (ht : t = 1 ∨ t = -1) (p : BlockIndex) :
    globalDiagonal t p ≠ 0 ↔ p.1 = 0 ∨ p.2.val < 4 := by
  rcases ht with rfl | rfl
  · rcases p with ⟨i,a⟩
    fin_cases i <;> fin_cases a <;>
      norm_num [globalDiagonal, localDiagonal, localBlock_det, alpha, low,
        eps, epsTable]
  · rcases p with ⟨i,a⟩
    fin_cases i <;> fin_cases a <;>
      norm_num [globalDiagonal, localDiagonal, localBlock_det, alpha, low,
        eps, epsTable]

theorem globalDiagonal_rank_twelve (t : ℝ) (ht : t = 1 ∨ t = -1) :
    (Matrix.diagonal (globalDiagonal t)).rank = 12 := by
  classical
  rw [Matrix.rank_diagonal]
  have hcard :
      Fintype.card {p : BlockIndex // p.1 = 0 ∨ p.2.val < 4} = 12 := by decide
  calc
    Fintype.card {p : BlockIndex // globalDiagonal t p ≠ 0} =
        Fintype.card {p : BlockIndex // p.1 = 0 ∨ p.2.val < 4} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (globalDiagonal_nonzero_iff t ht))
    _ = 12 := hcard

/-- The row and column elimination matrices have nonzero determinant. -/
theorem globalBlocks_rank_eq_diagonal (t : ℝ) :
    (globalBlocks t).rank = (Matrix.diagonal (globalDiagonal t)).rank := by
  have hL : IsUnit (globalLeft t).det := by
    rw [globalLeft_det]
    exact isUnit_one
  have hR : IsUnit (globalRight t).det := by
    rw [globalRight_det]
    exact isUnit_one
  have hchange :
      (globalLeft t * globalBlocks t * globalRight t).rank =
      (globalBlocks t).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det (globalRight t)
          (globalLeft t * globalBlocks t) hR]
    exact Matrix.rank_mul_eq_right_of_isUnit_det
      (globalLeft t) (globalBlocks t) hL
  rw [global_diagonalization] at hchange
  exact hchange.symm

/-- The actual real 16x16 left multiplication matrix has rank exactly 12 at
each of t=+1 and t=-1. -/
theorem full_rank_twelve (t : ℝ) (ht : t = 1 ∨ t = -1) :
    (leftMatrix t).rank = 12 := by
  have h := Matrix.rank_submatrix (leftMatrix t) rowEquiv colEquiv
  change ((leftMatrix t).submatrix rowOrder colOrder).rank =
    (leftMatrix t).rank at h
  rw [full_block_decomposition] at h
  exact h.symm.trans
    ((globalBlocks_rank_eq_diagonal t).trans (globalDiagonal_rank_twelve t ht))

/-- At every other real parameter the full determinant is nonzero and
the rank is the maximum possible value 16. -/
theorem full_rank_sixteen (t : ℝ) (ht : t ≠ 1 ∧ t ≠ -1) :
    (leftMatrix t).rank = 16 := by
  have hd : (leftMatrix t).det ≠ 0 := by
    intro h
    rcases (full_determinant_zero_iff t).mp h with h1 | h2
    · exact ht.1 h1
    · exact ht.2 h2
  have hu : IsUnit (leftMatrix t).det := isUnit_iff_ne_zero.mpr hd
  have hm : IsUnit (leftMatrix t) :=
    ((leftMatrix t).isUnit_iff_isUnit_det).2 hu
  simpa using Matrix.rank_of_isUnit (leftMatrix t) hm

/-- Complete real rank classification of this exact F16 left pencil. -/
theorem full_rank_classification (t : ℝ) :
    (leftMatrix t).rank = if t = 1 ∨ t = -1 then 12 else 16 := by
  split_ifs with h
  · exact full_rank_twelve t h
  · exact full_rank_sixteen t (by
      simp only [not_or] at h
      exact h)

end LinearInputF16FullRank
