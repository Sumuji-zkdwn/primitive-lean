/-!
# The real 16 by 16 left-pencil determinant

The full determinant of the explicitly tabulated sedenion left action
L_(e3) + t L_(e10), for an arbitrary real parameter t, is calculated
using two explicit bijections that reorder the rows and the columns
into eight 2 by 2 blocks.

All calculations use the original integer Cayley-Dickson sign table.
This is an actual Matrix.det identity, not a statement about a
separate polynomial or a list of numerical sample values.
-/

noncomputable section

namespace LinearInputF16Determinant

open LinearInputF16Holonomy LinearInputF16Recovery

/-- The same signed-basis left pencil as intPencil, with a real parameter. -/
def realPencilAll (t : ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun k j =>
    (if rightIndex (3 : Fin 16) j = k then (eps (3 : Fin 16) j : ℝ) else 0) +
    t * (if rightIndex (10 : Fin 16) j = k then (eps (10 : Fin 16) j : ℝ) else 0)

/-- Local block-row 0 is row e3*ea, block-row 1 is row e10*ea. -/
def rowCoord (p : Fin 2 × Fin 8) : Fin 16 :=
  if p.1 = 0 then rightIndex (3 : Fin 16) (low p.2)
  else rightIndex (10 : Fin 16) (low p.2)

/-- Local block-column 0 is ea, block-column 1 is e_(a xor 9). -/
def colCoord (p : Fin 2 × Fin 8) : Fin 16 :=
  if p.1 = 0 then low p.2 else partnerIndex p.2

/-- Explicit inverse for the row permutation (no choice is used). -/
def rowDecode (k : Fin 16) : Fin 2 × Fin 8 :=
  (if k.val < 8 then 0 else 1,
   ⟨(Nat.xor k.val (if k.val < 8 then 3 else 10)) % 8,
    Nat.mod_lt _ (by decide)⟩)

/-- Explicit inverse for the column permutation. -/
def colDecode (k : Fin 16) : Fin 2 × Fin 8 :=
  (if k.val < 8 then 0 else 1,
   ⟨(if k.val < 8 then k.val else Nat.xor k.val 9) % 8,
    Nat.mod_lt _ (by decide)⟩)

def rowEquiv : (Fin 2 × Fin 8) ≃ Fin 16 where
  toFun := rowCoord
  invFun := rowDecode
  left_inv := by decide
  right_inv := by decide

def colEquiv : (Fin 2 × Fin 8) ≃ Fin 16 where
  toFun := colCoord
  invFun := colDecode
  left_inv := by decide
  right_inv := by decide

/-- The combined row/column permutation is even. -/
theorem reindex_sign :
    Equiv.Perm.sign (colEquiv.symm.trans rowEquiv) = 1 := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  decide

/-- An explicit 2 by 2 block of the left pencil. -/
def block (a : Fin 8) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    if i = 0 then
      if j = 0 then (eps (3 : Fin 16) (low a) : ℝ)
      else t * (eps (10 : Fin 16) (partnerIndex a) : ℝ)
    else
      if j = 0 then t * (eps (10 : Fin 16) (low a) : ℝ)
      else (eps (3 : Fin 16) (partnerIndex a) : ℝ)

/-- The actual real left pencil, after the two explicit reindexings,
is exactly the direct sum of eight 2 by 2 blocks. -/
theorem reindexed_blocks (t : ℝ) :
    (Matrix.reindex rowEquiv.symm colEquiv.symm) (realPencilAll t) =
      Matrix.blockDiagonal (fun a : Fin 8 => block a t) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change realPencilAll t (rowCoord (i, a)) (colCoord (j, b)) =
    (if a = b then block a t i j else 0)
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [realPencilAll, rowCoord, colCoord, block,
      rightIndex, low, partnerIndex, eps, epsTable] <;> ring

/-- Four blocks contribute a signed (1+t^2), and four contribute
(1-t^2), for arbitrary real t. -/
theorem block_det (a : Fin 8) (t : ℝ) :
    (block a t).det =
      (if a.val < 4 then
        (if a.val = 0 ∨ a.val = 3 then -(1 + t ^ 2) else (1 + t ^ 2))
       else 1 - t ^ 2) := by
  rw [Matrix.det_fin_two]
  fin_cases a <;>
    norm_num [block, low, partnerIndex, eps, epsTable] <;> ring

/-- The complete 16 dimensional real left pencil determinant. -/
theorem realPencilAll_det (t : ℝ) :
    (realPencilAll t).det = (1 - t ^ 2) ^ 4 * (1 + t ^ 2) ^ 4 := by
  calc
    (realPencilAll t).det =
        ((Matrix.reindex rowEquiv.symm colEquiv.symm) (realPencilAll t)).det := by
      simpa [reindex_sign] using
        (Matrix.det_reindex rowEquiv.symm colEquiv.symm (realPencilAll t)).symm
    _ = (Matrix.blockDiagonal (fun a : Fin 8 => block a t)).det := by
      rw [reindexed_blocks]
    _ = ∏ a : Fin 8, (block a t).det := Matrix.det_blockDiagonal _
    _ = (1 - t ^ 2) ^ 4 * (1 + t ^ 2) ^ 4 := by
      simp_rw [block_det]
      simp [Fin.prod_univ_succ] <;> ring

end LinearInputF16Determinant
