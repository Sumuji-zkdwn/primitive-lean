/-!
# The full real determinant of the 16-dimensional sedenion left pencil

The determinant of L_(e3) + t L_(e10) is obtained from eight 2 by 2
blocks. The crucial support equalities are proved over the integers
by exhaustive checking of the original finite Cayley-Dickson table,
rather than repeatedly normalizing real-valued expressions.
-/

noncomputable section

namespace LinearInputF16Determinant

open LinearInputF16Holonomy LinearInputF16Recovery

/-- The integer coefficient of left multiplication by e3 at row k, column j. -/
def entryThree (k j : Fin 16) : ℤ :=
  if rightIndex (3 : Fin 16) j = k then eps (3 : Fin 16) j else 0

/-- The integer coefficient of left multiplication by e10. -/
def entryTen (k j : Fin 16) : ℤ :=
  if rightIndex (10 : Fin 16) j = k then eps (10 : Fin 16) j else 0

/-- The signed-basis left pencil with an arbitrary real parameter t. -/
def realPencilAll (t : ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun k j => (entryThree k j : ℝ) + t * (entryTen k j : ℝ)

/-- First block coordinate chooses left e3 or e10; second is a low index. -/
def rowCoord (p : Fin 2 × Fin 8) : Fin 16 :=
  if p.1 = 0 then rightIndex (3 : Fin 16) (low p.2)
  else rightIndex (10 : Fin 16) (low p.2)

/-- First block coordinate chooses the low basis or its xor-9 partner. -/
def colCoord (p : Fin 2 × Fin 8) : Fin 16 :=
  if p.1 = 0 then low p.2 else partnerIndex p.2

def rowDecode (k : Fin 16) : Fin 2 × Fin 8 :=
  (if k.val < 8 then 0 else 1,
   ⟨(Nat.xor k.val (if k.val < 8 then 3 else 10)) % 8,
    Nat.mod_lt _ (by decide)⟩)

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

theorem reindex_sign :
    Equiv.Perm.sign (colEquiv.symm.trans rowEquiv) = 1 := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  decide

/-- The t-independent component of the local 2 by 2 block. -/
def blockThree (a : Fin 8) : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.of fun i j =>
    if i = 0 then
      if j = 0 then eps (3 : Fin 16) (low a) else 0
    else if j = 0 then 0 else eps (3 : Fin 16) (partnerIndex a)

/-- The coefficient of t in the local 2 by 2 block. -/
def blockTen (a : Fin 8) : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.of fun i j =>
    if i = 0 then
      if j = 0 then 0 else eps (10 : Fin 16) (partnerIndex a)
    else if j = 0 then eps (10 : Fin 16) (low a) else 0

/-- The entire 256-entry support calculation is performed over integers.
Each integer coefficient vanishes between distinct blocks. -/
theorem block_entry_coefficients (i j : Fin 2) (a b : Fin 8) :
    entryThree (rowCoord (i, a)) (colCoord (j, b)) =
        (if a = b then blockThree a i j else 0) ∧
      entryTen (rowCoord (i, a)) (colCoord (j, b)) =
        (if a = b then blockTen a i j else 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> decide

/-- The real 2 by 2 block, with exactly the original integer coefficients. -/
def block (a : Fin 8) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => (blockThree a i j : ℝ) + t * (blockTen a i j : ℝ)

/-- Explicit row/column reindexing gives an exact block diagonal matrix. -/
theorem reindexed_blocks (t : ℝ) :
    (Matrix.reindex rowEquiv.symm colEquiv.symm) (realPencilAll t) =
      Matrix.blockDiagonal (fun a : Fin 8 => block a t) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change (entryThree (rowCoord (i, a)) (colCoord (j, b)) : ℝ) +
      t * (entryTen (rowCoord (i, a)) (colCoord (j, b)) : ℝ) =
    (if a = b then block a t i j else 0)
  obtain ⟨h3, h10⟩ := block_entry_coefficients i j a b
  rw [h3, h10]
  by_cases h : a = b
  · simp [h, block]
  · simp [h]

/-- Four block determinants are signed (1+t^2); the other four
are 1-t^2, as exact identities for any real t. -/
theorem block_det (a : Fin 8) (t : ℝ) :
    (block a t).det =
      (if a.val < 4 then
        (if a.val = 0 ∨ a.val = 3 then -(1 + t ^ 2) else (1 + t ^ 2))
       else 1 - t ^ 2) := by
  obtain ⟨ha, hb⟩ := block_coefficients a
  calc
    (block a t).det =
      ((eps (3 : Fin 16) (low a) * eps (3 : Fin 16) (partnerIndex a) : ℤ) : ℝ) -
        ((eps (10 : Fin 16) (low a) * eps (10 : Fin 16) (partnerIndex a) : ℤ) : ℝ)
          * t ^ 2 := by
      rw [Matrix.det_fin_two]
      simp [block, blockThree, blockTen]
      ring
    _ = (if a.val < 4 then
           (if a.val = 0 ∨ a.val = 3 then -(1 + t ^ 2) else (1 + t ^ 2))
         else 1 - t ^ 2) := by
      rw [ha, hb]
      fin_cases a <;> norm_num <;> ring

/-- Exact determinant of the actual real 16 by 16 left pencil. -/
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
      simp [Fin.prod_univ_succ]; ring

end LinearInputF16Determinant
