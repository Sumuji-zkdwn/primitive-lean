/-!
# Full 16 by 16 sedenion pencil: determinant by eight 2 by 2 blocks

All coefficient entries come from the existing, verified F16 epsilon table.
The row and column orderings are explicit finite permutations. They expose
eight independent blocks, so the large determinant is not evaluated by a
factorially large Leibniz sum.

The original operator is left multiplication by e3 + t e10. No assumption
that the sedenion algebra is associative or a field is used.
-/

noncomputable section

namespace LinearInputF16FullMatrix

open LinearInputF16Holonomy LinearInputF16Recovery

/-- Each group of two columns/rows is indexed by a low-three-bit label. -/
abbrev BlockIndex := Fin 2 × Fin 8

/-- Eight explicit XOR-with-nine results; a finite lookup speeds symbolic proofs. -/
def partnerTable (a : Fin 8) : Fin 16 :=
  if a.val = 0 then 9
  else if a.val = 1 then 8
  else if a.val = 2 then 11
  else if a.val = 3 then 10
  else if a.val = 4 then 13
  else if a.val = 5 then 12
  else if a.val = 6 then 15
  else 14

/-- The table agrees with the original XOR-based construction, exactly. -/
theorem partnerIndex_eq_partnerTable (a : Fin 8) :
    partnerIndex a = partnerTable a := by
  fin_cases a <;> decide

/-- Column 0 is e_a, column 1 is e_(a XOR 9). -/
def colOrder (p : BlockIndex) : Fin 16 :=
  if p.1 = 0 then low p.2 else partnerIndex p.2

/-- Output rows for left multiplication by e3 and e10. -/
def rowOrder (p : BlockIndex) : Fin 16 :=
  if p.1 = 0 then rightIndex (3 : Fin 16) (low p.2)
  else rightIndex (10 : Fin 16) (low p.2)

/-- Both orderings enumerate all 16 basis vectors with no repetition. -/
theorem colOrder_bijective : Function.Bijective colOrder := by decide

theorem rowOrder_bijective : Function.Bijective rowOrder := by decide

/-- A computational inverse; no choice-based inverse occurs in the sign test. -/
def colInverse (k : Fin 16) : BlockIndex :=
  if h : k.val < 8 then (0, ⟨k.val, h⟩)
  else (1, ⟨(Nat.xor k.val 9) % 8, Nat.mod_lt _ (by decide)⟩)

/-- Since XOR with 3 is its own inverse, the second order is explicit too. -/
def rowInverse (k : Fin 16) : BlockIndex :=
  colInverse (rightIndex (3 : Fin 16) k)

def colEquiv : BlockIndex ≃ Fin 16 where
  toFun := colOrder
  invFun := colInverse
  left_inv := by decide
  right_inv := by decide

def rowEquiv : BlockIndex ≃ Fin 16 where
  toFun := rowOrder
  invFun := rowInverse
  left_inv := by decide
  right_inv := by decide

/-- XOR with three is the product of eight disjoint swaps. -/
def xorThreeSwaps : Equiv.Perm (Fin 16) :=
  Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 4 7 *
    Equiv.swap 5 6 * Equiv.swap 8 11 * Equiv.swap 9 10 *
      Equiv.swap 12 15 * Equiv.swap 13 14

/-- The relative row/column permutation is exactly XOR with three. -/
theorem relative_permutation_eq_swaps :
    colEquiv.symm.trans rowEquiv = xorThreeSwaps := by
  apply Equiv.ext
  intro k
  fin_cases k <;> decide

/-- The row/column reordering is even, hence leaves the full determinant unchanged. -/
theorem reindex_sign_one :
    Equiv.Perm.sign (colEquiv.symm.trans rowEquiv) = 1 := by
  rw [relative_permutation_eq_swaps]
  simp [xorThreeSwaps, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

/-- Entry of left multiplication by a single signed basis vector. -/
def leftEntry (e row col : Fin 16) : ℤ :=
  if rightIndex e col = row then eps e col else 0

/-- The whole 16x16 left multiplication matrix over the reals. -/
def leftMatrix (t : ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  fun row col =>
    (leftEntry (3 : Fin 16) row col : ℝ) +
      t * (leftEntry (10 : Fin 16) row col : ℝ)

/-- Original left multiplication expressed as a matrix over integers. -/
def leftMatrixInt (t : ℤ) : Matrix (Fin 16) (Fin 16) ℤ :=
  fun row col => leftEntry (3 : Fin 16) row col + t * leftEntry (10 : Fin 16) row col

theorem leftMatrixInt_cast (t : ℤ) (i j : Fin 16) :
    leftMatrix (t : ℝ) i j = ((leftMatrixInt t) i j : ℝ) := by
  simp [leftMatrix, leftMatrixInt, Int.cast_add, Int.cast_mul]

/-- The coefficient at t=0 after both finite orderings are applied. -/
theorem leftEntry_three_reindexed :
    ∀ p q : BlockIndex,
      leftEntry (3 : Fin 16) (rowOrder p) (colOrder q) =
      (if p.2 = q.2 then
        if p.1 = q.1 then eps (3 : Fin 16) (colOrder q) else 0
       else 0) := by decide

/-- The coefficient at t=1 (before the variable t) sits off the local diagonal. -/
theorem leftEntry_ten_reindexed :
    ∀ p q : BlockIndex,
      leftEntry (10 : Fin 16) (rowOrder p) (colOrder q) =
      (if p.2 = q.2 then
        if p.1 ≠ q.1 then eps (10 : Fin 16) (colOrder q) else 0
       else 0) := by decide

/-- The actual two-dimensional block indexed by a low-three-bit value. -/
def localBlock (a : Fin 8) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    (if i = j then (eps (3 : Fin 16) (colOrder (j,a)) : ℝ) else 0) +
      t * (if i ≠ j then (eps (10 : Fin 16) (colOrder (j,a)) : ℝ) else 0)

/-- After independent row and column permutations, the full matrix is exactly
a homogeneous block diagonal of eight 2 by 2 matrices. -/
theorem full_block_decomposition (t : ℝ) :
    (leftMatrix t).submatrix rowOrder colOrder =
      Matrix.blockDiagonal (fun a : Fin 8 => localBlock a t) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have h3 := leftEntry_three_reindexed (i,a) (j,b)
  have h10 := leftEntry_ten_reindexed (i,a) (j,b)
  change
    (leftEntry (3 : Fin 16) (rowOrder (i,a)) (colOrder (j,b)) : ℝ) +
      t * (leftEntry (10 : Fin 16) (rowOrder (i,a)) (colOrder (j,b)) : ℝ) =
        (if a = b then localBlock a t i j else 0)
  rw [h3, h10]
  by_cases hab : a = b
  · subst b
    by_cases hij : i = j
    · simp [localBlock, hij]
    · simp [localBlock, hij]
  · simp [hab]

/-- The real determinant of each local block has one quadratic factor. -/
theorem localBlock_det (a : Fin 8) (t : ℝ) :
    (localBlock a t).det =
      (if a.val < 4 then
        (if a.val = 0 ∨ a.val = 3 then -(1 + t ^ 2) else 1 + t ^ 2)
       else 1 - t ^ 2) := by
  have hformula : (localBlock a t).det =
      (((eps (3 : Fin 16) (low a) *
          eps (3 : Fin 16) (partnerIndex a) : ℤ) : ℝ)) -
      (((eps (10 : Fin 16) (low a) *
          eps (10 : Fin 16) (partnerIndex a) : ℤ) : ℝ)) * t ^ 2 := by
    rw [Matrix.det_fin_two]
    simp [localBlock, colOrder, Int.cast_mul]
    ring
  rw [hformula]
  obtain ⟨h3, h10⟩ := block_coefficients a
  have hp :
      (((eps (3 : Fin 16) (low a) *
        eps (3 : Fin 16) (partnerIndex a) : ℤ) : ℝ)) =
      (if a.val = 0 ∨ a.val = 3 then (-1 : ℝ) else 1) := by
    exact_mod_cast h3
  have hq :
      (((eps (10 : Fin 16) (low a) *
        eps (10 : Fin 16) (partnerIndex a) : ℤ) : ℝ)) =
      (if a.val < 4 then
        (if a.val = 0 ∨ a.val = 3 then (1 : ℝ) else -1)
       else 1) := by
    exact_mod_cast h10
  rw [hp, hq]
  by_cases hlo : a.val < 4
  · by_cases h03 : a.val = 0 ∨ a.val = 3
    · simp only [if_pos hlo, if_pos h03]
      ring
    · simp only [if_pos hlo, if_neg h03]
      ring
  · have h03 : ¬(a.val = 0 ∨ a.val = 3) := by omega
    simp only [if_neg hlo, if_neg h03]
    ring

/-- Four factors of either quadratic, with the two negative factors cancelling. -/
theorem eight_block_product (t : ℝ) :
    (∏ a : Fin 8, (localBlock a t).det) =
      (1 - t ^ 2) ^ 4 * (1 + t ^ 2) ^ 4 := by
  simp_rw [localBlock_det]
  norm_num [Fin.prod_univ_succ]
  ring

/-- Full determinant, not merely a product of individual block determinants. -/
theorem full_determinant (t : ℝ) :
    (leftMatrix t).det =
      (t ^ 2 - 1) ^ 4 * (t ^ 2 + 1) ^ 4 := by
  have hs := Matrix.det_reindex rowEquiv.symm colEquiv.symm (leftMatrix t)
  have he : ((leftMatrix t).submatrix rowOrder colOrder).det = (leftMatrix t).det := by
    simp only [Equiv.symm_symm, reindex_sign_one, Units.val_one,
      Int.cast_one, one_mul, Matrix.reindex_apply] at hs
    change ((leftMatrix t).submatrix rowOrder colOrder).det =
      (leftMatrix t).det at hs
    exact hs
  calc
    (leftMatrix t).det =
        ((leftMatrix t).submatrix rowOrder colOrder).det := he.symm
    _ = (∏ a : Fin 8, (localBlock a t).det) := by
      rw [full_block_decomposition, Matrix.det_blockDiagonal]
    _ = (t ^ 2 - 1) ^ 4 * (t ^ 2 + 1) ^ 4 := by
      rw [eight_block_product]
      ring

/-- In real parameters, the pencil is singular precisely at plus or minus one. -/
theorem full_determinant_zero_iff (t : ℝ) :
    (leftMatrix t).det = 0 ↔ t = 1 ∨ t = -1 := by
  rw [full_determinant]
  constructor
  · intro h
    have hmul : t ^ 2 - 1 = 0 := by
      by_contra hneq
      have hleft : (t ^ 2 - 1) ^ 4 ≠ 0 := pow_ne_zero 4 hneq
      have hright : (t ^ 2 + 1) ^ 4 ≠ 0 := pow_ne_zero 4 (by positivity)
      exact (mul_ne_zero hleft hright) h
    have hh : (t - 1) * (t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hh with h1 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num [full_determinant]

end LinearInputF16FullMatrix
