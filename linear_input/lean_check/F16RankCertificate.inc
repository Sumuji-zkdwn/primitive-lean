/-!
# Certified rank of the 16-dimensional Cayley-Dickson left pencil

For t = 1 or t = -1 the signed left action L_(e3) + t L_(e10)
has rank 12 over the reals. The proof uses two exact integer matrix
certificates: a factorization through 12 columns and a 12 by 12
left-unmixing identity. Real rank inequalities are then applied to
these integer identities after the integer-to-real ring homomorphism.

No determinant expansion, numerical floating-point operation, new
axiom, or assumption of associativity of sedenions is used.
-/

noncomputable section

namespace LinearInputF16Rank

open LinearInputF16Holonomy

/-- The literal coefficient matrix of the existing integer leftPencil. -/
def intPencil (t : ℤ) : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.of fun k j =>
    (if rightIndex (3 : Fin 16) j = k then eps (3 : Fin 16) j else 0) +
    t * (if rightIndex (10 : Fin 16) j = k then eps (10 : Fin 16) j else 0)

/-- The same matrix, now acting on real coordinate vectors. -/
def realPencil (t : ℤ) : Matrix (Fin 16) (Fin 16) ℝ :=
  (intPencil t).map (Int.castRingHom ℝ)

/-- Include the twelve selected independent coordinates in Fin 16. -/
def include12 (i : Fin 12) : Fin 16 :=
  ⟨i.val, by have hi := i.isLt; omega⟩

/-- The first twelve actual columns, without row operations. -/
def firstColumns (t : ℤ) : Matrix (Fin 16) (Fin 12) ℤ :=
  Matrix.of fun k j => intPencil t k (include12 j)

/-- Exact integer coefficients expressing every discarded column using
one of the first twelve columns at the two singular parameters. -/
def rightFactor (t : ℤ) : Matrix (Fin 12) (Fin 16) ℤ :=
  Matrix.of fun i j =>
    if j.val < 12 then
      if i.val = j.val then 1 else 0
    else if j.val = 12 then
      if i.val = 5 then t else 0
    else if j.val = 13 then
      if i.val = 4 then -t else 0
    else if j.val = 14 then
      if i.val = 7 then -t else 0
    else
      if i.val = 6 then t else 0

/-- The selected 12-by-12 principal submatrix. -/
def firstBlock (t : ℤ) : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of fun i j => intPencil t (include12 i) (include12 j)

/-- Twice the inverse of the selected block, with integer entries.
The identity is used only at t=1 and t=-1. -/
def leftUnmix (t : ℤ) : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of fun i k =>
    if i.val = 0 then
      if k.val = 3 then 1 else if k.val = 10 then t else 0
    else if i.val = 1 then
      if k.val = 2 then 1 else if k.val = 11 then t else 0
    else if i.val = 2 then
      if k.val = 1 then -1 else if k.val = 8 then t else 0
    else if i.val = 3 then
      if k.val = 0 then -1 else if k.val = 9 then -t else 0
    else if i.val = 4 then
      if k.val = 7 then 2 else 0
    else if i.val = 5 then
      if k.val = 6 then -2 else 0
    else if i.val = 6 then
      if k.val = 5 then 2 else 0
    else if i.val = 7 then
      if k.val = 4 then -2 else 0
    else if i.val = 8 then
      if k.val = 2 then -t else if k.val = 11 then 1 else 0
    else if i.val = 9 then
      if k.val = 3 then t else if k.val = 10 then -1 else 0
    else if i.val = 10 then
      if k.val = 0 then -t else if k.val = 9 then 1 else 0
    else
      if k.val = 1 then -t else if k.val = 8 then -1 else 0

/-- A matrix with twelve nonzero diagonal entries. -/
def twiceIdentity : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.diagonal (fun _ => (2 : ℤ))

/-- All sixteen columns factor through twelve at t = +1. -/
theorem factor_plus :
    intPencil 1 = firstColumns 1 * rightFactor 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The same integer factorization at t = -1. -/
theorem factor_minus :
    intPencil (-1) = firstColumns (-1) * rightFactor (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- A two-sided rank certificate: left-unmixing the selected block
returns twice the identity, at t = +1. -/
theorem unmix_plus :
    leftUnmix 1 * firstBlock 1 = twiceIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The same identity at t = -1. -/
theorem unmix_minus :
    leftUnmix (-1) * firstBlock (-1) = twiceIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem factor_at (t : ℤ) (ht : t = 1 ∨ t = -1) :
    intPencil t = firstColumns t * rightFactor t := by
  rcases ht with rfl | rfl
  · exact factor_plus
  · exact factor_minus

theorem unmix_at (t : ℤ) (ht : t = 1 ∨ t = -1) :
    leftUnmix t * firstBlock t = twiceIdentity := by
  rcases ht with rfl | rfl
  · exact unmix_plus
  · exact unmix_minus

/-- Twelve nonzero rationally-free integer pivots remain nonzero over R. -/
theorem real_twiceIdentity_rank :
    ((twiceIdentity.map (Int.castRingHom ℝ))).rank = 12 := by
  classical
  have h : (twiceIdentity.map (Int.castRingHom ℝ)) =
      Matrix.diagonal (fun _ : Fin 12 => (2 : ℝ)) := by
    ext i j
    simp [twiceIdentity]
  rw [h, Matrix.rank_diagonal]
  simp

/-- Exactly twelve dimensions survive the real left action at both
singular integer parameters. This is the actual Matrix.rank in mathlib. -/
theorem realPencil_rank (t : ℤ) (ht : t = 1 ∨ t = -1) :
    (realPencil t).rank = 12 := by
  classical
  let f : ℤ →+* ℝ := Int.castRingHom ℝ
  have hfactor := congrArg
    (fun M : Matrix (Fin 16) (Fin 16) ℤ => M.map f) (factor_at t ht)
  simp only [Matrix.map_mul] at hfactor
  have hupper : (realPencil t).rank ≤ 12 := by
    change ((intPencil t).map f).rank ≤ 12
    rw [hfactor]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  have hunmix := congrArg
    (fun M : Matrix (Fin 12) (Fin 12) ℤ => M.map f) (unmix_at t ht)
  simp only [Matrix.map_mul] at hunmix
  have hlowerBlock : 12 ≤ ((firstBlock t).map f).rank := by
    calc
      12 = ((twiceIdentity.map f)).rank := by
        simpa [f] using real_twiceIdentity_rank.symm
      _ = (((leftUnmix t).map f) * ((firstBlock t).map f)).rank :=
        congrArg Matrix.rank hunmix.symm
      _ ≤ ((firstBlock t).map f).rank :=
        Matrix.rank_mul_le_right _ _
  have hsub : ((realPencil t).submatrix include12 include12) =
      (firstBlock t).map f := by
    ext i j
    rfl
  have hlower : 12 ≤ (realPencil t).rank := by
    calc
      12 ≤ ((firstBlock t).map f).rank := hlowerBlock
      _ = ((realPencil t).submatrix include12 include12).rank := by rw [hsub]
      _ ≤ (realPencil t).rank := Matrix.rank_submatrix_le _ _ _
  exact le_antisymm hupper hlower

theorem realPencil_plus_rank : (realPencil 1).rank = 12 :=
  realPencil_rank 1 (Or.inl rfl)

theorem realPencil_minus_rank : (realPencil (-1)).rank = 12 :=
  realPencil_rank (-1) (Or.inr rfl)

end LinearInputF16Rank
