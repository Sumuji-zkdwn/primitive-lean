/-!
# Constructive recovery from complementary matrix-pencil observations

The state is a finite vector over a field in which 2 is nonzero.  A supplied
left inverse D of B reconstructs the state from the average of the two
observations of B+tC at t=1 and t=-1.  Re-observation is an inverse on
compatible data, not on every element of the product observation space.

The inverse-matrix wrapper uses mathlib's actual nonsingular inverse B^-1.
No dynamics, probability model, or physical identification is assumed.
-/

noncomputable section

namespace LinearInputComplementaryPencilRecovery

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [Field K]

/-- The affine linear matrix pencil, with no nonsingularity assumption on
the individual parameter values. -/
def pencil (B C : Matrix n n K) (t : K) : Matrix n n K :=
  B + t • C

/-- The ordered observations at the opposite parameters +1 and -1. -/
def observe (B C : Matrix n n K) (v : n → K) : (n → K) × (n → K) :=
  ((pencil B C 1).mulVec v, (pencil B C (-1)).mulVec v)

/-- A concrete decoder parameterized by a supplied inverse matrix. -/
def decode (D : Matrix n n K) (y : (n → K) × (n → K)) : n → K :=
  D.mulVec ((1 / 2 : K) • (y.1 + y.2))

/-- A pair is compatible precisely when one state produces both entries. -/
def Compatible (B C : Matrix n n K) (y : (n → K) × (n → K)) : Prop :=
  ∃ v : n → K, observe B C v = y

/-- The decoder with the actual matrix inverse of the constant coefficient. -/
def inverseDecode (B : Matrix n n K) (y : (n → K) × (n → K)) : n → K :=
  decode B⁻¹ y

omit [Fintype n] [DecidableEq n] in
theorem pencil_pos (B C : Matrix n n K) : pencil B C 1 = B + C := by
  simp [pencil]

omit [Fintype n] [DecidableEq n] in
theorem pencil_neg (B C : Matrix n n K) : pencil B C (-1) = B - C := by
  simp [pencil, sub_eq_add_neg]

omit [DecidableEq n] in
theorem positive_probe (B C : Matrix n n K) (v : n → K) :
    (pencil B C 1).mulVec v = B.mulVec v + C.mulVec v := by
  rw [pencil_pos, Matrix.add_mulVec]

omit [DecidableEq n] in
theorem negative_probe (B C : Matrix n n K) (v : n → K) :
    (pencil B C (-1)).mulVec v = B.mulVec v - C.mulVec v := by
  rw [pencil_neg, Matrix.sub_mulVec]

omit [DecidableEq n] in
/-- The average isolates the constant coefficient B. -/
theorem probe_average (B C : Matrix n n K) (h2 : (2 : K) ≠ 0) (v : n → K) :
    (1 / 2 : K) •
        ((pencil B C 1).mulVec v + (pencil B C (-1)).mulVec v) =
      B.mulVec v := by
  rw [positive_probe, negative_probe]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [h2]; ring

omit [DecidableEq n] in
/-- The half difference isolates the parameter coefficient C. -/
theorem probe_difference (B C : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (v : n → K) :
    (1 / 2 : K) •
        ((pencil B C 1).mulVec v - (pencil B C (-1)).mulVec v) =
      C.mulVec v := by
  rw [positive_probe, negative_probe]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [h2]; ring

/-- Constructive recovery: only the explicitly supplied left inverse is used. -/
theorem decode_observe (B C D : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (hDB : D * B = 1) (v : n → K) :
    decode D (observe B C v) = v := by
  change D.mulVec ((1 / 2 : K) •
    ((pencil B C 1).mulVec v + (pencil B C (-1)).mulVec v)) = v
  rw [probe_average B C h2 v, Matrix.mulVec_mulVec, hDB, Matrix.one_mulVec]

theorem decode_leftInverse (B C D : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (hDB : D * B = 1) :
    Function.LeftInverse (decode D) (observe B C) :=
  decode_observe B C D h2 hDB

/-- No two states can have the same pair of observations. -/
theorem observe_injective (B C D : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (hDB : D * B = 1) : Function.Injective (observe B C) := by
  intro v w h
  calc
    v = decode D (observe B C v) := (decode_observe B C D h2 hDB v).symm
    _ = decode D (observe B C w) := congrArg (decode D) h
    _ = w := decode_observe B C D h2 hDB w

/-- Re-observation reproduces both entries of every compatible data pair. -/
theorem observe_decode_of_compatible (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1)
    (y : (n → K) × (n → K)) (hy : Compatible B C y) :
    observe B C (decode D y) = y := by
  rcases hy with ⟨v, rfl⟩
  rw [decode_observe B C D h2 hDB]

theorem positive_reconstruction (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1)
    (y : (n → K) × (n → K)) (hy : Compatible B C y) :
    (pencil B C 1).mulVec (decode D y) = y.1 :=
  congrArg Prod.fst (observe_decode_of_compatible B C D h2 hDB y hy)

theorem negative_reconstruction (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1)
    (y : (n → K) × (n → K)) (hy : Compatible B C y) :
    (pencil B C (-1)).mulVec (decode D y) = y.2 :=
  congrArg Prod.snd (observe_decode_of_compatible B C D h2 hDB y hy)

/-- Compatibility is exactly the fixed-point condition for decode/re-observe. -/
theorem compatible_iff_reconstruction (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1)
    (y : (n → K) × (n → K)) :
    Compatible B C y ↔ observe B C (decode D y) = y := by
  constructor
  · exact observe_decode_of_compatible B C D h2 hDB y
  · intro h
    exact ⟨decode D y, h⟩

/-- A constructive two-sided equivalence with the space of realizable
observation pairs; its inverse is exactly the explicit decoder. -/
def recoveryEquiv (B C D : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (hDB : D * B = 1) : (n → K) ≃ {y // Compatible B C y} where
  toFun v := ⟨observe B C v, v, rfl⟩
  invFun y := decode D y.1
  left_inv := decode_observe B C D h2 hDB
  right_inv := by
    intro y
    apply Subtype.ext
    exact observe_decode_of_compatible B C D h2 hDB y.1 y.2

/-- Every realizable pair has exactly one preimage, given by decode. -/
theorem unique_state (B C D : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (hDB : D * B = 1) (y : (n → K) × (n → K))
    (hy : Compatible B C y) : ∃! v : n → K, observe B C v = y := by
  refine ⟨decode D y, observe_decode_of_compatible B C D h2 hDB y hy, ?_⟩
  intro v hv
  calc
    v = decode D (observe B C v) := (decode_observe B C D h2 hDB v).symm
    _ = decode D y := congrArg (decode D) hv

omit [DecidableEq n] in
/-- The two observation kernels intersect in precisely the common kernel
of B and C.  This statement does not require B to be invertible. -/
theorem joint_kernel_iff (B C : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (v : n → K) :
    ((pencil B C 1).mulVec v = 0 ∧ (pencil B C (-1)).mulVec v = 0) ↔
      (B.mulVec v = 0 ∧ C.mulVec v = 0) := by
  constructor
  · rintro ⟨hp, hm⟩
    constructor
    · simpa [hp, hm] using (probe_average B C h2 v).symm
    · simpa [hp, hm] using (probe_difference B C h2 v).symm
  · rintro ⟨hB, hC⟩
    constructor
    · simp [positive_probe, hB, hC]
    · simp [negative_probe, hB, hC]

/-- With a left inverse of B, the common observation kernel is trivial. -/
theorem joint_kernel_trivial (B C D : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (hDB : D * B = 1) (v : n → K)
    (hp : (pencil B C 1).mulVec v = 0)
    (hm : (pencil B C (-1)).mulVec v = 0) : v = 0 := by
  have hB : B.mulVec v = 0 := ((joint_kernel_iff B C h2 v).mp ⟨hp, hm⟩).1
  calc
    v = D.mulVec (B.mulVec v) := by
      rw [Matrix.mulVec_mulVec, hDB, Matrix.one_mulVec]
    _ = 0 := by rw [hB, Matrix.mulVec_zero]

/-- IsUnit supplies the concrete nonsingular inverse used by inverseDecode. -/
theorem inverseDecode_observe (B C : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (hB : IsUnit B) (v : n → K) : inverseDecode B (observe B C v) = v := by
  exact decode_observe B C B⁻¹ h2
    (Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)) v

theorem inverseDecode_leftInverse (B C : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (hB : IsUnit B) :
    Function.LeftInverse (inverseDecode B) (observe B C) :=
  inverseDecode_observe B C h2 hB

theorem observe_injective_of_isUnit (B C : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hB : IsUnit B) :
    Function.Injective (observe B C) :=
  observe_injective B C B⁻¹ h2
    (Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB))

theorem observe_inverseDecode_of_compatible (B C : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hB : IsUnit B)
    (y : (n → K) × (n → K)) (hy : Compatible B C y) :
    observe B C (inverseDecode B y) = y :=
  observe_decode_of_compatible B C B⁻¹ h2
    (Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)) y hy

theorem positive_inverse_reconstruction (B C : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hB : IsUnit B)
    (y : (n → K) × (n → K)) (hy : Compatible B C y) :
    (pencil B C 1).mulVec (inverseDecode B y) = y.1 :=
  congrArg Prod.fst (observe_inverseDecode_of_compatible B C h2 hB y hy)

theorem negative_inverse_reconstruction (B C : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hB : IsUnit B)
    (y : (n → K) × (n → K)) (hy : Compatible B C y) :
    (pencil B C (-1)).mulVec (inverseDecode B y) = y.2 :=
  congrArg Prod.snd (observe_inverseDecode_of_compatible B C h2 hB y hy)

/-- Invertibility of B ensures that the decoded state's B-observation is
the average, even for an incompatible input pair. -/
theorem inverseDecode_midpoint (B : Matrix n n K) (hB : IsUnit B)
    (y : (n → K) × (n → K)) :
    B.mulVec (inverseDecode B y) = (1 / 2 : K) • (y.1 + y.2) := by
  change B.mulVec (B⁻¹.mulVec ((1 / 2 : K) • (y.1 + y.2))) = _
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB),
    Matrix.one_mulVec]

/-- A data pair is realizable exactly when its half difference agrees
with the C-observation of the state recovered from its average. -/
theorem compatible_iff_difference (B C : Matrix n n K) (h2 : (2 : K) ≠ 0)
    (hB : IsUnit B) (y : (n → K) × (n → K)) :
    Compatible B C y ↔
      C.mulVec (inverseDecode B y) = (1 / 2 : K) • (y.1 - y.2) := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [inverseDecode_observe B C h2 hB]
    exact (probe_difference B C h2 v).symm
  · intro hC
    refine ⟨inverseDecode B y, ?_⟩
    apply Prod.ext
    · change (pencil B C 1).mulVec (inverseDecode B y) = y.1
      rw [positive_probe, inverseDecode_midpoint B hB y, hC]
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      field_simp [h2]; ring
    · change (pencil B C (-1)).mulVec (inverseDecode B y) = y.2
      rw [negative_probe, inverseDecode_midpoint B hB y, hC]
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      field_simp [h2]; ring

end LinearInputComplementaryPencilRecovery
