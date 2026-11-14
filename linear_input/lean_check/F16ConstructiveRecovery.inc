/-!
# Constructive recovery for the actual 16-dimensional F16 left pencil

The matrix family is the original `realPencilAll`, including its signed
Cayley-Dickson coefficient table.  The general complementary-pencil theorem
is applied after an entrywise identification of that matrix family.

Re-observation is asserted for pairs arising from one state.  An arbitrary
pair of 16-vectors need not be in this 16-dimensional observation image.
-/

noncomputable section

namespace LinearInputF16ConstructiveRecovery

open LinearInputF16Determinant
open LinearInputF16CompleteRank
open LinearInputF16UnexpectedBridges

/-- The original constant left action, not a replacement normal form. -/
def baseMatrix : Matrix (Fin 16) (Fin 16) ℝ := realPencilAll 0

/-- The original coefficient of the real pencil parameter. -/
def slopeMatrix : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j => (entryTen i j : ℝ)

/-- Entrywise identification with the general linear matrix pencil. -/
theorem pencil_identification (t : ℝ) :
    realPencilAll t =
      LinearInputComplementaryPencilRecovery.pencil baseMatrix slopeMatrix t := by
  ext i j
  simp [realPencilAll, LinearInputComplementaryPencilRecovery.pencil,
    baseMatrix, slopeMatrix]

/-- The two original 16-dimensional observations, at t=1 and t=-1. -/
def observations (v : Fin 16 → ℝ) : (Fin 16 → ℝ) × (Fin 16 → ℝ) :=
  ((realPencilAll 1).mulVec v, (realPencilAll (-1)).mulVec v)

/-- The same observation map as the general theorem, with no dimension reduction. -/
theorem observations_identification (v : Fin 16 → ℝ) :
    observations v =
      LinearInputComplementaryPencilRecovery.observe baseMatrix slopeMatrix v := by
  unfold observations LinearInputComplementaryPencilRecovery.observe
  rw [← pencil_identification 1, ← pencil_identification (-1)]

/-- The concrete decoder: invert the original t=0 matrix on the averaged data. -/
def reconstruct (y : (Fin 16 → ℝ) × (Fin 16 → ℝ)) : Fin 16 → ℝ :=
  LinearInputComplementaryPencilRecovery.inverseDecode baseMatrix y

/-- The decoder is precisely the requested explicit matrix formula. -/
theorem reconstruct_formula (y : (Fin 16 → ℝ) × (Fin 16 → ℝ)) :
    reconstruct y =
      ((realPencilAll 0)⁻¹).mulVec ((1 / 2 : ℝ) • (y.1 + y.2)) := by
  rfl

/-- The previously certified invertibility supplies the general theorem's hypothesis. -/
theorem baseMatrix_isUnit : IsUnit baseMatrix := zero_probe_isUnit

/-- The constant matrix has the previously certified determinant one. -/
theorem baseMatrix_det : baseMatrix.det = 1 := by
  unfold baseMatrix
  rw [realPencilAll_det]
  norm_num

/-- Constructive recovery for every real 16-vector, via the general theorem. -/
theorem reconstruct_observations (v : Fin 16 → ℝ) :
    reconstruct (observations v) = v := by
  rw [observations_identification]
  exact LinearInputComplementaryPencilRecovery.inverseDecode_observe
    baseMatrix slopeMatrix (by norm_num) baseMatrix_isUnit v

/-- The explicit decoder is a left inverse of the original paired observation. -/
theorem reconstruct_leftInverse : Function.LeftInverse reconstruct observations :=
  reconstruct_observations

/-- The new constructive proof also recovers the previously established injectivity. -/
theorem observations_injective : Function.Injective observations := by
  intro v w h
  have hr := congrArg reconstruct h
  simpa only [reconstruct_observations] using hr

/-- A pair of observations is compatible exactly when one state realizes it. -/
def Compatible (y : (Fin 16 → ℝ) × (Fin 16 → ℝ)) : Prop :=
  ∃ v : Fin 16 → ℝ, observations v = y

/-- Identification of the concrete and general compatibility predicates. -/
theorem compatible_identification (y : (Fin 16 → ℝ) × (Fin 16 → ℝ)) :
    Compatible y ↔
      LinearInputComplementaryPencilRecovery.Compatible baseMatrix slopeMatrix y := by
  unfold Compatible LinearInputComplementaryPencilRecovery.Compatible
  simp only [observations_identification]

/-- On compatible data, decoding and then observing returns the entire input pair. -/
theorem observations_reconstruct (y : (Fin 16 → ℝ) × (Fin 16 → ℝ))
    (hy : Compatible y) : observations (reconstruct y) = y := by
  rcases hy with ⟨v, rfl⟩
  rw [reconstruct_observations]

/-- The positive singular observation is reconstructed exactly. -/
theorem plus_observation_reconstruct (y : (Fin 16 → ℝ) × (Fin 16 → ℝ))
    (hy : Compatible y) : (realPencilAll 1).mulVec (reconstruct y) = y.1 := by
  have h := congrArg (fun z : (Fin 16 → ℝ) × (Fin 16 → ℝ) => z.fst)
    (observations_reconstruct y hy)
  change (realPencilAll 1).mulVec (reconstruct y) = y.1 at h
  exact h

/-- The negative singular observation is reconstructed exactly. -/
theorem minus_observation_reconstruct (y : (Fin 16 → ℝ) × (Fin 16 → ℝ))
    (hy : Compatible y) : (realPencilAll (-1)).mulVec (reconstruct y) = y.2 := by
  have h := congrArg (fun z : (Fin 16 → ℝ) × (Fin 16 → ℝ) => z.snd)
    (observations_reconstruct y hy)
  change (realPencilAll (-1)).mulVec (reconstruct y) = y.2 at h
  exact h

/-- Compatible data determine a unique real 16-dimensional state. -/
theorem unique_reconstruction (y : (Fin 16 → ℝ) × (Fin 16 → ℝ))
    (hy : Compatible y) : ∃! v : Fin 16 → ℝ, observations v = y := by
  refine ⟨reconstruct y, observations_reconstruct y hy, ?_⟩
  intro v hv
  have h := congrArg reconstruct hv
  simpa only [reconstruct_observations] using h

/-- The two individually nontrivial observation kernels have trivial intersection. -/
theorem joint_kernel_zero (v : Fin 16 → ℝ) :
    ((realPencilAll 1).mulVec v = 0 ∧
      (realPencilAll (-1)).mulVec v = 0) ↔ v = 0 := by
  constructor
  · rintro ⟨hp, hm⟩
    apply observations_injective
    simp [observations, hp, hm]
  · rintro rfl
    simp

/-- Rank loss in both probes and constructive exact recovery hold simultaneously. -/
theorem singular_probes_exact_recovery :
    (realPencilAll 1).rank = 12 ∧
    (realPencilAll (-1)).rank = 12 ∧
    ∀ v : Fin 16 → ℝ, reconstruct (observations v) = v := by
  exact ⟨rank_at_plus_one, rank_at_minus_one, reconstruct_observations⟩

end LinearInputF16ConstructiveRecovery
