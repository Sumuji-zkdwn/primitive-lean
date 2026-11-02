/-!
# A two-dimensional F16 Fenchel slice and its E-atlas realization

The smooth F16 source singles out the quadratic slice
  V_t(s,v) = (1-t)^2*s^2 + (1+t^2)*v^2/2.
Here it is identified with an exact specialization of the original
polynomial E, and its physical-pairing Fenchel scores are controlled.
The full 16-dimensional Fenchel formula is not asserted by this file.
At t = -1 this particular slice is regular, although the full pencil
is singular. No statement about a generic variable-pair atlas is made.
-/

noncomputable section
open Real Set

namespace LinearInputF16FenchelAtlas

open LinearInputVariablePairs
open LinearInputF16Determinant LinearInputF16CompleteRank

def sectionEnergy (t s v : ℝ) : ℝ :=
  (1 - t) ^ 2 * s ^ 2 + (1 + t ^ 2) * v ^ 2 / 2

def score (t p q s v : ℝ) : ℝ := p * s + q * v - sectionEnergy t s v

/-- The quadratic F16 slice belongs to the existing seven-symbol E family. -/
theorem section_is_original_E (t s v : ℝ) :
    sectionEnergy t s v =
      energy (2 * (1 - t) ^ 2) 0 (1 + t ^ 2) 0 s v 0 := by
  unfold sectionEnergy energy
  ring

/-- The Jacobian of the actual E-gradient, rather than a postulated Hessian. -/
theorem section_hessian_determinant (t s v : ℝ) :
    jacobianPair
      (fun x y => (gradXY (2 * (1 - t) ^ 2) 0 (1 + t ^ 2) 0 0 (x, y)).1)
      (fun x y => (gradXY (2 * (1 - t) ^ 2) 0 (1 + t ^ 2) 0 0 (x, y)).2) s v =
      2 * (1 - t) ^ 2 * (1 + t ^ 2) := by
  rw [gradXY_jacobian]
  ring

theorem section_hessian_zero_iff (t : ℝ) :
    2 * (1 - t) ^ 2 * (1 + t ^ 2) = 0 ↔ t = 1 := by
  have hn : 1 + t ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    have hprod : (1 - t) ^ 2 * (1 + t ^ 2) = 0 := by nlinarith
    have hsq : (1 - t) ^ 2 = 0 := (mul_eq_zero.mp hprod).resolve_right hn
    nlinarith [sq_nonneg (1 - t)]
  · intro ht
    subst t
    norm_num

theorem section_nonnegative (t s v : ℝ) : 0 ≤ sectionEnergy t s v := by
  unfold sectionEnergy
  positivity

theorem section_at_zero (s v : ℝ) :
    sectionEnergy 0 s v = s ^ 2 + v ^ 2 / 2 := by
  norm_num [sectionEnergy]

theorem section_at_one (s v : ℝ) : sectionEnergy 1 s v = v ^ 2 := by
  norm_num [sectionEnergy]

theorem section_at_minus_one (s v : ℝ) :
    sectionEnergy (-1) s v = 4 * s ^ 2 + v ^ 2 := by
  norm_num [sectionEnergy]

/-- At t=0 the physical Fenchel score has a sharp finite upper bound. -/
theorem zero_score_upper (p q s v : ℝ) :
    score 0 p q s v ≤ p ^ 2 / 4 + q ^ 2 / 2 := by
  have hs := sq_nonneg (s - p / 2)
  have hv := sq_nonneg (v - q)
  unfold score sectionEnergy
  nlinarith

theorem zero_score_attained (p q : ℝ) :
    score 0 p q (p / 2) q = p ^ 2 / 4 + q ^ 2 / 2 := by
  unfold score sectionEnergy
  ring

/-- The chosen F16 section has a flat s-direction exactly at t=1. -/
theorem one_score_upper (q s v : ℝ) :
    score 1 0 q s v ≤ q ^ 2 / 4 := by
  have hv := sq_nonneg (v - q / 2)
  unfold score sectionEnergy
  nlinarith

theorem one_score_attained (q : ℝ) :
    score 1 0 q 0 (q / 2) = q ^ 2 / 4 := by
  unfold score sectionEnergy
  ring

/-- Any nonzero s-dual coefficient makes the Fenchel score unbounded above. -/
theorem one_score_unbounded (p q : ℝ) (hp : p ≠ 0) :
    ¬ BddAbove (Set.range (fun z : ℝ × ℝ => score 1 p q z.1 z.2)) := by
  intro hbdd
  obtain ⟨B, hB⟩ := hbdd
  let s : ℝ := (B + 1 - q ^ 2 / 4) / p
  have hv : score 1 p q s (q / 2) = B + 1 := by
    dsimp [score, sectionEnergy, s]
    field_simp [hp]
    ring
  have hu : score 1 p q s (q / 2) ≤ B :=
    hB (score 1 p q s (q / 2)) (Set.mem_range.mpr ⟨(s, q / 2), rfl⟩)
  linarith

/-- Exact finite-value domain of the restricted Fenchel conjugate at t=1. -/
theorem one_score_bdd_iff (p q : ℝ) :
    BddAbove (Set.range (fun z : ℝ × ℝ => score 1 p q z.1 z.2)) ↔ p = 0 := by
  constructor
  · intro hbdd
    by_contra hp
    exact one_score_unbounded p q hp hbdd
  · intro hp
    subst p
    refine ⟨q ^ 2 / 4, ?_⟩
    intro a ha
    obtain ⟨z, rfl⟩ := ha
    exact one_score_upper q z.1 z.2

/-- The opposite t=-1 singularity of the full pencil is not visible
in this selected 2D section. Its Fenchel score stays bounded. -/
theorem minus_one_score_upper (p q s v : ℝ) :
    score (-1) p q s v ≤ p ^ 2 / 16 + q ^ 2 / 4 := by
  have hs := sq_nonneg (s - p / 8)
  have hv := sq_nonneg (v - q / 2)
  unfold score sectionEnergy
  nlinarith

theorem minus_one_score_attained (p q : ℝ) :
    score (-1) p q (p / 8) (q / 2) = p ^ 2 / 16 + q ^ 2 / 4 := by
  unfold score sectionEnergy
  ring

/-- These are the existing *actual* 16x16 matrix ranks, not slice ranks. -/
theorem full_f16_rank_classification (t : ℝ) :
    (realPencilAll t).rank =
      if t = 1 ∨ t = -1 then 12 else 16 :=
  rank_classification t

theorem slice_and_full_rank_at_one :
    (realPencilAll 1).rank = 12 ∧
    (2 * (1 - (1 : ℝ)) ^ 2 * (1 + (1 : ℝ) ^ 2) = 0) ∧
    ¬ BddAbove (Set.range (fun z : ℝ × ℝ => score 1 1 0 z.1 z.2)) := by
  exact ⟨rank_at_plus_one, by norm_num, one_score_unbounded 1 0 (by norm_num)⟩

end LinearInputF16FenchelAtlas
