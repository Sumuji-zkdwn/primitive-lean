/-!
# An exact F16 / Chebyshev / dihedral / dual-probe bridge

The original signed Cayley-Dickson table and the previously proved full
16x16 real pencil are used without changing their conventions.

This file does NOT identify the sedenion algebra with a field extension or
derive the WFS response law from F16.  The dihedral action below is an
identified two-dimensional *normal-form* action, not a new F16 automorphism.
-/

noncomputable section

namespace LinearInputF16UnexpectedBridges

open LinearInputF16Holonomy
open LinearInputF16Recovery
open LinearInputF16Determinant
open LinearInputF16CompleteRank
open LinearInputVariablePairGalois

/-- Off-diagonal coefficient in the first normalized row. -/
def signedUpper (a : Fin 8) : ℤ :=
  eps (3 : Fin 16) (low a) * eps (10 : Fin 16) (partnerIndex a)

/-- Off-diagonal coefficient in the second normalized row. -/
def signedLower (a : Fin 8) : ℤ :=
  eps (3 : Fin 16) (partnerIndex a) * eps (10 : Fin 16) (low a)

/-- Four rotation-type blocks and four reflection-type blocks, from the
original 256-entry signed table, with no chosen continuous model. -/
theorem signed_product (a : Fin 8) :
    signedUpper a * signedLower a =
      (if a.val < 4 then -1 else 1) := by
  fin_cases a <;> decide

/-- The concrete row-sign gauge (multiplying each row by its constant
diagonal coefficient) applied to a genuine F16 2x2 block. -/
def normalizedBlock (a : Fin 8) (t : ℝ) (i j : Fin 2) : ℝ :=
  (if i = 0 then (eps (3 : Fin 16) (low a) : ℝ)
   else (eps (3 : Fin 16) (partnerIndex a) : ℝ)) * block a t i j

/-- The normalized off-diagonal generator of an actual F16 block. -/
def generatorEntry (a : Fin 8) (i j : Fin 2) : ℝ :=
  if i = 0 then
    if j = 0 then 0 else (signedUpper a : ℝ)
  else
    if j = 0 then (signedLower a : ℝ) else 0

/-- Each original signed F16 block becomes I+tJ_a under a fixed,
t-independent invertible row-sign gauge. -/
theorem normalized_block_formula (a : Fin 8) (t : ℝ) (i j : Fin 2) :
    normalizedBlock a t i j =
      (if i = j then (1 : ℝ) else 0) + t * generatorEntry a i j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [normalizedBlock, generatorEntry, signedUpper, signedLower,
      block, blockThree, blockTen, eps, epsTable, low, partnerIndex] <;>
    ring <;> norm_num [Nat.xor]

/-- The normalized generator acting on an abstract two-dimensional pair. -/
def signedAction (a : Fin 8) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((signedUpper a : ℝ) * z.2, (signedLower a : ℝ) * z.1)

/-- Block 1 supplies a genuine quarter turn. -/
theorem quarter_sample (z : ℝ × ℝ) :
    signedAction (1 : Fin 8) z = (-z.2, z.1) := by
  have hu : signedUpper (1 : Fin 8) = -1 := by decide
  have hl : signedLower (1 : Fin 8) = 1 := by decide
  simp [signedAction, hu, hl]

/-- Block 5 supplies a reflection. -/
theorem reflection_sample (z : ℝ × ℝ) :
    signedAction (5 : Fin 8) z = (z.2, z.1) := by
  have hu : signedUpper (5 : Fin 8) = 1 := by decide
  have hl : signedLower (5 : Fin 8) = 1 := by decide
  simp [signedAction, hu, hl]

/-- The quarter turn has square minus identity. -/
theorem quarter_square (z : ℝ × ℝ) :
    signedAction 1 (signedAction 1 z) = (-z.1, -z.2) := by
  rcases z with ⟨x, y⟩
  simp [quarter_sample]

theorem quarter_four (z : ℝ × ℝ) :
    signedAction 1 (signedAction 1 (signedAction 1 (signedAction 1 z))) = z := by
  rcases z with ⟨x, y⟩
  simp [quarter_sample]

theorem reflection_square (z : ℝ × ℝ) :
    signedAction 5 (signedAction 5 z) = z := by
  rcases z with ⟨x, y⟩
  simp [reflection_sample]

/-- Explicit D4 relation R J R = J^-1 = J^3 after identifying block
coordinate planes; not a claim about F16 algebra automorphisms. -/
theorem reflection_conjugates_quarter (z : ℝ × ℝ) :
    signedAction 5 (signedAction 1 (signedAction 5 z)) =
      signedAction 1 (signedAction 1 (signedAction 1 z)) := by
  rcases z with ⟨x, y⟩
  simp [quarter_sample, reflection_sample]

/-- An invertible linear coordinate choice diagonalizes the reflection.
This is the same reflection normal form used in the projective WFS lift. -/
def diagonalGauge (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 - z.2, z.1 + z.2)

def diagonalReflection (z : ℝ × ℝ) : ℝ × ℝ :=
  (-z.1, z.2)

theorem reflection_gauge (z : ℝ × ℝ) :
    diagonalGauge (signedAction 5 z) = diagonalReflection (diagonalGauge z) := by
  rw [reflection_sample]
  rcases z with ⟨x, y⟩
  simp [diagonalGauge, diagonalReflection] <;> ring

/-- Genuine F16 determinant expressed through the *existing* cubic
discriminant, not an identification of the two dynamical systems. -/
theorem determinant_chebyshev_discriminant (t : ℝ) :
    (realPencilAll t).det =
      ((1 + t ^ 2) * cubicDiscriminant 4 (-3) t / 432) ^ 4 := by
  rw [realPencilAll_det, chebyshev_discriminant]
  ring

theorem singular_iff_chebyshev_critical (t : ℝ) :
    (realPencilAll t).rank = 12 ↔
      cubicDiscriminant 4 (-3) t = 0 := by
  exact (rank_twelve_iff t).trans
    (chebyshev_discriminant_critical_iff t).symm

/-- The quadratic-resolvent discriminant 4(t^2-1) is an exact negative
scalar multiple of the cubic discriminant. -/
theorem resolvent_cubic_discriminants (t : ℝ) :
    4 * (t ^ 2 - 1) = -cubicDiscriminant 4 (-3) t / 108 := by
  rw [chebyshev_discriminant]
  ring

/-- Average of opposite parameter probes recovers the invertible t=0
left action, although the plus-one and minus-one actions are individually rank deficient. -/
theorem opposite_probe_sum :
    realPencilAll 1 + realPencilAll (-1) =
      (2 : ℝ) • realPencilAll 0 := by
  ext i j
  simp [realPencilAll] <;> ring

theorem zero_probe_isUnit : IsUnit (realPencilAll 0) := by
  have hd : (realPencilAll 0).det ≠ 0 := by
    rw [realPencilAll_det]
    norm_num
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)

/-- The pair of individually singular 16x16 probes jointly separates
all real 16-vectors, with no extra data or stochastic assumptions. -/
theorem opposite_probe_joint_injective :
    Function.Injective (fun v : Fin 16 → ℝ =>
      ((realPencilAll 1).mulVec v, (realPencilAll (-1)).mulVec v)) := by
  intro v w h
  have hp : (realPencilAll 1).mulVec v = (realPencilAll 1).mulVec w :=
    congrArg Prod.fst h
  have hm : (realPencilAll (-1)).mulVec v = (realPencilAll (-1)).mulVec w :=
    congrArg Prod.snd h
  have hsum :
      (realPencilAll 1 + realPencilAll (-1)).mulVec v =
        (realPencilAll 1 + realPencilAll (-1)).mulVec w := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec]
    exact congrArg2 (· + ·) hp hm
  have hscaled :
      (2 : ℝ) • (realPencilAll 0).mulVec v =
        (2 : ℝ) • (realPencilAll 0).mulVec w := by
    simpa only [opposite_probe_sum, Matrix.smul_mulVec] using hsum
  have hzero : (realPencilAll 0).mulVec v = (realPencilAll 0).mulVec w := by
    funext i
    have hi := congrFun hscaled i
    change (2 : ℝ) * ((realPencilAll 0).mulVec v i) =
      (2 : ℝ) * ((realPencilAll 0).mulVec w i) at hi
    linarith
  exact Matrix.mulVec_injective_of_isUnit zero_probe_isUnit hzero

end LinearInputF16UnexpectedBridges
