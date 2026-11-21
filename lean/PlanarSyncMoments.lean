import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SimpRw

/-!
# Exact discrepancy moments of two observed planar meshes

The mesh points have specified correspondences and a shared coordinate system.
The chosen update first mixes corresponding points, then applies a common
linear map and adds the same point-specific displacement to both images.

The main results derive three closed moment updates from the actual finite
point sums.  The moment recurrence is not an assumed substitute for the mesh
dynamics.  A singular linear map is permitted; no inverse is used.  The inputs
must be known, and the three moments predict discrepancy, not complete images.

These are algebraic results for a selected model.  They assert neither a law
of tidal/quantum dynamics nor a continuous-time convergence theorem.  A vanishing
observed discrepancy does not identify unobserved states or point labels.
-/

noncomputable section

namespace PlanarSyncMoments

open scoped BigOperators

abbrev Point := ℝ × ℝ

structure Map2 where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

structure Moment where
  xx : ℝ
  xy : ℝ
  yy : ℝ

theorem moment_ext {S T : Moment}
    (hxx : S.xx = T.xx) (hxy : S.xy = T.xy) (hyy : S.yy = T.yy) : S = T := by
  cases S with
  | mk sx sr sy =>
    cases T with
    | mk tx tr ty =>
      dsimp at hxx hxy hyy
      subst tx
      subst tr
      subst ty
      rfl

def applyMap (A : Map2) (p : Point) : Point :=
  (A.a * p.1 + A.b * p.2, A.c * p.1 + A.d * p.2)

def pointScale (β : ℝ) (p : Point) : Point := (β * p.1, β * p.2)

def pointAdd (p q : Point) : Point := (p.1 + q.1, p.2 + q.2)

def pointSub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)

def mix (α : ℝ) (x y : Point) : Point :=
  ((1 - α) * x.1 + α * y.1, (1 - α) * x.2 + α * y.2)

def stepLeft (α : ℝ) (A : Map2) (x y u : Point) : Point :=
  pointAdd (applyMap A (mix α x y)) u

def stepRight (α : ℝ) (A : Map2) (x y u : Point) : Point :=
  pointAdd (applyMap A (mix α y x)) u

def transform (β : ℝ) (A : Map2) (p : Point) : Point :=
  pointScale β (applyMap A p)

/-- The identical point-specific displacement cancels from the actual update. -/
theorem common_drive_difference (α : ℝ) (A : Map2) (x y u : Point) :
    pointSub (stepLeft α A x y u) (stepRight α A x y u) =
      transform (1 - 2 * α) A (pointSub x y) := by
  apply Prod.ext <;>
    dsimp [pointSub, stepLeft, stepRight, pointAdd, mix, transform, pointScale, applyMap] <;>
    ring

def pointMoment (p : Point) : Moment := ⟨p.1 ^ 2, p.1 * p.2, p.2 ^ 2⟩

def momentScale (w : ℝ) (S : Moment) : Moment := ⟨w * S.xx, w * S.xy, w * S.yy⟩

def energy (S : Moment) : ℝ := S.xx + S.yy

/-- The polynomial form of `β² A S Aᵀ`, using its three independent entries. -/
def updateMoment (β : ℝ) (A : Map2) (S : Moment) : Moment :=
  ⟨β ^ 2 * (A.a ^ 2 * S.xx + 2 * A.a * A.b * S.xy + A.b ^ 2 * S.yy),
   β ^ 2 * (A.a * A.c * S.xx + (A.a * A.d + A.b * A.c) * S.xy +
     A.b * A.d * S.yy),
   β ^ 2 * (A.c ^ 2 * S.xx + 2 * A.c * A.d * S.xy + A.d ^ 2 * S.yy)⟩

theorem pointMoment_transform (β : ℝ) (A : Map2) (p : Point) :
    pointMoment (transform β A p) = updateMoment β A (pointMoment p) := by
  apply moment_ext <;> dsimp [pointMoment, transform, pointScale, applyMap, updateMoment] <;> ring

theorem updateMoment_scale (β w : ℝ) (A : Map2) (S : Moment) :
    updateMoment β A (momentScale w S) = momentScale w (updateMoment β A S) := by
  apply moment_ext <;> dsimp [updateMoment, momentScale] <;> ring

section FiniteMeshes

variable {ι : Type*} [Fintype ι]

/-- Uncentered second moments of a finite discrepancy field. -/
def sumMoments (D : ι → Point) : Moment :=
  ⟨∑ i, (D i).1 ^ 2, ∑ i, (D i).1 * (D i).2, ∑ i, (D i).2 ^ 2⟩

/-- Mean moments; the empty mesh uses the usual Lean convention `0⁻¹ = 0`. -/
def meanMoments (D : ι → Point) : Moment :=
  momentScale (Fintype.card ι : ℝ)⁻¹ (sumMoments D)

theorem sum_three (a b c : ℝ) (f g h : ι → ℝ) :
    (∑ i, (a * f i + b * g i + c * h i)) =
      a * (∑ i, f i) + b * (∑ i, g i) + c * (∑ i, h i) := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- Closure is derived from the point sums, not postulated for a new state. -/
theorem sumMoments_transform (β : ℝ) (A : Map2) (D : ι → Point) :
    sumMoments (fun i => transform β A (D i)) = updateMoment β A (sumMoments D) := by
  apply moment_ext
  · change (∑ i, (β * (A.a * (D i).1 + A.b * (D i).2)) ^ 2) =
      β ^ 2 * (A.a ^ 2 * (∑ i, (D i).1 ^ 2) +
        2 * A.a * A.b * (∑ i, (D i).1 * (D i).2) +
        A.b ^ 2 * (∑ i, (D i).2 ^ 2))
    calc
      _ = ∑ i, ((β ^ 2 * A.a ^ 2) * (D i).1 ^ 2 +
          (β ^ 2 * (2 * A.a * A.b)) * ((D i).1 * (D i).2) +
          (β ^ 2 * A.b ^ 2) * (D i).2 ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [sum_three]; ring
  · change (∑ i, (β * (A.a * (D i).1 + A.b * (D i).2)) *
        (β * (A.c * (D i).1 + A.d * (D i).2))) =
      β ^ 2 * (A.a * A.c * (∑ i, (D i).1 ^ 2) +
        (A.a * A.d + A.b * A.c) * (∑ i, (D i).1 * (D i).2) +
        A.b * A.d * (∑ i, (D i).2 ^ 2))
    calc
      _ = ∑ i, ((β ^ 2 * (A.a * A.c)) * (D i).1 ^ 2 +
          (β ^ 2 * (A.a * A.d + A.b * A.c)) * ((D i).1 * (D i).2) +
          (β ^ 2 * (A.b * A.d)) * (D i).2 ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [sum_three]; ring
  · change (∑ i, (β * (A.c * (D i).1 + A.d * (D i).2)) ^ 2) =
      β ^ 2 * (A.c ^ 2 * (∑ i, (D i).1 ^ 2) +
        2 * A.c * A.d * (∑ i, (D i).1 * (D i).2) +
        A.d ^ 2 * (∑ i, (D i).2 ^ 2))
    calc
      _ = ∑ i, ((β ^ 2 * A.c ^ 2) * (D i).1 ^ 2 +
          (β ^ 2 * (2 * A.c * A.d)) * ((D i).1 * (D i).2) +
          (β ^ 2 * A.d ^ 2) * (D i).2 ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [sum_three]; ring

theorem meanMoments_transform (β : ℝ) (A : Map2) (D : ι → Point) :
    meanMoments (fun i => transform β A (D i)) = updateMoment β A (meanMoments D) := by
  unfold meanMoments
  rw [sumMoments_transform, updateMoment_scale]

/-- The three mean moments of the actually updated pair obey the closed rule. -/
theorem meanMoments_pair_step (α : ℝ) (A : Map2) (X Y U : ι → Point) :
    meanMoments (fun i =>
      pointSub (stepLeft α A (X i) (Y i) (U i))
        (stepRight α A (X i) (Y i) (U i))) =
      updateMoment (1 - 2 * α) A (meanMoments (fun i => pointSub (X i) (Y i))) := by
  simp_rw [common_drive_difference]
  exact meanMoments_transform (1 - 2 * α) A (fun i => pointSub (X i) (Y i))

theorem common_drive_moments_independent (α : ℝ) (A : Map2) (X Y U V : ι → Point) :
    meanMoments (fun i =>
      pointSub (stepLeft α A (X i) (Y i) (U i))
        (stepRight α A (X i) (Y i) (U i))) =
    meanMoments (fun i =>
      pointSub (stepLeft α A (X i) (Y i) (V i))
        (stepRight α A (X i) (Y i) (V i))) := by
  rw [meanMoments_pair_step, meanMoments_pair_step]

theorem mean_energy_eq_average_squared_distance (D : ι → Point) :
    energy (meanMoments D) =
      (Fintype.card ι : ℝ)⁻¹ * (∑ i, ((D i).1 ^ 2 + (D i).2 ^ 2)) := by
  simp only [energy, meanMoments, momentScale, sumMoments, Finset.sum_add_distrib]
  ring

end FiniteMeshes

theorem energy_update (β : ℝ) (A : Map2) (S : Moment) :
    energy (updateMoment β A S) =
      β ^ 2 * ((A.a ^ 2 + A.c ^ 2) * S.xx +
        2 * (A.a * A.b + A.c * A.d) * S.xy + (A.b ^ 2 + A.d ^ 2) * S.yy) := by
  dsimp [energy, updateMoment]
  ring

theorem energy_update_factor (β : ℝ) (A : Map2) (S : Moment) :
    energy (updateMoment β A S) = β ^ 2 * energy (updateMoment 1 A S) := by
  dsimp [energy, updateMoment]
  ring

/-- The coordinate form of `Aᵀ A = λ I`. -/
def Isotropic (A : Map2) (scale : ℝ) : Prop :=
  A.a ^ 2 + A.c ^ 2 = scale ∧ A.b ^ 2 + A.d ^ 2 = scale ∧ A.a * A.b + A.c * A.d = 0

theorem energy_update_isotropic (β scale : ℝ) (A : Map2) (S : Moment)
    (h : Isotropic A scale) :
    energy (updateMoment β A S) = β ^ 2 * scale * energy S := by
  rcases h with ⟨hx, hy, hxy⟩
  rw [energy_update, hx, hy, hxy]
  dsimp [energy]
  ring

/-- Direction-independent scaling of every point norm characterizes isotropy. -/
theorem point_energy_scaling_iff_isotropic (A : Map2) (scale : ℝ) :
    (∀ p : Point, energy (updateMoment 1 A (pointMoment p)) = scale * energy (pointMoment p)) ↔
      Isotropic A scale := by
  constructor
  · intro h
    have hx := h (1, 0)
    have hy := h (0, 1)
    have hxy := h (1, 1)
    simp only [energy, updateMoment, pointMoment] at hx hy hxy
    norm_num at hx hy hxy
    refine ⟨hx, hy, ?_⟩
    nlinarith
  · intro h p
    simpa using energy_update_isotropic 1 scale A (pointMoment p) h

def identityMap : Map2 := ⟨1, 0, 0, 1⟩

theorem identity_energy_update (β : ℝ) (S : Moment) :
    energy (updateMoment β identityMap S) = β ^ 2 * energy S := by
  dsimp [energy, updateMoment, identityMap]
  ring

theorem quarter_coupling_energy (S : Moment) :
    energy (updateMoment (1 - 2 * (1 / 4 : ℝ)) identityMap S) = (1 / 4) * energy S := by
  rw [identity_energy_update]
  norm_num

def probeX : Map2 := ⟨1, 0, 0, 0⟩
def probeY : Map2 := ⟨0, 1, 0, 0⟩
def probeSum : Map2 := ⟨1, 1, 0, 0⟩

theorem read_probeX (S : Moment) : energy (updateMoment 1 probeX S) = S.xx := by
  dsimp [energy, updateMoment, probeX]
  ring

theorem read_probeY (S : Moment) : energy (updateMoment 1 probeY S) = S.yy := by
  dsimp [energy, updateMoment, probeY]
  ring

theorem read_probeSum (S : Moment) :
    energy (updateMoment 1 probeSum S) = S.xx + 2 * S.xy + S.yy := by
  dsimp [energy, updateMoment, probeSum]
  ring

/-- These three permitted one-step measurements recover all moment entries. -/
theorem three_probes_separate (S T : Moment)
    (hx : energy (updateMoment 1 probeX S) = energy (updateMoment 1 probeX T))
    (hy : energy (updateMoment 1 probeY S) = energy (updateMoment 1 probeY T))
    (hs : energy (updateMoment 1 probeSum S) = energy (updateMoment 1 probeSum T)) : S = T := by
  rw [read_probeX, read_probeX] at hx
  rw [read_probeY, read_probeY] at hy
  rw [read_probeSum, read_probeSum] at hs
  apply moment_ext
  · exact hx
  · linarith
  · exact hy

/-- Equality of every future one-step linear readout is exactly moment equality. -/
theorem all_linear_readouts_eq_iff (S T : Moment) :
    (∀ A : Map2, energy (updateMoment 1 A S) = energy (updateMoment 1 A T)) ↔ S = T := by
  constructor
  · intro h
    exact three_probes_separate S T (h probeX) (h probeY) (h probeSum)
  · rintro rfl
    intro A
    rfl

/-- The same separation holds with any fixed nonzero coupling multiplier. -/
theorem all_scaled_linear_readouts_eq_iff (β : ℝ) (hβ : β ≠ 0) (S T : Moment) :
    (∀ A : Map2, energy (updateMoment β A S) = energy (updateMoment β A T)) ↔ S = T := by
  constructor
  · intro h
    apply (all_linear_readouts_eq_iff S T).mp
    intro A
    have he := h A
    rw [energy_update_factor β A S, energy_update_factor β A T] at he
    exact mul_left_cancel₀ (pow_ne_zero 2 hβ) he
  · rintro rfl
    intro A
    rfl

def runMoments : List (ℝ × Map2) → Moment → Moment
  | [], S => S
  | (β, A) :: ops, S => runMoments ops (updateMoment β A S)

theorem equal_moments_all_operation_lists (S T : Moment) (h : S = T)
    (ops : List (ℝ × Map2)) : energy (runMoments ops S) = energy (runMoments ops T) := by
  rw [h]

def anisotropicMap : Map2 := ⟨2, 0, 0, 1 / 2⟩
def shearMap : Map2 := ⟨1, 1, 0, 1⟩

/-- Same squared distance, but two different futures under anisotropic stretch. -/
theorem scalar_energy_counterexample :
    energy (pointMoment (1, 0)) = energy (pointMoment (0, 1)) ∧
    energy (updateMoment (1 / 2) anisotropicMap (pointMoment (1, 0))) = 1 ∧
    energy (updateMoment (1 / 2) anisotropicMap (pointMoment (0, 1))) = 1 / 16 := by
  norm_num [energy, pointMoment, updateMoment, anisotropicMap]

/-- The diagonal moments alone discard a distinction exposed by shear. -/
theorem cross_moment_counterexample :
    (pointMoment (1, 1)).xx = (pointMoment (1, -1)).xx ∧
    (pointMoment (1, 1)).yy = (pointMoment (1, -1)).yy ∧
    energy (updateMoment (1 / 2) shearMap (pointMoment (1, 1))) = 5 / 4 ∧
    energy (updateMoment (1 / 2) shearMap (pointMoment (1, -1))) = 1 / 4 := by
  norm_num [pointMoment, energy, updateMoment, shearMap]

/-- Every difference is sent to a line by this singular common map. -/
theorem projection_has_zero_vertical_component (β : ℝ) (p : Point) :
    (transform β probeX p).2 = 0 := by
  simp [transform, pointScale, applyMap, probeX]

/-- A discrepancy constrained to a line can still be nonzero. -/
theorem line_collapse_not_synchronization :
    (updateMoment (1 / 2) probeX (pointMoment (1, 1))).yy = 0 ∧
    energy (updateMoment (1 / 2) probeX (pointMoment (1, 1))) = 1 / 4 ∧
    0 < energy (updateMoment (1 / 2) probeX (pointMoment (1, 1))) := by
  norm_num [pointMoment, energy, updateMoment, probeX]

#print axioms PlanarSyncMoments.meanMoments_pair_step
#print axioms PlanarSyncMoments.point_energy_scaling_iff_isotropic
#print axioms PlanarSyncMoments.all_linear_readouts_eq_iff

end PlanarSyncMoments
