import Mathlib.Tactic
import Research.KKHopfTwoSections
import Research.KKHopfPhaseUnique

/-!
# Equatorial transition of the Hopf north/south sections

On the equator u²+v²=1, w=0, the north and south local sections
are related by the unique circle phase (C,S)=(u,-v). This is the
complex conjugation map on the equatorial unit circle. This file
makes no formal winding-degree / Chern-class claim.
-/
namespace KKHopfEquator
open KKHopfGlobalAlgebra

/-- The actual unit-circle overlap transition on the equator. -/
theorem equator_transition (u v : ℝ) (hunit : u^2+v^2=1) :
    rotate u (-v) (KKHopfSurjective.northVec u v 0) =
      KKHopfTwoSections.southVec u v 0 := by
  have hd : Real.sqrt (2:ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  funext i
  fin_cases i <;>
    norm_num [rotate, KKHopfSurjective.northVec,
      KKHopfTwoSections.southVec] <;>
    field_simp [hd] <;> nlinarith [hunit]

/-- Equatorial transition is uniquely the conjugate phase. -/
theorem equator_transition_unique (u v C S : ℝ)
    (hunit : u^2+v^2=1)
    (heq : rotate C S (KKHopfSurjective.northVec u v 0) =
      KKHopfTwoSections.southVec u v 0) :
    C=u ∧ S=-v := by
  have hSphere : u^2+v^2+(0:ℝ)^2=1 := by nlinarith [hunit]
  have hPositive : 0 < (1+(0:ℝ)) := by norm_num
  have hNorm := (KKHopfSurjective.north_chart u v 0 hSphere hPositive).1
  have hEq : rotate C S (KKHopfSurjective.northVec u v 0) =
      rotate u (-v) (KKHopfSurjective.northVec u v 0) := by
    rw [equator_transition u v hunit]
    exact heq
  exact KKHopfPhaseUnique.phase_unique_on_sphere C S u (-v)
    (KKHopfSurjective.northVec u v 0) hNorm hEq

end KKHopfEquator
