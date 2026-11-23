import Mathlib.Tactic
import Mathlib.Topology.Covering.FundamentalGroupCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Research.KKHopfTransitionContinuous
import Research.KKHopfEquator

/-!
# Hopf equator clutching phase and the orientation-reversing winding loop

This file bridges the actual north/south Hopf transition to a standard
angular reversal in the period-one additive circle. It uses Mathlib's
existing theorem windingNumber_zsmulLoop for the genuine fundamental-group
winding number, not a custom integer label.

It does not construct the characteristic first Chern class of a Mathlib
principal U(1)-bundle. The classical equality c1 = degree(clutching map)
requires an additional bundle/cohomology theorem.

Coordinates on the equator are (u,v,w)=(cos θ,sin θ,0).
-/

namespace KKHopfWinding
open KKHopfGlobalAlgebra KKHopfQuotient KKHopfNorthTriv
open KKHopfTransitionContinuous

/-- Embed an equatorial unit phase as a point of the north/south overlap. -/
def equatorBase (p : UnitPhase) : OverlapBase := by
  refine ⟨⟨(fun i : Fin 3 =>
    if i = 0 then p.1 0 else if i = 1 then p.1 1 else 0), ?_⟩, ?_⟩
  · change (p.1 0)^2 + (p.1 1)^2 + (0 : ℝ)^2 = 1
    simpa using p.2
  · change 0 < 1 + (0 : ℝ) ∧ 0 < 1 - (0 : ℝ)
    constructor <;> norm_num

/-- On the real unit circle, complex conjugation reflects the sine sign. -/
def equatorConj (p : UnitPhase) : UnitPhase := by
  refine ⟨(fun i : Fin 2 => if i = 0 then p.1 0 else -(p.1 1)), ?_⟩
  change (p.1 0)^2 + (-(p.1 1))^2 = 1
  nlinarith [p.2]

theorem equatorConj_involutive (p : UnitPhase) :
    equatorConj (equatorConj p) = p := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [equatorConj]

/-- The actual previously verified U(1) transition reduces exactly
to conjugation on every point of the equator, not just a sample angle. -/
theorem transition_on_equator (p : UnitPhase) :
    transition (equatorBase p) = equatorConj p := by
  let u : ℝ := p.1 0
  let v : ℝ := p.1 1
  have hunit : u^2 + v^2 = 1 := p.2
  have hnorm : radiusSq (KKHopfSurjective.northVec u v 0) = 1 :=
    (KKHopfSurjective.north_chart u v 0
      (by simpa using hunit) (by norm_num)).1
  have htrans : rotate ((transition (equatorBase p)).1 0)
      ((transition (equatorBase p)).1 1)
      (KKHopfSurjective.northVec u v 0) =
      KKHopfTwoSections.southVec u v 0 := by
    simpa [equatorBase, u, v] using
      (transition_rotates_sections (equatorBase p))
  have hsame : rotate ((transition (equatorBase p)).1 0)
      ((transition (equatorBase p)).1 1)
      (KKHopfSurjective.northVec u v 0) =
      rotate u (-v) (KKHopfSurjective.northVec u v 0) := by
    calc
      _ = KKHopfTwoSections.southVec u v 0 := htrans
      _ = _ := (KKHopfEquator.equator_transition u v hunit).symm
  have hphase := KKHopfPhaseUnique.phase_unique_on_sphere
    ((transition (equatorBase p)).1 0) ((transition (equatorBase p)).1 1)
    u (-v) (KKHopfSurjective.northVec u v 0) hnorm hsame
  apply Subtype.ext
  funext i
  fin_cases i
  · change ((transition (equatorBase p)).1 0) = u
    exact hphase.1
  · change ((transition (equatorBase p)).1 1) = -v
    exact hphase.2

/-- The trigonometric circle parametrization is genuinely a unit phase. -/
noncomputable def circleParam (θ : ℝ) : UnitPhase := by
  refine ⟨(fun i : Fin 2 =>
    if i = 0 then Real.cos θ else Real.sin θ), ?_⟩
  change (Real.cos θ)^2 + (Real.sin θ)^2 = 1
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The exact Hopf transition reverses the angle θ -> -θ. -/
theorem equator_transition_angle_reverse (θ : ℝ) :
    transition (equatorBase (circleParam θ)) = circleParam (-θ) := by
  rw [transition_on_equator]
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [equatorConj, circleParam, Real.cos_neg, Real.sin_neg]

/-- Real and imaginary coordinates of the existing Mathlib Circle. -/
noncomputable def circlePhase (z : Circle) : UnitPhase := by
  refine ⟨(fun i : Fin 2 =>
    if i = 0 then (z : ℂ).re else (z : ℂ).im), ?_⟩
  change (z : ℂ).re^2 + (z : ℂ).im^2 = 1
  have hz := Circle.normSq_coe z
  rw [Complex.normSq_apply] at hz
  nlinarith [hz]

/-- The Mathlib complex circle exponential agrees with the real
cos/sin parametrization used in the actual equator clutching map. -/
theorem circlePhase_exp (θ : ℝ) :
    circlePhase (Circle.exp θ) = circleParam θ := by
  apply Subtype.ext
  funext i
  fin_cases i
  · change ((Circle.exp θ : Circle) : ℂ).re = Real.cos θ
    simpa only [Circle.coe_exp] using Complex.exp_ofReal_mul_I_re θ
  · change ((Circle.exp θ : Circle) : ℂ).im = Real.sin θ
    simpa only [Circle.coe_exp] using Complex.exp_ofReal_mul_I_im θ

/-- The equatorial transition is the inverse exponential phase
at any real angle: a genuine link to Mathlib's complex circle. -/
theorem transition_as_inverse_exp (θ : ℝ) :
    transition (equatorBase (circlePhase (Circle.exp θ))) =
      circlePhase (Circle.exp (-θ)) := by
  rw [circlePhase_exp]
  rw [equator_transition_angle_reverse]
  exact (circlePhase_exp (-θ)).symm

/-- A standard loop that goes backwards once around AddCircle 1 has
exact fundamental-group winding number -1 (Mathlib, not a fake degree). -/
theorem backward_winding_number :
    AddCircle.windingNumber
      { asHom := Path.Homotopic.Quotient.mk
          (AddCircle.zsmulLoop (1 : ℝ) 0 (-1)) } = (-1 : ℤ) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  simpa using
    (AddCircle.windingNumber_zsmulLoop (p := (1 : ℝ)) (x := (0 : ℝ)) (-1))

/-- The canonical exponential map of the additive circle sends
angle negation to the inverse multiplicative phase. -/
theorem circle_of_additive_neg (x : AddCircle (1 : ℝ)) :
    (-x).toCircle = (x.toCircle)⁻¹ :=
  AddCircle.toCircle_neg x

/-- Connect the *actual Hopf equator transition* to the inverse
circle operation under Mathlib's additive-circle exponential model. -/
theorem transition_of_additive_circle (x : AddCircle (1 : ℝ)) :
    transition (equatorBase (circlePhase x.toCircle)) =
      circlePhase ((-x).toCircle) := by
  rw [transition_on_equator]
  rw [circle_of_additive_neg]
  -- The inverse of a unit complex number is its complex conjugate.
  apply Subtype.ext
  funext i
  fin_cases i
  · change (x.toCircle : ℂ).re = ((x.toCircle⁻¹ : Circle) : ℂ).re
    rw [Circle.coe_inv_eq_conj]
    simp
  · change -((x.toCircle : ℂ).im) = ((x.toCircle⁻¹ : Circle) : ℂ).im
    rw [Circle.coe_inv_eq_conj]
    simp

end KKHopfWinding
