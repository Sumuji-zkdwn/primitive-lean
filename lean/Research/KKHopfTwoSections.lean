import Mathlib.Tactic
import Research.KKHopfOrbit
import Research.KKHopfSurjective

/-!
# Explicit north/south Hopf sections on the two sphere charts

The pointwise overlap theorem produces an actual unit-circle transition
phase, using the previously certified algebraic completeness of the fibres.
The sections' smoothness and the quotient manifold atlas are not inferred.
-/
namespace KKHopfTwoSections
open KKHopfGlobalAlgebra

noncomputable def southVec (u v w : ℝ) : X4 :=
  let d := Real.sqrt (2*(1-w))
  fun i => if i=0 then u/d else if i=1 then -v/d
           else if i=2 then (1-w)/d else 0

theorem south_chart (u v w : ℝ)
    (hsphere : u^2+v^2+w^2=1) (hpos : 0 < 1-w) :
    radiusSq (southVec u v w)=1 ∧
    hopfX (southVec u v w)=u ∧
    hopfY (southVec u v w)=v ∧
    hopfZ (southVec u v w)=w := by
  let d : ℝ := Real.sqrt (2*(1-w))
  have harg : 0 ≤ 2*(1-w) := by positivity
  have hdpos : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hd2 : d^2 = 2*(1-w) := Real.sq_sqrt harg
  have hwne : 1-w ≠ 0 := ne_of_gt hpos
  have hsum : u^2+v^2+(1-w)^2=2*(1-w) := by nlinarith [hsphere]
  have hdiff : u^2+v^2-(1-w)^2=2*w*(1-w) := by nlinarith [hsphere]
  refine ⟨?_,?_,?_,?_⟩
  · change (u/d)^2+(-v/d)^2+((1-w)/d)^2+(0:ℝ)^2=1
    calc
      _ = (u^2+v^2+(1-w)^2)/d^2 := by ring
      _ = 1 := by rw [hsum,hd2]; field_simp [hwne]
  · change 2*((u/d)*((1-w)/d)+(-v/d)*(0:ℝ))=u
    calc
      _ = (2*(1-w)*u)/d^2 := by ring
      _ = u := by rw [hd2]; field_simp [hwne]
  · change 2*((u/d)*(0:ℝ)-(-v/d)*((1-w)/d))=v
    calc
      _ = (2*(1-w)*v)/d^2 := by ring
      _ = v := by rw [hd2]; field_simp [hwne]
  · change (u/d)^2+(-v/d)^2-((1-w)/d)^2-(0:ℝ)^2=w
    calc
      _ = (u^2+v^2-(1-w)^2)/d^2 := by ring
      _ = w := by rw [hdiff,hd2]; field_simp [hwne]

/-- The local sections are related by a genuine unit phase on their
common domain. The phase is constructive via the parent orbit theorem. -/
theorem north_south_overlap (u v w : ℝ)
    (hsphere : u^2+v^2+w^2=1)
    (hn : 0 < 1+w) (hs : 0 < 1-w) :
    ∃ C S : ℝ, C^2+S^2=1 ∧
      rotate C S (KKHopfSurjective.northVec u v w) = southVec u v w := by
  obtain ⟨hN,hNx,hNy,hNz⟩ :=
    KKHopfSurjective.north_chart u v w hsphere hn
  obtain ⟨hS,hSx,hSy,hSz⟩ := south_chart u v w hsphere hs
  exact KKHopfOrbit.same_hopf_implies_unit_rotation
    (KKHopfSurjective.northVec u v w) (southVec u v w)
    hN hS (hNx.trans hSx.symm) (hNy.trans hSy.symm) (hNz.trans hSz.symm)

end KKHopfTwoSections
