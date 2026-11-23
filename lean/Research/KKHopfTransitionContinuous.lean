import Mathlib.Tactic
import Research.KKHopfTransitionAlgebra
import Research.KKHopfNorthTriv

/-!
# Continuous normalized transition phase of Hopf north/south charts

The real formula from KKHopfTransitionAlgebra defines a continuous
unit-circle valued map on the north/south overlap. No winding/Chern
number is claimed in this module.
-/
namespace KKHopfTransitionContinuous
open KKHopfGlobalAlgebra KKHopfQuotient KKHopfNorthTriv KKHopfTransitionAlgebra

abbrev OverlapBase := {b : Sphere2 // 0 < 1 + b.1 2 ∧ 0 < 1 - b.1 2}

noncomputable def northDen (b : OverlapBase) : ℝ := Real.sqrt (2*(1+b.1.1 2))
noncomputable def southDen (b : OverlapBase) : ℝ := Real.sqrt (2*(1-b.1.1 2))

private theorem baseCoord_cont (i : Fin 3) :
    Continuous (fun b : OverlapBase => b.1.1 i) :=
  (continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)

private theorem northDen_cont : Continuous northDen := by
  apply Real.continuous_sqrt.comp
  exact continuous_const.mul (continuous_const.add (baseCoord_cont 2))

private theorem southDen_cont : Continuous southDen := by
  apply Real.continuous_sqrt.comp
  exact continuous_const.mul (continuous_const.sub (baseCoord_cont 2))

private theorem northDen_ne (b : OverlapBase) : northDen b ≠ 0 := by
  unfold northDen
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  exact mul_pos (by norm_num) b.2.1

private theorem southDen_ne (b : OverlapBase) : southDen b ≠ 0 := by
  unfold southDen
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  exact mul_pos (by norm_num) b.2.2

/-- Exact continuous candidate, defined on all overlap points. -/
noncomputable def transition (b : OverlapBase) : UnitPhase := by
  let dn := northDen b
  let ds := southDen b
  let u := b.1.1 0
  let v := b.1.1 1
  let w := b.1.1 2
  have h := full_overlap_transition u v w b.1.2 b.2.1 b.2.2
  refine ⟨(fun i => if i=0 then transitionC u dn ds else transitionS v dn ds), ?_⟩
  change (transitionC u dn ds)^2+(transitionS v dn ds)^2=1
  exact h.1

/-- The full overlap transition is continuous as an S¹-valued map. -/
theorem transition_continuous : Continuous transition := by
  have hden : Continuous (fun b : OverlapBase => northDen b * southDen b) :=
    northDen_cont.mul southDen_cont
  have hnonzero (b : OverlapBase) : northDen b*southDen b ≠ 0 :=
    mul_ne_zero (northDen_ne b) (southDen_ne b)
  have hC : Continuous (fun b : OverlapBase =>
      transitionC (b.1.1 0) (northDen b) (southDen b)) := by
    unfold transitionC
    exact (continuous_const.mul (baseCoord_cont 0)).div hden hnonzero
  have hS : Continuous (fun b : OverlapBase =>
      transitionS (b.1.1 1) (northDen b) (southDen b)) := by
    unfold transitionS
    exact ((continuous_const.mul (baseCoord_cont 1)).neg).div hden hnonzero
  have hcoord : Continuous (fun b : OverlapBase => (transition b).1) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun b : OverlapBase =>
        transitionC (b.1.1 0) (northDen b) (southDen b))
      exact hC
    · change Continuous (fun b : OverlapBase =>
        transitionS (b.1.1 1) (northDen b) (southDen b))
      exact hS
  exact hcoord.subtype_mk (fun b => (transition b).2)

/-- The continuous overlap phase sends the north local section to
    the south local section for every common base point. -/
theorem transition_rotates_sections (b : OverlapBase) :
    rotate ((transition b).1 0) ((transition b).1 1)
      (KKHopfSurjective.northVec (b.1.1 0) (b.1.1 1) (b.1.1 2)) =
      KKHopfTwoSections.southVec (b.1.1 0) (b.1.1 1) (b.1.1 2) := by
  exact (full_overlap_transition (b.1.1 0) (b.1.1 1) (b.1.1 2)
    b.1.2 b.2.1 b.2.2).2

end KKHopfTransitionContinuous
