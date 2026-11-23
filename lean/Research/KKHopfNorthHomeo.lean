import Mathlib.Tactic
import Research.KKHopfNorthTriv

/-!
# Topological (not smooth) local trivialization of the Hopf north patch

The north fibre chart is a homeomorphism over the open base patch.
This is a refinement of KKHopfNorthTriv.northTrivialization.
-/
namespace KKHopfNorthHomeo
open KKHopfGlobalAlgebra KKHopfQuotient KKHopfNorthTriv

private theorem baseVec_cont :
    Continuous (fun b : NorthBase => (b.1.1 : Fin 3 → ℝ)) := by
  exact continuous_subtype_val.comp continuous_subtype_val

private theorem baseCoord_cont (i : Fin 3) :
    Continuous (fun b : NorthBase => b.1.1 i) :=
  (continuous_apply i).comp baseVec_cont

private theorem den_cont :
    Continuous (fun b : NorthBase => Real.sqrt (2*(1+b.1.1 2))) := by
  apply Real.continuous_sqrt.comp
  exact continuous_const.mul (continuous_const.add (baseCoord_cont 2))

private theorem den_ne (b : NorthBase) :
    Real.sqrt (2*(1+b.1.1 2)) ≠ 0 := by
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  exact mul_pos (by norm_num) b.2

private theorem northVec_cont :
    Continuous (fun b : NorthBase => KKHopfSurjective.northVec
      (b.1.1 0) (b.1.1 1) (b.1.1 2)) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun b : NorthBase =>
        (1+b.1.1 2) / Real.sqrt (2*(1+b.1.1 2)))
    exact (continuous_const.add (baseCoord_cont 2)).div den_cont den_ne
  · change Continuous (fun _ : NorthBase => (0:ℝ))
    exact continuous_const
  · change Continuous (fun b : NorthBase =>
        b.1.1 0 / Real.sqrt (2*(1+b.1.1 2)))
    exact (baseCoord_cont 0).div den_cont den_ne
  · change Continuous (fun b : NorthBase =>
        b.1.1 1 / Real.sqrt (2*(1+b.1.1 2)))
    exact (baseCoord_cont 1).div den_cont den_ne

private theorem northSection_cont : Continuous northSection := by
  have h : Continuous (fun b : NorthBase =>
      KKHopfSurjective.northVec (b.1.1 0) (b.1.1 1) (b.1.1 2)) := northVec_cont
  exact h.subtype_mk (by intro b; exact (northSection b).2)

private theorem base_cont : Continuous base := by
  have hp : Continuous (fun X : NorthTotal => proj X.1) :=
    KKHopfHomeo.proj_continuous.comp continuous_subtype_val
  exact hp.subtype_mk (fun X => (base X).2)

private theorem n_cont : Continuous (fun X : NorthTotal =>
    ((northSection (base X)).1 : X4)) :=
  continuous_subtype_val.comp (northSection_cont.comp base_cont)

private theorem x_cont : Continuous (fun X : NorthTotal => (X.1.1 : X4)) :=
  continuous_subtype_val.comp continuous_subtype_val

private theorem ncoord_cont (i : Fin 4) : Continuous
    (fun X : NorthTotal => (northSection (base X)).1 i) :=
  (continuous_apply i).comp n_cont

private theorem xcoord_cont (i : Fin 4) : Continuous
    (fun X : NorthTotal => X.1.1 i) :=
  (continuous_apply i).comp x_cont

private theorem dot_cont : Continuous (fun X : NorthTotal =>
    KKHopfActionFree.dot4 (northSection (base X)).1 X.1.1) := by
  change Continuous (fun X : NorthTotal =>
    (northSection (base X)).1 0 * X.1.1 0 +
    (northSection (base X)).1 1 * X.1.1 1 +
    (northSection (base X)).1 2 * X.1.1 2 +
    (northSection (base X)).1 3 * X.1.1 3)
  exact (((((ncoord_cont 0).mul (xcoord_cont 0)).add
    ((ncoord_cont 1).mul (xcoord_cont 1))).add
    ((ncoord_cont 2).mul (xcoord_cont 2))).add
    ((ncoord_cont 3).mul (xcoord_cont 3)))

private theorem skew_cont : Continuous (fun X : NorthTotal =>
    KKHopfPhaseUnique.skew (northSection (base X)).1 X.1.1) := by
  change Continuous (fun X : NorthTotal =>
    (northSection (base X)).1 0 * X.1.1 1 -
    (northSection (base X)).1 1 * X.1.1 0 +
    (northSection (base X)).1 2 * X.1.1 3 -
    (northSection (base X)).1 3 * X.1.1 2)
  exact ((((ncoord_cont 0).mul (xcoord_cont 1)).sub
    ((ncoord_cont 1).mul (xcoord_cont 0))).add
    ((ncoord_cont 2).mul (xcoord_cont 3))).sub
    ((ncoord_cont 3).mul (xcoord_cont 2))

private theorem phase_cont : Continuous phase := by
  have h : Continuous (fun X : NorthTotal => (phase X).1) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun X : NorthTotal =>
        KKHopfActionFree.dot4 (northSection (base X)).1 X.1.1)
      exact dot_cont
    · change Continuous (fun X : NorthTotal =>
        KKHopfPhaseUnique.skew (northSection (base X)).1 X.1.1)
      exact skew_cont
  exact h.subtype_mk (fun X => (phase X).2)

private theorem decode_cont : Continuous decode :=
  base_cont.prodMk phase_cont

private theorem product_phase_cont (i : Fin 2) : Continuous
    (fun bp : NorthBase × UnitPhase => bp.2.1 i) :=
  (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)

private theorem product_north_cont : Continuous (fun bp : NorthBase × UnitPhase =>
    (northSection bp.1).1) :=
  continuous_subtype_val.comp (northSection_cont.comp continuous_fst)

private theorem product_north_coord_cont (i : Fin 4) : Continuous
    (fun bp : NorthBase × UnitPhase => (northSection bp.1).1 i) :=
  (continuous_apply i).comp product_north_cont

private theorem product_rot_cont : Continuous (fun bp : NorthBase × UnitPhase =>
    rotate (bp.2.1 0) (bp.2.1 1) (northSection bp.1).1) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun bp : NorthBase × UnitPhase =>
      bp.2.1 0*(northSection bp.1).1 0 - bp.2.1 1*(northSection bp.1).1 1)
    exact ((product_phase_cont 0).mul (product_north_coord_cont 0)).sub
      ((product_phase_cont 1).mul (product_north_coord_cont 1))
  · change Continuous (fun bp : NorthBase × UnitPhase =>
      bp.2.1 1*(northSection bp.1).1 0 + bp.2.1 0*(northSection bp.1).1 1)
    exact ((product_phase_cont 1).mul (product_north_coord_cont 0)).add
      ((product_phase_cont 0).mul (product_north_coord_cont 1))
  · change Continuous (fun bp : NorthBase × UnitPhase =>
      bp.2.1 0*(northSection bp.1).1 2 - bp.2.1 1*(northSection bp.1).1 3)
    exact ((product_phase_cont 0).mul (product_north_coord_cont 2)).sub
      ((product_phase_cont 1).mul (product_north_coord_cont 3))
  · change Continuous (fun bp : NorthBase × UnitPhase =>
      bp.2.1 1*(northSection bp.1).1 2 + bp.2.1 0*(northSection bp.1).1 3)
    exact ((product_phase_cont 1).mul (product_north_coord_cont 2)).add
      ((product_phase_cont 0).mul (product_north_coord_cont 3))

private theorem encode_cont : Continuous (fun bp : NorthBase × UnitPhase =>
    encode bp.1 bp.2) := by
  have hr : Continuous (fun bp : NorthBase × UnitPhase =>
      rotatedSection bp.1 bp.2) :=
    product_rot_cont.subtype_mk (fun bp => (rotatedSection bp.1 bp.2).2)
  exact hr.subtype_mk (fun bp => (encode bp.1 bp.2).2)

noncomputable def northHomeomorph : NorthTotal ≃ₜ NorthBase × UnitPhase where
  toEquiv := northTrivialization
  continuous_toFun := decode_cont
  continuous_invFun := encode_cont

end KKHopfNorthHomeo
