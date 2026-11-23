import Mathlib.Tactic
import Mathlib.Topology.Constructions.SumProd
import Research.KKHopfNorthHomeo

/-!
# South Hopf local homeomorphism from the north chart by pair symmetry.

The coordinate swap (z1,z2) ↦ (z2,z1) induces
(u,v,w) ↦ (u,-v,-w) on the Hopf base, interchanges the two
hemispherical chart domains, and commutes with the diagonal circle action.

This yields a genuine Homeomorph E_S ≃ₜ B_S × U(1).
This is topological, not yet a smooth principal-bundle atlas.
-/

namespace KKHopfSouthHomeo
open KKHopfGlobalAlgebra KKHopfQuotient KKHopfNorthTriv

def swapPairs (X : X4) : X4 := fun i =>
  if i = 0 then X 2 else if i = 1 then X 3
  else if i = 2 then X 0 else X 1

theorem swapPairs_twice (X : X4) : swapPairs (swapPairs X) = X := by
  funext i
  fin_cases i <;> simp [swapPairs]

theorem swapPairs_radius (X : X4) :
    radiusSq (swapPairs X) = radiusSq X := by
  simp [radiusSq, swapPairs]
  ring

theorem swapPairs_hopfX (X : X4) :
    hopfX (swapPairs X) = hopfX X := by
  simp [hopfX, swapPairs]
  ring

theorem swapPairs_hopfY (X : X4) :
    hopfY (swapPairs X) = -hopfY X := by
  simp [hopfY, swapPairs]
  ring

theorem swapPairs_hopfZ (X : X4) :
    hopfZ (swapPairs X) = -hopfZ X := by
  simp [hopfZ, swapPairs]
  ring

def swapSphere (x : Sphere3) : Sphere3 :=
  ⟨swapPairs x.1, by rw [swapPairs_radius, x.2]⟩

theorem swapSphere_twice (x : Sphere3) : swapSphere (swapSphere x) = x := by
  apply Subtype.ext
  exact swapPairs_twice x.1

def baseFlip (b : Sphere2) : Sphere2 :=
  ⟨fun i => if i = 0 then b.1 0 else if i = 1 then -b.1 1 else -b.1 2, by
    change (b.1 0)^2 + (-b.1 1)^2 + (-b.1 2)^2 = 1
    nlinarith [b.2]⟩

theorem baseFlip_twice (b : Sphere2) : baseFlip (baseFlip b) = b := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [baseFlip]

theorem proj_swapSphere (x : Sphere3) :
    proj (swapSphere x) = baseFlip (proj x) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · change hopfX (swapPairs x.1) = hopfX x.1
    exact swapPairs_hopfX x.1
  · change hopfY (swapPairs x.1) = -hopfY x.1
    exact swapPairs_hopfY x.1
  · change hopfZ (swapPairs x.1) = -hopfZ x.1
    exact swapPairs_hopfZ x.1

private theorem swapPairs_continuous : Continuous swapPairs := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun X : X4 => X 2)
    exact continuous_apply 2
  · change Continuous (fun X : X4 => X 3)
    exact continuous_apply 3
  · change Continuous (fun X : X4 => X 0)
    exact continuous_apply 0
  · change Continuous (fun X : X4 => X 1)
    exact continuous_apply 1

private theorem swapSphere_continuous : Continuous swapSphere := by
  have h : Continuous (fun x : Sphere3 => swapPairs x.1) :=
    swapPairs_continuous.comp continuous_subtype_val
  exact h.subtype_mk (fun x => (swapSphere x).2)

private theorem baseFlip_continuous : Continuous baseFlip := by
  have hc (i : Fin 3) : Continuous (fun b : Sphere2 => b.1 i) :=
    (continuous_apply i).comp continuous_subtype_val
  have hv : Continuous (fun b : Sphere2 => (baseFlip b).1) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun b : Sphere2 => b.1 0)
      exact hc 0
    · change Continuous (fun b : Sphere2 => -b.1 1)
      exact (hc 1).neg
    · change Continuous (fun b : Sphere2 => -b.1 2)
      exact (hc 2).neg
  exact hv.subtype_mk (fun b => (baseFlip b).2)

abbrev SouthBase := {b : Sphere2 // 0 < 1 - b.1 2}
abbrev SouthTotal := {x : Sphere3 // 0 < 1 - (proj x).1 2}

def southBaseToNorth (b : SouthBase) : NorthBase :=
  ⟨baseFlip b.1, by
    change 0 < 1 + (baseFlip b.1).1 2
    simpa [baseFlip, sub_eq_add_neg] using b.2⟩

def northBaseToSouth (b : NorthBase) : SouthBase :=
  ⟨baseFlip b.1, by
    change 0 < 1 - (baseFlip b.1).1 2
    simpa [baseFlip, sub_eq_add_neg] using b.2⟩

def southTotalToNorth (x : SouthTotal) : NorthTotal :=
  ⟨swapSphere x.1, by
    change 0 < 1 + (proj (swapSphere x.1)).1 2
    rw [proj_swapSphere]
    simpa [baseFlip, sub_eq_add_neg] using x.2⟩

def northTotalToSouth (x : NorthTotal) : SouthTotal :=
  ⟨swapSphere x.1, by
    change 0 < 1 - (proj (swapSphere x.1)).1 2
    rw [proj_swapSphere]
    simpa [baseFlip, sub_eq_add_neg] using x.2⟩

noncomputable def baseSouthToNorthHomeo : SouthBase ≃ₜ NorthBase where
  toEquiv := {
    toFun := southBaseToNorth
    invFun := northBaseToSouth
    left_inv := by
      intro b
      apply Subtype.ext
      exact baseFlip_twice b.1
    right_inv := by
      intro b
      apply Subtype.ext
      exact baseFlip_twice b.1 }
  continuous_toFun := by
    have h : Continuous (fun b : SouthBase => baseFlip b.1) :=
      baseFlip_continuous.comp continuous_subtype_val
    exact h.subtype_mk (fun b => (southBaseToNorth b).2)
  continuous_invFun := by
    have h : Continuous (fun b : NorthBase => baseFlip b.1) :=
      baseFlip_continuous.comp continuous_subtype_val
    exact h.subtype_mk (fun b => (northBaseToSouth b).2)

noncomputable def totalSouthToNorthHomeo : SouthTotal ≃ₜ NorthTotal where
  toEquiv := {
    toFun := southTotalToNorth
    invFun := northTotalToSouth
    left_inv := by
      intro x
      apply Subtype.ext
      exact swapSphere_twice x.1
    right_inv := by
      intro x
      apply Subtype.ext
      exact swapSphere_twice x.1 }
  continuous_toFun := by
    have h : Continuous (fun x : SouthTotal => swapSphere x.1) :=
      swapSphere_continuous.comp continuous_subtype_val
    exact h.subtype_mk (fun x => (southTotalToNorth x).2)
  continuous_invFun := by
    have h : Continuous (fun x : NorthTotal => swapSphere x.1) :=
      swapSphere_continuous.comp continuous_subtype_val
    exact h.subtype_mk (fun x => (northTotalToSouth x).2)

/-- True topological southern Hopf fibre chart by transporting the
    existing north chart along the complex coordinate pair swap. -/
noncomputable def southHomeomorph : SouthTotal ≃ₜ SouthBase × UnitPhase :=
  (totalSouthToNorthHomeo.trans KKHopfNorthHomeo.northHomeomorph).trans
    (baseSouthToNorthHomeo.symm.prodCongr (Homeomorph.refl UnitPhase))

end KKHopfSouthHomeo
