import Research.SmoothRicciYangMills
import RicciFlowBlueprint.OrthonormalFrame
import RicciFlowBlueprint.GlobalExtension

/-!
# From a smooth metric to local C2 orthonormal frames, then YM

A smooth metric yields an orthonormal local frame near any point:
take the frame from a local trivialization, apply pointwise
Gram-Schmidt, then use globally C2 bump-function extensions of
each local frame section. Shrink to a common open neighbourhood
where all extended sections agree with the original local frame.

The upstream proofs of Gram-Schmidt regularity and global section
extensions are pre-existing Apache-2.0 mathematical formalizations
(ported from korbonits/ricci-flow-blueprint, pinned SHA c8017e2c2689).
This file supplies the actual finite-index assembly and applies the
genuine Ricci-flat Levi-Civita -> curvature YM theorem of the parent
module, removing the final 'local frame' premise.

This is Riemannian smooth manifold geometry, not Lorentzian physics
and not an independently propagating Yang-Mills boson field.
-/

namespace SmoothRicciFrameExistence

open Bundle FiberBundle Filter Manifold VectorField
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ω M]
  [RiemannianBundle (fun y : M => TangentSpace I y)]
  [IsContMDiffRiemannianBundle I 3 E
    (fun y : M => TangentSpace I y)]

/-- Any point of a C3 Riemannian manifold admits a local
orthonormal frame that consists of globally C2 vector fields,
after shrinking its open domain. This is the missing regularity
and frame-existence hypothesis of the imported contracted Bianchi
theorem, discharged from the actual metric. -/
theorem exists_global_C2_orthonormal_frame (x : M) :
    ∃ (fr : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
      (u : Set M),
      IsOpen u ∧ x ∈ u ∧
      IsOrthonormalFrameOn I E 1 fr u ∧
      (∀ i, CMDiff 2 (T% (fr i))) := by
  classical
  letI : IsContMDiffRiemannianBundle I 1 E
      (fun y : M => TangentSpace I y) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  letI : IsContMDiffRiemannianBundle I 2 E
      (fun y : M => TangentSpace I y) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  let e := trivializationAt E (TangentSpace I (M := M)) x
  let b := Module.finBasis ℝ E
  let s : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    b.orthonormalFrame e
  have hx : x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hlocal : IsOrthonormalFrameOn I E 2 s e.baseSet := by
    exact b.orthonormalFrame_isOrthonormalFrameOn e
  have hsection (i : Fin (Module.finrank ℝ E)) :
      CMDiff[e.baseSet] 2 (T% (s i)) := by
    exact b.contMDiffOn_orthonormalFrame_baseSet e i
  have hext (i : Fin (Module.finrank ℝ E)) :
      ∃ fr : Π y : M, TangentSpace I y,
        CMDiff 2 (T% fr) ∧ fr =ᶠ[𝓝 x] s i := by
    exact RicciFlowBlueprint.exists_contMDiff_eventuallyEq
      (I := I) (n := 2) (e.open_baseSet.mem_nhds hx) (hsection i)
  choose fr hfr heq using hext
  have hnear : ∀ᶠ y in 𝓝 x,
      ∀ i : Fin (Module.finrank ℝ E), fr i y = s i y := by
    exact Filter.eventually_all.mpr heq
  have hcommon :
      e.baseSet ∩ {y : M | ∀ i, fr i y = s i y} ∈ 𝓝 x :=
    Filter.inter_mem (e.open_baseSet.mem_nhds hx) hnear
  obtain ⟨u, hu_sub, hu_open, hx_u⟩ :=
    mem_nhds_iff.mp hcommon
  have hbase (y : M) (hy : y ∈ u) : y ∈ e.baseSet :=
    (hu_sub hy).1
  have hfr_eq (i : Fin (Module.finrank ℝ E))
      (y : M) (hy : y ∈ u) : fr i y = s i y :=
    (hu_sub hy).2 i
  have hls : IsLocalFrameOn I E 1 s u where
    linearIndependent := by
      intro y hy
      exact hlocal.linearIndependent (hbase y hy)
    generating := by
      intro y hy
      exact hlocal.generating (hbase y hy)
    contMDiffOn i := by
      exact ((hsection i).mono (fun y hy => hbase y hy)).of_le (by norm_num)
  have hlf : IsLocalFrameOn I E 1 fr u :=
    hls.congr (fun i y hy => (hfr_eq i y hy).symm)
  have hor : IsOrthonormalFrameOn I E 1 fr u where
    toIsLocalFrameOn := hlf
    orthonormal := by
      intro y hy
      have eq_frame :
          (fun i => fr i y) = (fun i => s i y) := by
        funext i
        exact hfr_eq i y hy
      rw [eq_frame]
      exact hlocal.orthonormal (hbase y hy)
  exact ⟨fr, u, hu_open, hx_u, hor, hfr⟩

/-- The final Riemannian theorem: every globally Ricci-flat C3
Riemannian metric has Levi-Civita curvature with zero actual
source-free Yang-Mills divergence at every point.

It includes no ad hoc Bianchi, pair exchange, trace, parallel Ricci,
or orthonormal-frame hypotheses. All smooth geometric constraints
are discharged by upstream proof modules plus the theorem above. -/
theorem levi_civita_ricci_flat_yang_mills
    (hRic : ∀ (Y Z : Π y : M, TangentSpace I y) (p : M),
      (CovariantDerivative.leviCivitaConnection I M).ricci Y Z p = 0)
    {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    (CovariantDerivative.leviCivitaConnection I M).divCurvature Y Z W x = 0 := by
  obtain ⟨fr, u, hu, hx, hs, hfr⟩ :=
    exists_global_C2_orthonormal_frame I M x
  exact SmoothRicciYangMills.levi_civita_ricci_flat_yang_mills_of_frame
    I M hRic hY hZ hW hs hu hx hfr

end SmoothRicciFrameExistence
