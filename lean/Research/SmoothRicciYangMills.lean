import Research.RicciTraceCovariance
import RicciFlowBlueprint.Divergence
import Research.SmoothMetricBianchi

/-!
# Actual smooth Levi-Civita Ricci-flat curvature is Yang--Mills

The divergence of Riemann curvature is a trace of the actual covariant
derivative on the tangent space, with frame independence proved in
RicciFlowBlueprint.Divergence (Apache-2.0 upstream, c8017e2c2689).

For C3 Riemannian metrics, the connection C1/C2 smoothness is derived in
the parent PR #189. A genuine *local smooth orthonormal frame*
is made explicit as a hypothesis for now. This theorem does not assume
Bianchi, Riemann pair symmetry, Ricci trace compatibility, or YM itself:
those come from imported smooth geometry proofs.

The available formalism is Riemannian. This is not yet a Lorentzian
Standard Model Yang--Mills field with independent dynamical bosons.
-/

namespace SmoothRicciYangMills

open Bundle FiberBundle CovariantDerivative VectorField
open scoped Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E
    (fun (x : M) => TangentSpace I x)]

/-- With C3 metric regularity, the actual Levi-Civita connection
is C1. This is an explicitly proved local typeclass witness. -/
instance instC1LeviCivitaFromC3 :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) 1 :=
  SmoothMetricBianchi.levi_civita_C1 I M

/-- With C3 metric regularity, the actual Levi-Civita connection
is C2, so true covariant Riemann divergence is a well-typed term. -/
instance instC2LeviCivitaFromC3 :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) 2 :=
  SmoothMetricBianchi.levi_civita_C2 I M

/-- Vanishing of global geometric Ricci implies vanishing of its
genuine covariant derivative (not a finite FrameJet imitation). -/
theorem cov_ricci_zero
    (cov : CovariantDerivative I E
      (fun (x : M) => TangentSpace I x))
    [ContMDiffCovariantDerivative cov 1]
    [ContMDiffCovariantDerivative cov 2]
    (hRic : ∀ (Y Z : Π x : M, TangentSpace I x) (p : M),
      cov.ricci Y Z p = 0)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    cov.covRicci X Y Z x = 0 := by
  have hzero : (fun p : M => cov.ricci Y Z p) =
      (fun _ => (0 : ℝ)) := by
    funext p
    exact hRic Y Z p
  unfold CovariantDerivative.covRicci
  rw [hzero, mvfderiv_const]
  simp [hRic]

/-- The frame-independent Yang--Mills divergence is zero for the
actual Mathlib Levi-Civita connection of a Ricci-flat C3 metric,
given a smooth orthonormal frame on a neighbourhood of x.

The local frame availability is explicit. The curvature Bianchi,
trace compatibility and all other identities are proved in the
imported geometric formalization, not independently assumed here. -/
theorem levi_civita_ricci_flat_yang_mills_of_frame
    (hRic : ∀ (Y Z : Π x : M, TangentSpace I x) (p : M),
      (leviCivitaConnection I M).ricci Y Z p = 0)
    {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W))
    {ι : Type*} [Fintype ι]
    {fr : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hs : IsOrthonormalFrameOn I E 1 fr u)
    (hu : IsOpen u) (hx : x ∈ u)
    (hfr : ∀ i, CMDiff 2 (T% (fr i))) :
    (leviCivitaConnection I M).divCurvature Y Z W x = 0 := by
  letI : IsContMDiffRiemannianBundle I 1 E
      (fun y : M => TangentSpace I y) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  letI : IsContMDiffRiemannianBundle I 2 E
      (fun y : M => TangentSpace I y) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  letI : ContMDiffCovariantDerivative (leviCivitaConnection I M) 1 :=
    SmoothMetricBianchi.levi_civita_C1 I M
  letI : ContMDiffCovariantDerivative (leviCivitaConnection I M) 2 :=
    SmoothMetricBianchi.levi_civita_C2 I M
  have htor : (leviCivitaConnection I M).torsion = 0 :=
    CovariantDerivative.torsion_leviCivitaConnection_eq_zero I
  have hmet : (leviCivitaConnection I M).IsMetricCompatible
      (M := M) (V := TangentSpace I) :=
    CovariantDerivative.isMetricCompatible_leviCivitaConnection I
  have hcontr :=
    (leviCivitaConnection I M).divCurvature_eq_covRicci_sub
      htor hmet hY hZ hW hs hu hx hfr
  rw [hcontr,
    cov_ricci_zero I M (leviCivitaConnection I M) hRic Y Z W x,
    cov_ricci_zero I M (leviCivitaConnection I M) hRic Z Y W x]
  ring

end SmoothRicciYangMills
