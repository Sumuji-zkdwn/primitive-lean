import RicciFlowBlueprint.Bianchi
import Research.BianchiOperatorBridge
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# Smooth Levi-Civita second Bianchi using a proved CovariantDerivative theorem

The upstream formalization in RicciFlowBlueprint.Bianchi has a full
manifold-level second Bianchi proof for torsion-free C^2 covariant
derivatives. This wrapper instantiates it with Mathlib's ACTUAL
Levi-Civita connection (not a free record named "Levi-Civita").

Pinned mathlib constructs a Levi-Civita connection and proves
torsion-free and metric-compatible, but its C^2 smoothness is not
yet proved by that constructor. The two ContMDiffCovariantDerivative
typeclass assumptions are therefore EXPLICIT additional hypotheses.
This is a conditional smooth manifold result, not a direct proof
that the mathlib-constructed Levi-Civita is C^2 in all instances.

The contraction to Yang-Mills in Research.RicciFlatBianchiYangMills
is separately kernel-proved in finite frame components. A tensorial
frame/curvature identification, smooth Riemann pair symmetries,
and an actual global Ricci section still need bridging.
-/

namespace SmoothLeviCivitaBianchi

open Bundle FiberBundle VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) => TangentSpace I x)]

/-- Actual pinned Mathlib Levi-Civita connection is torsion-free. -/
theorem actual_torsion_zero :
    (CovariantDerivative.leviCivitaConnection I M).torsion = 0 :=
  CovariantDerivative.torsion_leviCivitaConnection_eq_zero I

/-- Actual pinned Mathlib Levi-Civita connection is metric-compatible. -/
theorem actual_metric_compatible :
    (CovariantDerivative.leviCivitaConnection I M).IsMetricCompatible
      (M := M) (V := TangentSpace I) :=
  CovariantDerivative.isMetricCompatible_leviCivitaConnection I

variable [ContMDiffCovariantDerivative
    (CovariantDerivative.leviCivitaConnection I M) 1]
  [ContMDiffCovariantDerivative
    (CovariantDerivative.leviCivitaConnection I M) 2]

/-- The **manifold-level differential second Bianchi identity** for
    the actual Mathlib-constructed smooth Levi-Civita connection.

    Connection C^2 regularity is explicitly assumed here, as it is
    not established for this constructor in the pinned mathlib.
    Vector fields X,Y,Z are C^2 and W is C^3.
    This statement concerns the genuine covariant curvature derivative,
    not constant connection matrices. -/
theorem levi_civita_second_bianchi
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W)) :
    (CovariantDerivative.leviCivitaConnection I M).covCurvature X Y Z W x +
    (CovariantDerivative.leviCivitaConnection I M).covCurvature Y Z X W x +
    (CovariantDerivative.leviCivitaConnection I M).covCurvature Z X Y W x =
      0 := by
  exact (CovariantDerivative.leviCivitaConnection I M).bianchi_second
    (actual_torsion_zero I M) hX hY hZ hW

end SmoothLeviCivitaBianchi
