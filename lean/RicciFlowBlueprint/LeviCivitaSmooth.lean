/-! Apache-2.0 compatibility shim for RicciFlowBlueprint.LeviCivitaSmooth,
source upstream c8017e2c26898d11f39cec0dfce89368d5a0506a. The smoothness proof is already imported from
LeviCivitaSmoothPort.lean on the parent branch; only distinct Ricci/sectional
helper definitions are reproduced below to avoid duplicate global names. -/
import RicciFlowBlueprint.LeviCivita
import RicciFlowBlueprint.LeviCivitaSmoothPort

open Bundle CovariantDerivative Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace RicciFlowBlueprint

section RicciOfMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

-- BENCH: ricci-of-metric
/-- **The Ricci curvature of a metric.** For a `C²` Riemannian metric `g`, `Ric(g)` is the Ricci
curvature of its Levi-Civita connection. This is a genuine function of `g` and not junk: the
Levi-Civita connection is `C¹` (`contMDiffCovariantDerivative_leviCivitaConnection`), which is
what `ricci` needs to be the trace of a tensor. -/
noncomputable def ricciOfMetric
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (X Y : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  (leviCivitaConnection I M).ricci X Y x

/-- The sectional curvature of a `C²` metric, via its Levi-Civita connection. -/
noncomputable def sectionalCurvatureOfMetric
    (g : ContMDiffRiemannianMetric I 2 E (fun (x : M) ↦ TangentSpace I x))
    (X Y : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  sectionalCurvature (leviCivitaConnection I M) X Y x

end RicciOfMetric
end RicciFlowBlueprint
