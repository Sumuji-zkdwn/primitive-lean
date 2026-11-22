import RicciFlowBlueprint.LeviCivitaSmoothPort
import Research.SmoothLeviCivitaBianchi

/-!
# Levi-Civita second Bianchi from metric C3 regularity

This module does *not* assume the smoothness of Levi-Civita as an
unproved class instance. It derives C1 and C2 regularity of the
mathlib-constructed connection from a C3 Riemannian metric using the
Apache-2.0-licensed port of RicciFlowBlueprint.LeviCivitaSmooth.

The second Bianchi identity then follows from the already kernel-checked
smooth curvature theorem. All metric/bundle regularity hypotheses remain
explicit. This is Riemannian, not yet Lorentzian and not yet the final
Ricci-flat Yang-Mills tensor contraction.
-/

namespace SmoothMetricBianchi

open Bundle FiberBundle CovariantDerivative VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun (x : M) => TangentSpace I x)]

/-- The Mathlib Levi-Civita connection is C² if the tangent
    Riemannian metric is C³ and the manifold is C-infinity. -/
theorem levi_civita_C2 :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) 2 := by
  letI : IsContMDiffRiemannianBundle I 1 E
      (fun (x : M) => TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  letI : IsContMDiffRiemannianBundle I (((2 : ℕ∞) : ℕ∞ω) + 1) E
      (fun (x : M) => TangentSpace I x) := by
    simpa using
      (inferInstance : IsContMDiffRiemannianBundle I 3 E
        (fun (x : M) => TangentSpace I x))
  exact RicciFlowBlueprint.contMDiffCovariantDerivative_leviCivitaConnection
    (I := I) (M := M) (k := 2)

/-- Also C¹ (either by the upstream instance or the general smoothness
    theorem, with its lower metric regularity obtained from C³). -/
theorem levi_civita_C1 :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) 1 := by
  letI : IsContMDiffRiemannianBundle I 1 E
      (fun (x : M) => TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  letI : IsContMDiffRiemannianBundle I (((1 : ℕ∞) : ℕ∞ω) + 1) E
      (fun (x : M) => TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  exact RicciFlowBlueprint.contMDiffCovariantDerivative_leviCivitaConnection
    (I := I) (M := M) (k := 1)

/-- **No additional connection smoothness premise**: if the metric
    is C³, genuine Levi-Civita curvature obeys second Bianchi.

    Vector fields X/Y/Z are C² and W is C³. -/
theorem levi_civita_second_bianchi_of_C3_metric
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 3 (T% W)) :
    (leviCivitaConnection I M).covCurvature X Y Z W x +
    (leviCivitaConnection I M).covCurvature Y Z X W x +
    (leviCivitaConnection I M).covCurvature Z X Y W x = 0 := by
  letI : IsContMDiffRiemannianBundle I 1 E
      (fun (x : M) => TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  letI : ContMDiffCovariantDerivative (leviCivitaConnection I M) 1 :=
    levi_civita_C1 I M
  letI : ContMDiffCovariantDerivative (leviCivitaConnection I M) 2 :=
    levi_civita_C2 I M
  exact SmoothLeviCivitaBianchi.levi_civita_second_bianchi
    I M hX hY hZ hW

end SmoothMetricBianchi
