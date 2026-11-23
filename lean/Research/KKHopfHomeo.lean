import Mathlib.Tactic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Lemmas
import Research.KKHopfQuotient

/-!
# Topological Hopf quotient: S³/U(1) is homeomorphic to S²

The equivalence of underlying sets is proved in KKHopfQuotient, with the
actual circle orbit relation identified by KKHopfOrbit. Here the quotient
is given Mathlib's natural coinduced topology. We show S³ is compact, the
Hopf map is continuous, and use compact-to-Hausdorff continuity to upgrade
the algebraic equivalence to a homeomorphism. This is still *not* a smooth
principal-bundle trivialization or a Mathlib diffeomorphism.
-/
namespace KKHopfHomeo
open KKHopfGlobalAlgebra KKHopfQuotient

private theorem continuous_radiusSq : Continuous (fun X : X4 => radiusSq X) := by
  unfold radiusSq
  fun_prop

private theorem sphere3_closed : IsClosed {X : X4 | radiusSq X = 1} := by
  exact isClosed_eq continuous_radiusSq continuous_const

private theorem sphere3_compact : IsCompact {X : X4 | radiusSq X = 1} := by
  have hcube : IsCompact {X : X4 | ∀ i : Fin 4, X i ∈ Set.Icc (-1 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hsub : {X : X4 | radiusSq X = 1} ⊆
      {X : X4 | ∀ i : Fin 4, X i ∈ Set.Icc (-1 : ℝ) 1} := by
    intro X hX i
    have hsq : (X i)^2 ≤ 1 := by
      fin_cases i <;> dsimp [radiusSq] at hX ⊢ <;>
        nlinarith [sq_nonneg (X 0), sq_nonneg (X 1),
          sq_nonneg (X 2), sq_nonneg (X 3)]
    exact ⟨by nlinarith, by nlinarith⟩
  exact hcube.of_isClosed_subset sphere3_closed hsub

private theorem sphere3_compactSpace : CompactSpace Sphere3 :=
  (isCompact_iff_compactSpace).mp sphere3_compact

/-- Every coordinate polynomial of the Hopf map is continuous. -/
theorem proj_continuous : Continuous proj := by
  have hc (i : Fin 4) : Continuous (fun X : Sphere3 => X.1 i) :=
    (continuous_apply i).comp continuous_subtype_val
  have h : Continuous (fun X : Sphere3 => (proj X).1) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun X : Sphere3 =>
        2 * (X.1 0 * X.1 2 + X.1 1 * X.1 3))
      exact continuous_const.mul (((hc 0).mul (hc 2)).add ((hc 1).mul (hc 3)))
    · change Continuous (fun X : Sphere3 =>
        2 * (X.1 0 * X.1 3 - X.1 1 * X.1 2))
      exact continuous_const.mul (((hc 0).mul (hc 3)).sub ((hc 1).mul (hc 2)))
    · change Continuous (fun X : Sphere3 =>
        X.1 0 ^ 2 + X.1 1 ^ 2 - X.1 2 ^ 2 - X.1 3 ^ 2)
      exact ((((hc 0).pow 2).add ((hc 1).pow 2)).sub ((hc 2).pow 2)).sub ((hc 3).pow 2)
  simpa using h.subtype_mk (fun X => (proj X).2)

/-- Descent from the quotient is continuous by the quotient topology. -/
theorem descent_continuous : Continuous descent := by
  unfold descent
  exact proj_continuous.quotient_lift (by intro X Y h; exact h)

/-- First homeomorphism result: the natural topological orbit quotient
of S³ by the diagonal U(1) action is homeomorphic to the unit S². -/
noncomputable def quotientHomeomorph : OrbitSpace ≃ₜ Sphere2 := by
  letI : CompactSpace Sphere3 := sphere3_compactSpace
  have h : Continuous (orbitEquivS2 : OrbitSpace → Sphere2) := by
    change Continuous descent
    exact descent_continuous
  exact h.homeoOfEquivCompactToT2

end KKHopfHomeo
