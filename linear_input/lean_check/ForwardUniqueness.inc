import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
Uniqueness of actual C¹ autonomous ODE solutions on closed forward intervals
and half-lines.  Compact images of supplied finite trajectory segments provide
a common Lipschitz constant, so no confinement hypothesis is needed.
-/

noncomputable section
namespace LinearInputForwardUniqueness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

open Set
open LinearInputTrajectoryExistence LinearInputRegularBand

/-- Two actual solutions of a C¹ vector field with the same initial value
agree on a closed time interval.  Their own compact images supply the common
Lipschitz set; neither an energy band nor a global Lipschitz bound is assumed. -/
theorem solution_unique_on_Icc {F : V → V} {a c : ℝ}
    {z w : ℝ → V} (hF : ContDiff ℝ 1 F)
    (hz : ∀ t ∈ Icc a c, HasDerivAt z (F (z t)) t)
    (hw : ∀ t ∈ Icc a c, HasDerivAt w (F (w t)) t)
    (heq : z a = w a) : EqOn z w (Icc a c) := by
  have hzc : ContinuousOn z (Icc a c) :=
    fun t ht => (hz t ht).continuousAt.continuousWithinAt
  have hwc : ContinuousOn w (Icc a c) :=
    fun t ht => (hw t ht).continuousAt.continuousWithinAt
  let K : Set V := z '' Icc a c ∪ w '' Icc a c
  have hK : IsCompact K :=
    (isCompact_Icc.image_of_continuousOn hzc).union
      (isCompact_Icc.image_of_continuousOn hwc)
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
    hF.locallyLipschitz.locallyLipschitzOn
  apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => K)
    (K := L) (fun _ _ => hL) hzc
    (fun t ht => (hz t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) ?_ hwc
    (fun t ht => (hw t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) ?_ heq
  · intro t ht
    exact Or.inl ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩
  · intro t ht
    exact Or.inr ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩

/-- The finite-interval uniqueness theorem gives uniqueness on a forward
half-line.  No assumptions are made about the negative-time extensions. -/
theorem solution_unique_on_Ici {F : V → V} {a : ℝ}
    {z w : ℝ → V} (hF : ContDiff ℝ 1 F)
    (hz : ∀ t ∈ Ici a, HasDerivAt z (F (z t)) t)
    (hw : ∀ t ∈ Ici a, HasDerivAt w (F (w t)) t)
    (heq : z a = w a) : EqOn z w (Ici a) := by
  intro t ht
  exact solution_unique_on_Icc hF
    (fun s hs => hz s hs.1) (fun s hs => hw s hs.1) heq ⟨ht, le_refl t⟩

/-- The feedback vector solutions are unique on every finite forward interval,
for every real parameter choice and every C¹ autonomous tangential coefficient. -/
theorem feedback_solution_unique_on_Icc {b : ℝ × ℝ → ℝ}
    (hb : ContDiff ℝ 1 b) {lam r u gamma target a c : ℝ} {z w : ℝ → ℝ × ℝ}
    (hz : ∀ t ∈ Icc a c,
      HasDerivAt z (vectorField lam r u gamma target b (z t)) t)
    (hw : ∀ t ∈ Icc a c,
      HasDerivAt w (vectorField lam r u gamma target b (w t)) t)
    (heq : z a = w a) : EqOn z w (Icc a c) :=
  solution_unique_on_Icc (contDiff_vectorField hb lam r u gamma target) hz hw heq

/-- Supplied feedback vector solutions with the same initial state agree for
all nonnegative times.  Existence remains a separate assertion. -/
theorem feedback_solution_unique_on_Ici {b : ℝ × ℝ → ℝ}
    (hb : ContDiff ℝ 1 b) {lam r u gamma target : ℝ} {z w : ℝ → ℝ × ℝ}
    (hz : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt z (vectorField lam r u gamma target b (z t)) t)
    (hw : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt w (vectorField lam r u gamma target b (w t)) t)
    (heq : z 0 = w 0) : EqOn z w (Ici (0 : ℝ)) :=
  solution_unique_on_Ici (contDiff_vectorField hb lam r u gamma target) hz hw heq

/-- The same uniqueness statement in the original coordinate trajectory
predicate.  Both curves use the same state-dependent coefficient b. -/
theorem coordinate_solution_unique_on_Ici {b : ℝ × ℝ → ℝ}
    (hb : ContDiff ℝ 1 b) {lam r u gamma target : ℝ}
    {x₁ y₁ x₂ y₂ : ℝ → ℝ}
    (h₁ : IsTrajectory lam r u gamma target x₁ y₁ (fun t => b (x₁ t, y₁ t)))
    (h₂ : IsTrajectory lam r u gamma target x₂ y₂ (fun t => b (x₂ t, y₂ t)))
    (hx : x₁ 0 = x₂ 0) (hy : y₁ 0 = y₂ 0) :
    EqOn x₁ x₂ (Ici (0 : ℝ)) ∧ EqOn y₁ y₂ (Ici (0 : ℝ)) := by
  have heq : EqOn (fun t => (x₁ t, y₁ t)) (fun t => (x₂ t, y₂ t)) (Ici (0 : ℝ)) :=
    feedback_solution_unique_on_Ici hb
      (fun t ht => hasDerivAt_vectorField_iff.mpr (h₁ t ht))
      (fun t ht => hasDerivAt_vectorField_iff.mpr (h₂ t ht)) (Prod.ext hx hy)
  exact ⟨fun _ ht => congrArg Prod.fst (heq ht),
    fun _ ht => congrArg Prod.snd (heq ht)⟩

end LinearInputForwardUniqueness
