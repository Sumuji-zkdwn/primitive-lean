/-! Initial data now supplies an actual global solution with quantitative energy decay. -/
noncomputable section
namespace LinearInputGlobalConsequences
open Set Filter
open scoped Topology
open LinearInputDesign LinearInputGradient LinearInputTrajectoryExistence
open LinearInputGradientBound

/-- Actual global existence and the explicit convergence bound in one theorem. -/
theorem exists_global_convergent_solution {lam r u gamma target : ℝ}
    {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (z₀ : ℝ × ℝ) (hinit : target ≤ E lam r u z₀.1 z₀.2) :
    ∃ z : ℝ → ℝ × ℝ, z 0 = z₀ ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt z (vectorField lam r u gamma target b (z t)) t) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 ≤ E lam r u (z t).1 (z t).2 - target ∧
        E lam r u (z t).1 (z t).2 - target ≤
          (E lam r u z₀.1 z₀.2 - target) * Real.exp
            (-(gamma * gradientLowerBound lam r u target (E lam r u z₀.1 z₀.2)) * t)) ∧
      Tendsto (fun t => E lam r u (z t).1 (z t).2) atTop (𝓝 target) := by
  obtain ⟨z, hz₀, hz, _⟩ := LinearInputGlobalTrajectory.exists_global_solution
    hb hlam hgamma.le z₀ hinit
  have htraj := isTrajectory_of_global_solution hz
  have hi : target ≤ E lam r u (z 0).1 (z 0).2 := by simpa only [hz₀] using hinit
  obtain ⟨_, _, _, hlimit⟩ := LinearInputInvariance.energy_convergence_of_initial
    hlam hgamma htarget htraj hi
  refine ⟨z, hz₀, hz, ?_, hlimit⟩
  intro t ht
  simpa only [hz₀] using energy_error_exponential_of_initial
    hlam hgamma.le htarget htraj hi ht

/-- Above the target, the constructed convergent global solution is injective in time. -/
theorem exists_global_injective_convergent_solution {lam r u gamma target : ℝ}
    {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (z₀ : ℝ × ℝ) (hinit : target < E lam r u z₀.1 z₀.2) :
    ∃ z : ℝ → ℝ × ℝ, z 0 = z₀ ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt z (vectorField lam r u gamma target b (z t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → target < E lam r u (z t).1 (z t).2) ∧
      StrictAntiOn (fun t => E lam r u (z t).1 (z t).2) (Ici (0 : ℝ)) ∧
      InjOn z (Ici (0 : ℝ)) ∧
      Tendsto (fun t => E lam r u (z t).1 (z t).2) atTop (𝓝 target) := by
  obtain ⟨z, hz₀, hz, _, hlimit⟩ := exists_global_convergent_solution
    hb hlam hgamma htarget z₀ hinit.le
  have htraj := isTrajectory_of_global_solution hz
  have hi : target < E lam r u (z 0).1 (z 0).2 := by simpa only [hz₀] using hinit
  refine ⟨z, hz₀, hz, ?_,
    LinearInputStrictEnergy.energy_strictAntiOn hlam hgamma htarget htraj hi,
    ?_, hlimit⟩
  · intro t ht
    exact LinearInputStrictEnergy.energy_strictly_above_target htraj hi ht
  · simpa only [Prod.eta] using
      LinearInputStrictEnergy.trajectory_injOn hlam hgamma htarget htraj hi

end LinearInputGlobalConsequences
