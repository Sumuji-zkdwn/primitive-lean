/-! Actual forward-global feedback trajectories from compact energy confinement. -/

noncomputable section
open Set
namespace LinearInputGlobalTrajectory

open LinearInputDesign LinearInputTrajectoryExistence LinearInputRegularBand

/-- Every initial state above the target has an actual forward-global solution.
The compact band and the required uniform continuation time are derived. -/
theorem exists_global_solution {lam r u gamma target : ℝ} {b : ℝ × ℝ → ℝ}
    (hb : ContDiff ℝ 1 b) (hlam : 0 < lam) (hgamma : 0 ≤ gamma)
    (z₀ : ℝ × ℝ) (hinit : target ≤ E lam r u z₀.1 z₀.2) :
    ∃ z : ℝ → ℝ × ℝ, z 0 = z₀ ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt z (vectorField lam r u gamma target b (z t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → target ≤ E lam r u (z t).1 (z t).2 ∧
        E lam r u (z t).1 (z t).2 ≤ E lam r u z₀.1 z₀.2) := by
  let K : Set (ℝ × ℝ) := {z | target ≤ E lam r u z.1 z.2 ∧
    E lam r u z.1 z.2 ≤ E lam r u z₀.1 z₀.2}
  have hK : IsCompact K :=
    LinearInputCoercivity.isCompact_band hlam r u target (E lam r u z₀.1 z₀.2)
  have hstart : z₀ ∈ K := ⟨hinit, le_refl _⟩
  have hF : ContDiff ℝ 1 (vectorField lam r u gamma target b) :=
    contDiff_vectorField hb lam r u gamma target
  obtain ⟨ε, hε, hlocal⟩ := LinearInputCompactLocalExistence.exists_uniform_local_time hF hK
  have hstay : ∀ (a : ℝ) (z : ℝ → ℝ × ℝ), z 0 = z₀ →
      (∀ t ∈ Ioo (-ε) a,
        HasDerivAt z (vectorField lam r u gamma target b (z t)) t) →
      ∀ t : ℝ, 0 ≤ t → t < a → z t ∈ K := by
    intro a z hz₀ hz t ht hta
    have hi : target ≤ E lam r u (z 0).1 (z 0).2 := by simpa only [hz₀] using hinit
    have he := LinearInputFiniteBand.energy_band_on_Ioo hgamma hε hz hi ht hta
    simpa only [K, mem_ofPred_eq, hz₀] using he
  obtain ⟨z, hz₀, hz⟩ :=
    LinearInputGlobalContinuation.exists_forward_solution hF hstart hε hlocal hstay
  refine ⟨z, hz₀, hz, fun t ht => ?_⟩
  have hi : target ≤ E lam r u (z 0).1 (z 0).2 := by simpa only [hz₀] using hinit
  have he := LinearInputFiniteBand.energy_band_on_Icc hgamma ht
    (fun s hs => hz s hs.1) hi (show t ∈ Icc (0 : ℝ) t from ⟨ht, le_refl t⟩)
  simpa only [hz₀] using he

/-- The existing coordinate trajectory predicate now has actual global inhabitants. -/
theorem exists_global_coordinate_trajectory {lam r u gamma target : ℝ} {b : ℝ × ℝ → ℝ}
    (hb : ContDiff ℝ 1 b) (hlam : 0 < lam) (hgamma : 0 ≤ gamma)
    (x₀ y₀ : ℝ) (hinit : target ≤ E lam r u x₀ y₀) :
    ∃ x y : ℝ → ℝ, x 0 = x₀ ∧ y 0 = y₀ ∧
      IsTrajectory lam r u gamma target x y (fun t => b (x t, y t)) ∧
      ∀ t : ℝ, 0 ≤ t → target ≤ E lam r u (x t) (y t) ∧
        E lam r u (x t) (y t) ≤ E lam r u x₀ y₀ := by
  obtain ⟨z, hz₀, hz, hband⟩ := exists_global_solution hb hlam hgamma (x₀, y₀) hinit
  refine ⟨fun t => (z t).1, fun t => (z t).2,
    congrArg Prod.fst hz₀, congrArg Prod.snd hz₀, ?_, hband⟩
  exact isTrajectory_of_global_solution hz

/-- The original positive tangential coefficient admits actual forward-global solutions. -/
theorem exists_global_solution_one_add_sq {lam r u gamma target : ℝ}
    {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ 1 Q) (hlam : 0 < lam) (hgamma : 0 ≤ gamma)
    (z₀ : ℝ × ℝ) (hinit : target ≤ E lam r u z₀.1 z₀.2) :
    ∃ z : ℝ → ℝ × ℝ, z 0 = z₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt z (vectorField lam r u gamma target (fun q => 1 + Q q ^ 2) (z t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → target ≤ E lam r u (z t).1 (z t).2 ∧
        E lam r u (z t).1 (z t).2 ≤ E lam r u z₀.1 z₀.2) :=
  exists_global_solution (contDiff_const.add (hQ.pow 2)) hlam hgamma z₀ hinit

end LinearInputGlobalTrajectory
