import Elastica.Stationary

/-! A third actual linearized constraint adds a third multiplier.
No rank assumption is needed once stationarity on the common kernel is given.
This does not assert that every constrained local minimum has that stationarity.
-/
noncomputable section
namespace LinearInputConstraints

theorem exists_three_multipliers_of_kernel
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f c₁ c₂ c₃ : V →ₗ[ℝ] ℝ)
    (h : ∀ v, c₁ v = 0 → c₂ v = 0 → c₃ v = 0 → f v = 0) :
    ∃ lam mu p : ℝ, ∀ v,
      f v + lam * c₁ v + mu * c₂ v + p * c₃ v = 0 := by
  let c : V →ₗ[ℝ] ℝ × (ℝ × ℝ) := c₁.prod (c₂.prod c₃)
  have hf : f ∈ (LinearMap.ker c).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    have hv' : c v = 0 := hv
    exact h v (congrArg Prod.fst hv')
      (congrArg (fun z : ℝ × (ℝ × ℝ) => z.2.1) hv')
      (congrArg (fun z : ℝ × (ℝ × ℝ) => z.2.2) hv')
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hf
  obtain ⟨g, hg⟩ := hf
  refine ⟨-g (1, (0, 0)), -g (0, (1, 0)), -g (0, (0, 1)), ?_⟩
  intro v
  have hgv : g (c v) = f v := DFunLike.congr_fun hg v
  have hc : c v = (c₁ v) • (1, (0, 0)) +
      (c₂ v) • (0, (1, 0)) + (c₃ v) • (0, (0, 1)) := by
    ext <;> simp [c]
  rw [hc, map_add, map_add, map_smul, map_smul, map_smul] at hgv
  simp only [smul_eq_mul] at hgv
  nlinarith

end LinearInputConstraints
