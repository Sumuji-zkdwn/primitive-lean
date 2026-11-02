/-! Initial data for the full coupled system yields spatial convergence. -/
noncomputable section
namespace LinearInputCoupledConsequences
open Set Filter
open scoped Topology
open LinearInputDesign LinearInputCoupledTrajectory
open LinearInputGradientBound LinearInputLevelConvergence

/-- An actual coupled global solution, internal bounds, and quantitative
energy and spatial convergence, all obtained from the initial data. -/
theorem exists_global_convergent_solution {n : ℕ} {lam r u gamma target : ℝ}
    {b : State n → ℝ} {kappa rho : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    (hb : ContDiff ℝ 1 b) (hPhi : ContDiff ℝ 1 Phi)
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hkappa : ∀ i, 0 < kappa i)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (q₀ : State n) (hinit : target ≤ E lam r u q₀.1.1 q₀.1.2) :
    ∃ M : Fin n → ℝ, (∀ i, 0 ≤ M i) ∧ ∃ q : ℝ → State n, q 0 = q₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, |(q t).2 i| ≤ M i) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 ≤ E lam r u (q t).1.1 (q t).1.2 - target ∧
        E lam r u (q t).1.1 (q t).1.2 - target ≤
          (E lam r u q₀.1.1 q₀.1.2 - target) * Real.exp
            (-(gamma * gradientLowerBound lam r u target (E lam r u q₀.1.1 q₀.1.2)) * t)) ∧
      (∀ t : ℝ, 0 ≤ t →
        Metric.infDist (q t).1 {p : ℝ × ℝ | E lam r u p.1 p.2 = target} ≤
          bandRadius lam r u (E lam r u q₀.1.1 q₀.1.2) /
            (target - (max (-r) 0) ^ 2 / (12 * lam)) *
            (E lam r u q₀.1.1 q₀.1.2 - target) * Real.exp
              (-(gamma * gradientLowerBound lam r u target (E lam r u q₀.1.1 q₀.1.2)) * t)) ∧
      Tendsto (fun t => E lam r u (q t).1.1 (q t).1.2) atTop (𝓝 target) ∧
      Tendsto (fun t => Metric.infDist (q t).1
        {p : ℝ × ℝ | E lam r u p.1 p.2 = target}) atTop (𝓝 0) := by
  obtain ⟨M, hM, q, hq₀, hq, hbound⟩ :=
    LinearInputCoupledTrajectory.exists_global_solution hb hPhi hlam hgamma.le hkappa q₀ hinit
  have htraj := isTrajectory_of_global_solution hq
  have hi : target ≤ E lam r u (q 0).1.1 (q 0).1.2 := by simpa only [hq₀] using hinit
  obtain ⟨_, _, _, hE⟩ := LinearInputInvariance.energy_convergence_of_initial
    hlam hgamma htarget htraj hi
  refine ⟨M, hM, q, hq₀, hq, fun t ht => (hbound t ht).2, ?_, ?_, hE, ?_⟩
  · intro t ht
    simpa only [hq₀] using energy_error_exponential_of_initial
      hlam hgamma.le htarget htraj hi ht
  · intro t ht
    simpa only [hq₀, Prod.eta] using
      (spatial_error_exponential_of_initial hlam hgamma.le htarget htraj hi ht).2
  · simpa only [Prod.eta] using
      spatial_convergence_of_initial hlam hgamma htarget htraj hi

/-- Strict initial energy excess also prevents any spatial return, even
while the internal state evolves. No limit of a single spatial point is asserted. -/
theorem exists_global_injective_convergent_solution {n : ℕ} {lam r u gamma target : ℝ}
    {b : State n → ℝ} {kappa rho : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    (hb : ContDiff ℝ 1 b) (hPhi : ContDiff ℝ 1 Phi)
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hkappa : ∀ i, 0 < kappa i)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (q₀ : State n) (hinit : target < E lam r u q₀.1.1 q₀.1.2) :
    ∃ q : ℝ → State n, q 0 = q₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → target < E lam r u (q t).1.1 (q t).1.2) ∧
      StrictAntiOn (fun t => E lam r u (q t).1.1 (q t).1.2) (Ici (0 : ℝ)) ∧
      InjOn (fun t => (q t).1) (Ici (0 : ℝ)) ∧
      Tendsto (fun t => E lam r u (q t).1.1 (q t).1.2) atTop (𝓝 target) ∧
      Tendsto (fun t => Metric.infDist (q t).1
        {p : ℝ × ℝ | E lam r u p.1 p.2 = target}) atTop (𝓝 0) := by
  obtain ⟨_, _, q, hq₀, hq, _, _, _, hE, hdist⟩ := exists_global_convergent_solution
    hb hPhi hlam hgamma hkappa htarget q₀ hinit.le
  have htraj := isTrajectory_of_global_solution hq
  have hi : target < E lam r u (q 0).1.1 (q 0).1.2 := by simpa only [hq₀] using hinit
  refine ⟨q, hq₀, hq, ?_,
    LinearInputStrictEnergy.energy_strictAntiOn hlam hgamma htarget htraj hi, ?_, hE, hdist⟩
  · intro t ht
    exact LinearInputStrictEnergy.energy_strictly_above_target htraj hi ht
  · simpa only [Prod.eta] using
      LinearInputStrictEnergy.trajectory_injOn hlam hgamma htarget htraj hi

end LinearInputCoupledConsequences
