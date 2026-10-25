/-!
Composition of existing curvature-energy conservation and the transverse square.
The variable remains arclength. A phase-energy minimum is a minimum of the
finite-dimensional quartic energy, not a minimum of the curve functional.
The rigidity and exclusion statements include zero input and zero pressure.
No new curve, feedback law, or minimizing curve is constructed here.
-/

noncomputable section
namespace LinearInputCurvatureRigidity

open Real Set
open LinearInputDesign

/-- If a forced curvature phase reaches a global minimum of its quartic energy
at one interior point, conservation makes every phase point a global minimum.
Comparison with the valley forces zero curvature derivative everywhere, hence
constant curvature on the interval. No uniqueness of the phase minimum is used. -/
theorem forced_phase_minimum_rigidity {k sigma u a b s₀ : ℝ}
    {kappa : ℝ → ℝ} (hk : k ≠ 0)
    (hκ : ContDiff ℝ 2 kappa)
    (heq : ∀ s ∈ Ioo a b,
      k * deriv (deriv kappa) s + k * (kappa s) ^ 3 / 2 -
        sigma * kappa s = k * u)
    (hs₀ : s₀ ∈ Ioo a b)
    (hmin : ∀ x y : ℝ,
      E (1 / 2) (-sigma / k) u (kappa s₀)
        (deriv kappa s₀ + sqrt 2 * kappa s₀) ≤
      E (1 / 2) (-sigma / k) u x y) :
    ∀ s ∈ Ioo a b, kappa s = kappa s₀ ∧ deriv kappa s = 0 := by
  obtain ⟨c, hc⟩ := LinearInputCurvatureBridge.forced_energy_constant hk hκ heq
  have hd : ∀ s ∈ Ioo a b, deriv kappa s = 0 := by
    intro s hs
    have hvalley :
        E (1 / 2) (-sigma / k) u (kappa s)
          (deriv kappa s + sqrt 2 * kappa s) ≤
        E (1 / 2) (-sigma / k) u (kappa s) (sqrt 2 * kappa s) := by
      rw [hc s hs, ← hc s₀ hs₀]
      exact hmin (kappa s) (sqrt 2 * kappa s)
    simp only [E, add_sub_cancel_right, sub_self,
      zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] at hvalley
    nlinarith [sq_nonneg (deriv kappa s)]
  have hconst : ∃ K : ℝ, ∀ s ∈ Ioo a b, kappa s = K := by
    apply isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    · intro s _
      exact (hκ.differentiable (by norm_num) s).differentiableWithinAt
    · exact hd
  obtain ⟨K, hK⟩ := hconst
  exact fun s hs => ⟨(hK s hs).trans (hK s₀ hs₀).symm, hd s hs⟩

/-- A nonconstant forced curvature curve has no phase point that globally
minimizes its quartic phase energy, for zero and nonzero input alike. -/
theorem forced_phase_not_minimum_of_nonconstant {k sigma u a b : ℝ}
    {kappa : ℝ → ℝ} (hk : k ≠ 0)
    (hκ : ContDiff ℝ 2 kappa)
    (heq : ∀ s ∈ Ioo a b,
      k * deriv (deriv kappa) s + k * (kappa s) ^ 3 / 2 -
        sigma * kappa s = k * u)
    (hnonconst : ¬ ∃ K : ℝ, ∀ s ∈ Ioo a b, kappa s = K) :
    ∀ s ∈ Ioo a b, ¬ ∀ x y : ℝ,
      E (1 / 2) (-sigma / k) u (kappa s)
        (deriv kappa s + sqrt 2 * kappa s) ≤
      E (1 / 2) (-sigma / k) u x y := by
  intro s hs hmin
  have hrigid := forced_phase_minimum_rigidity hk hκ heq hs hmin
  exact hnonconst ⟨kappa s, fun t ht => (hrigid t ht).1⟩

/-- The same pressure, tension, and conserved energy supplied by actual
area-constrained local minimality also obey the phase-minimum exclusion.
The pressure may be zero: nonconstant curvature alone gives the exclusion. -/
theorem locallyMinimizing_phase_minimum_exclusion {θ : ℝ → ℝ} {k ℓ : ℝ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hmin : LinearInputAreaMinimum.LocallyMinimizing k θ ℓ)
    (hnonconst : ¬ ∃ K : ℝ, ∀ s ∈ Ioo 0 ℓ, deriv θ s = K) :
    ∃ p sigma c : ℝ,
      LinearInputPressureStationary.Stationary k p θ ℓ ∧
      ∀ s ∈ Ioo 0 ℓ,
        (k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
          sigma * deriv θ s = p) ∧
        E (1 / 2) (-sigma / k) (p / k) (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s) = c ∧
        (¬ ∀ x y : ℝ,
          E (1 / 2) (-sigma / k) (p / k) (deriv θ s)
            (deriv (deriv θ) s + sqrt 2 * deriv θ s) ≤
          E (1 / 2) (-sigma / k) (p / k) x y) := by
  obtain ⟨p, sigma, c, hp, hchain⟩ :=
    LinearInputMainResult.locallyMinimizing_pressure_curvature_phase hℓ hk hθ hmin
  have hκ : ContDiff ℝ 2 (deriv θ) := hθ.deriv' (n := 2)
  have hforced : ∀ s ∈ Ioo 0 ℓ,
      k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
        sigma * deriv θ s = k * (p / k) := by
    intro s hs
    rw [(hchain s hs).1]
    field_simp
  refine ⟨p, sigma, c, hp, fun s hs => ⟨(hchain s hs).1, (hchain s hs).2.1, ?_⟩⟩
  exact forced_phase_not_minimum_of_nonconstant hk.ne' hκ hforced hnonconst s hs

end LinearInputCurvatureRigidity
