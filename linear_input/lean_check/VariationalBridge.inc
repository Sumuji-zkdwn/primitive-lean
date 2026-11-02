import Elastica.MinimumConditions
import Elastica.AffineEquivalence

/-!
The classical phase energy is obtained from the existing variational theorem.
Stationarity is the original predicate of actual parameter derivatives.  For a
nonstraight constrained local minimum even this predicate is derived.  The
independent variable is arc length, not a new physical-time evolution.
-/

noncomputable section
namespace LinearInputVariationalBridge

open Real Set Elastica LinearInputDesign LinearInputGradient

/-- A curvature-linear density changes the actual energy only by the endpoint
angle difference.  Here the endpoint angles are real-valued lifts. -/
theorem energy_linear_density {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (u : ℝ) :
    energy (fun q => ε q - u * q) θ ℓ =
      energy ε θ ℓ - u * (θ ℓ - θ 0) := by
  have h := energy_affine_density hε hθ (-u) 0 ℓ
  simpa only [neg_mul, add_neg_cancel, zero_mul, add_zero, sub_eq_add_neg] using h

/-- Fixed endpoint-angle variations have the same actual derivative
stationarity after adding a curvature-linear density. -/
theorem stationary_linear_density_iff {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (u : ℝ) :
    Stationary (fun q => ε q - u * q) θ ℓ ↔ Stationary ε θ ℓ := by
  simpa only [neg_mul, add_zero, sub_eq_add_neg] using
    stationary_affine_density_iff hε hθ (-u) 0

/-- The original constrained local-minimum predicate is unchanged by this
linear density, including its original C¹ neighborhood definition. -/
theorem locallyMinimizing_linear_density_iff {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (u : ℝ) :
    LocallyMinimizing (fun q => ε q - u * q) θ ℓ ↔
      LocallyMinimizing ε θ ℓ := by
  simpa only [neg_mul, add_zero, sub_eq_add_neg] using
    locallyMinimizing_affine_density_iff hε hθ (-u) 0

/-- The actual constrained stationarity theorem supplies the classical
curvature equation; it is not assumed as extra input. -/
theorem stationary_quadratic_curvature {θ : ℝ → ℝ} {ℓ k : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hstat : Stationary (fun q => k * q ^ 2 / 2) θ ℓ) :
    ∃ σ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
        σ * deriv θ s = 0 := by
  obtain ⟨lam, μ, σ, heq⟩ :=
    stationary_angle_firstIntegral_curvature hℓ (by fun_prop) hθ hstat
  refine ⟨σ, fun s hs => ?_⟩
  exact quadratic_curvature_equation (hθ.deriv' (n := 2)) (heq s hs).2.2

/-- Actual constrained stationarity produces the quartic phase energy and its
Hamiltonian equations along arc length.  The phase input is exactly zero. -/
theorem stationary_quadratic_phase_energy {θ : ℝ → ℝ} {ℓ k : ℝ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hstat : Stationary (fun q => k * q ^ 2 / 2) θ ℓ) :
    ∃ σ c : ℝ, ∀ s ∈ Ioo 0 ℓ,
      E (1 / 2) (-σ / k) 0 (deriv θ s)
        (deriv (deriv θ) s + sqrt 2 * deriv θ s) = c ∧
      HasDerivAt (deriv θ)
        (gy (deriv θ s) (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s ∧
      HasDerivAt (fun t => deriv (deriv θ) t + sqrt 2 * deriv θ t)
        (-gx (1 / 2) (-σ / k) 0 (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s := by
  obtain ⟨σ, heq⟩ := stationary_quadratic_curvature hℓ hθ hstat
  have hκ : ContDiff ℝ 2 (deriv θ) := hθ.deriv' (n := 2)
  obtain ⟨c, hc⟩ := LinearInputCurvatureBridge.energy_constant (ne_of_gt hk) hκ heq
  refine ⟨σ, c, fun s hs => ⟨hc s hs, ?_⟩⟩
  exact LinearInputCurvatureBridge.phase_hasDerivAt (ne_of_gt hk) hκ (heq s hs)

/-- A nonstraight constrained local minimum of the quadratic density with
any curvature-linear addition yields the same unforced quartic phase system.
Neither stationarity nor the curvature equation is supplied as a hypothesis.
The constant σ is chosen for the quadratic representative of the density. -/
theorem locallyMinimizing_linear_quadratic_phase_energy
    {θ : ℝ → ℝ} {ℓ k u : ℝ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hne : ¬ ∀ s ∈ Icc 0 ℓ, θ s = θ 0)
    (hmin : LocallyMinimizing (fun q => k * q ^ 2 / 2 - u * q) θ ℓ) :
    ∃ σ c : ℝ, ∀ s ∈ Ioo 0 ℓ,
      E (1 / 2) (-σ / k) 0 (deriv θ s)
        (deriv (deriv θ) s + sqrt 2 * deriv θ s) = c ∧
      HasDerivAt (deriv θ)
        (gy (deriv θ s) (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s ∧
      HasDerivAt (fun t => deriv (deriv θ) t + sqrt 2 * deriv θ t)
        (-gx (1 / 2) (-σ / k) 0 (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s := by
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  have hmin0 : LocallyMinimizing (fun q => k * q ^ 2 / 2) θ ℓ :=
    (locallyMinimizing_linear_density_iff (by fun_prop) hθ1 u).mp hmin
  have hstat := locallyMinimizing_stationary_of_nonstraight hℓ (by fun_prop) hθ1
    (exists_nonzero_curvature_of_nonconstant hℓ hθ1 hne) hmin0
  exact stationary_quadratic_phase_energy hℓ hk hθ hstat

end LinearInputVariationalBridge
