/-!
Positive similarities of every candidate curve act on the finite Bayesian
exponential-weight update as a change of inverse temperature.  The scaling
laws are the existing Elastica energy theorems (`energy_scaling_quadratic`,
`energy_scaling_of_homogeneous`), used inside the proofs; the finite candidate
family, prior and inverse temperature are explicit choices.  Every candidate is
scaled by the same factor, so lengths and endpoint data are transported, not
held fixed.  No minimizing curve, dynamics or physical temperature is asserted.
-/

noncomputable section
open Real Filter
open scoped Topology

namespace LinearInputScaleTemperature

open LinearInputBayes

/-- For a density homogeneous of degree `m`, scaling every candidate curve by
`a > 0` gives the same posterior as the unscaled candidates at inverse
temperature `β * a^(1-m)`.  The energy law is the existing Elastica theorem. -/
theorem scaled_posterior_homogeneous {α : Type*} [Fintype α] (w : α → ℝ)
    {ε : ℝ → ℝ} {θ : α → ℝ → ℝ} (hθ : ∀ x, Differentiable ℝ (θ x))
    {a m : ℝ} (ha : 0 < a)
    (hε : ∀ t : ℝ, 0 < t → ∀ q : ℝ, ε (t * q) = t ^ m * ε q) (β ℓ : ℝ) :
    posterior w (fun x => Elastica.exponentialWeight β ε (fun s => θ x (s / a)) (a * ℓ)) =
      posterior w (fun x => Elastica.exponentialWeight (β * a ^ (1 - m)) ε (θ x) ℓ) := by
  refine congrArg (posterior w) (funext fun x => ?_)
  unfold Elastica.exponentialWeight
  rw [Elastica.energy_scaling_of_homogeneous (hθ x) ha hε ℓ]
  congr 1
  ring

/-- The classical quadratic density: scaling every candidate by `a > 0` is the
same update at inverse temperature `β / a`. -/
theorem scaled_posterior_quadratic {α : Type*} [Fintype α] (w : α → ℝ)
    {θ : α → ℝ → ℝ} (hθ : ∀ x, Differentiable ℝ (θ x)) {a : ℝ} (ha : 0 < a)
    (β k ℓ : ℝ) :
    posterior w (fun x => Elastica.exponentialWeight β (fun q => k * q ^ 2 / 2)
        (fun s => θ x (s / a)) (a * ℓ)) =
      posterior w (fun x => Elastica.exponentialWeight (β / a) (fun q => k * q ^ 2 / 2)
        (θ x) ℓ) := by
  refine congrArg (posterior w) (funext fun x => ?_)
  unfold Elastica.exponentialWeight
  rw [Elastica.energy_scaling_quadratic (hθ x) ha k ℓ]
  congr 1
  ring

/-- The same statement as an exponential tilt of the unscaled bending energies. -/
theorem scaled_posterior_quadratic_tilt {α : Type*} [Fintype α] (w : α → ℝ)
    {θ : α → ℝ → ℝ} (hθ : ∀ x, Differentiable ℝ (θ x)) {a : ℝ} (ha : 0 < a)
    (β k ℓ : ℝ) :
    posterior w (fun x => Elastica.exponentialWeight β (fun q => k * q ^ 2 / 2)
        (fun s => θ x (s / a)) (a * ℓ)) =
      tilt w (-(β / a)) (fun x => Elastica.energy (fun q => k * q ^ 2 / 2) (θ x) ℓ) := by
  rw [scaled_posterior_quadratic w hθ ha β k ℓ]
  exact curve_weight_as_tilt w (β / a) (fun q => k * q ^ 2 / 2) θ ℓ

/-- Enlarging every candidate without bound removes the influence of bending:
for a prior distribution, each posterior probability tends to its prior value.
The limit uses the scaling law, not an assumed temperature dependence. -/
theorem scaled_posterior_tendsto_prior {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) {θ : α → ℝ → ℝ} (hθ : ∀ x, Differentiable ℝ (θ x))
    (β k ℓ : ℝ) (x : α) :
    Tendsto (fun a : ℝ => posterior w (fun y => Elastica.exponentialWeight β
        (fun q => k * q ^ 2 / 2) (fun s => θ y (s / a)) (a * ℓ)) x) atTop (𝓝 (w x)) := by
  set B : α → ℝ := fun y => Elastica.energy (fun q => k * q ^ 2 / 2) (θ y) ℓ with hB
  have heq : (fun a : ℝ => posterior w (fun y => exp (-(β / a) * B y)) x) =ᶠ[atTop]
      (fun a : ℝ => posterior w (fun y => Elastica.exponentialWeight β
        (fun q => k * q ^ 2 / 2) (fun s => θ y (s / a)) (a * ℓ)) x) := by
    filter_upwards [eventually_gt_atTop 0] with a ha
    rw [scaled_posterior_quadratic w hθ ha β k ℓ]
    rfl
  refine Tendsto.congr' heq ?_
  have h0 : Tendsto (fun a : ℝ => β / a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hL : ∀ y, Tendsto (fun a : ℝ => w y * exp (-(β / a) * B y)) atTop (𝓝 (w y)) := by
    intro y
    have h := tendsto_const_nhds (x := w y) |>.mul ((h0.neg.mul_const (B y)).rexp)
    simpa using h
  have hm : Tendsto (fun a : ℝ => mass (fun y => w y * exp (-(β / a) * B y))) atTop
      (𝓝 (mass w)) := by
    unfold mass
    exact tendsto_finsetSum _ (fun y _ => hL y)
  have h := (hL x).div hm (by rw [hw.2]; norm_num)
  rw [hw.2, div_one] at h
  exact h

end LinearInputScaleTemperature
