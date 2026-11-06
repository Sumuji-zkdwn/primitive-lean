import Elastica.ExponentialWeight
import Mathlib.Tactic

/-!
# A finite transport / history-cost bridge (isolated extension)

This is a restricted mathematical bridge between Okanohara's finite-time
transport and history-conditioned adaptation viewpoints (arXiv:2601.17607
and arXiv:2602.07950v3) and the existing Elastica energy/weight operations.

It DOES NOT formalize the full Wasserstein-2 metric, entropy production,
continuous probability-measure dynamics, fluid-fiber constitutive laws,
or computational complexity. A two-segment scalar action is a finite
analogue of the speed-limit inequality, not the general ESL theorem.

The additive history penalty is an explicit model choice. The already
defined Elastica.energy and Elastica.exponentialWeight are reused directly.
-/

namespace Elastica

/-- Signed endpoint displacement of two unit-duration transport segments. -/
def twoStepTransport (u v : ℝ) : ℝ := u + v

/-- Quadratic action of the two velocity segments. -/
def twoStepAction (u v : ℝ) : ℝ := u ^ 2 + v ^ 2

/-- Discrete finite-time speed limit: displacement squared is at most
duration (two units) times quadratic action. -/
theorem two_step_speed_limit (u v : ℝ) :
    (twoStepTransport u v) ^ 2 ≤ 2 * twoStepAction u v := by
  unfold twoStepTransport twoStepAction
  nlinarith [sq_nonneg (u - v)]

/-- The constant-speed trajectory attains the scalar lower bound. -/
theorem balanced_path_attains_bound (d : ℝ) :
    (twoStepTransport (d / 2) (d / 2)) ^ 2 =
      2 * twoStepAction (d / 2) (d / 2) := by
  unfold twoStepTransport twoStepAction
  ring

/-- Unit-horizon, unit-displacement adaptation cost at memory h.
This is the constant-control toy model's action, not a generic complexity bound. -/
def historyUnitCost (h : ℝ) : ℝ := (1 + h) ^ 2

/-- The input required to produce displacement d under gain 1/(1+h). -/
def requiredInput (h d : ℝ) : ℝ := (1 + h) * d

/-- The quadratic action of this required constant input. -/
def requiredAction (h d : ℝ) : ℝ := (requiredInput h d) ^ 2

/-- Exact history-sensitive input cost for the unit-time scalar model. -/
theorem required_action_exact (h d : ℝ) :
    requiredAction h d = historyUnitCost h * d ^ 2 := by
  unfold requiredAction requiredInput historyUnitCost
  ring

/-- Under nonnegative memory, larger memory cannot reduce unit cost. -/
theorem history_unit_cost_mono {h₀ h₁ : ℝ}
    (h₀_nonneg : 0 ≤ h₀) (hle : h₀ ≤ h₁) :
    historyUnitCost h₀ ≤ historyUnitCost h₁ := by
  have hs : 0 ≤ 2 + h₀ + h₁ := by linarith
  have hp : 0 ≤ (h₁ - h₀) * (2 + h₀ + h₁) :=
    mul_nonneg (sub_nonneg.mpr hle) hs
  unfold historyUnitCost
  nlinarith

/-- An extended state (observable position, unobserved memory). -/
abbrev HistoryState := ℝ × ℝ

def readPosition (s : HistoryState) : ℝ := s.1

def adaptationCost (s : HistoryState) : ℝ := historyUnitCost s.2

/-- Equal visible position need not imply equal adaptation cost. -/
theorem same_observation_different_cost :
    readPosition ((0 : ℝ), (0 : ℝ)) =
      readPosition ((0 : ℝ), (2 : ℝ)) ∧
    adaptationCost ((0 : ℝ), (0 : ℝ)) ≠
      adaptationCost ((0 : ℝ), (2 : ℝ)) := by
  constructor
  · rfl
  · norm_num [adaptationCost, historyUnitCost]

/-- Adaptation cost does not factor through present-position observation. -/
theorem adaptation_cost_not_observation_factor :
    ¬ ∃ f : ℝ → ℝ, ∀ s : HistoryState,
        adaptationCost s = f (readPosition s) := by
  rintro ⟨f, hf⟩
  have h₀ := hf ((0 : ℝ), (0 : ℝ))
  have h₂ := hf ((0 : ℝ), (2 : ℝ))
  norm_num [adaptationCost, historyUnitCost, readPosition] at h₀ h₂
  linarith

/-- Explicitly chosen augmentation of the existing curvature integral. -/
noncomputable def historyAugmentedEnergy (ε θ : ℝ → ℝ) (ℓ h : ℝ) : ℝ :=
  energy ε θ ℓ + historyUnitCost h

/-- The history penalty cannot lower the original Elastica energy. -/
theorem energy_le_history_augmented (ε θ : ℝ → ℝ) (ℓ h : ℝ) :
    energy ε θ ℓ ≤ historyAugmentedEnergy ε θ ℓ h := by
  unfold historyAugmentedEnergy historyUnitCost
  nlinarith [sq_nonneg (1 + h)]

/-- For the same actual curve, ordered nonnegative histories order costs. -/
theorem history_augmented_energy_mono (ε θ : ℝ → ℝ) (ℓ : ℝ)
    {h₀ h₁ : ℝ} (h₀_nonneg : 0 ≤ h₀) (hle : h₀ ≤ h₁) :
    historyAugmentedEnergy ε θ ℓ h₀ ≤
      historyAugmentedEnergy ε θ ℓ h₁ := by
  have hc := history_unit_cost_mono h₀_nonneg hle
  unfold historyAugmentedEnergy
  linarith

/-- Apply the existing whole-energy exponential representation to the
history-augmented energy, not to the curvature density. -/
noncomputable def historyAugmentedWeight (β : ℝ) (ε θ : ℝ → ℝ) (ℓ h : ℝ) : ℝ :=
  Real.exp (-β * historyAugmentedEnergy ε θ ℓ h)

/-- Existing Elastica exponential-weight order remains valid after adding
the explicit nonnegative history cost. This invokes a *previous* theorem. -/
theorem history_weight_le_original {β : ℝ} (hβ : 0 < β)
    (ε θ : ℝ → ℝ) (ℓ h : ℝ) :
    historyAugmentedWeight β ε θ ℓ h ≤
      exponentialWeight β ε θ ℓ := by
  change Real.exp (-β * historyAugmentedEnergy ε θ ℓ h) ≤
    Real.exp (-β * energy ε θ ℓ)
  exact (exp_neg_mul_le_exp_neg_mul_iff hβ).2
    (energy_le_history_augmented ε θ ℓ h)

end Elastica

/-! Explicit kernel-axiom audit for the standalone extension. -/
#print axioms Elastica.two_step_speed_limit
#print axioms Elastica.balanced_path_attains_bound
#print axioms Elastica.required_action_exact
#print axioms Elastica.history_unit_cost_mono
#print axioms Elastica.same_observation_different_cost
#print axioms Elastica.adaptation_cost_not_observation_factor
#print axioms Elastica.energy_le_history_augmented
#print axioms Elastica.history_augmented_energy_mono
#print axioms Elastica.history_weight_le_original
