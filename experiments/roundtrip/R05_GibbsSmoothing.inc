import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Round trip 5: corner of the value function → Gibbs free energy → pencil again

Input: round 4 (the minimum of two affine observation lines has a corner).
Translation (statistical mechanics): replace the minimum by the Gibbs free energy
`-β⁻¹ log Σ exp(-β eᵢ)`, using the baseline order-reversal of `exp(-β ·)`.
Back-translation: for the two Maxwell states `e± = E₀ ∓ a u`, the free energy is
`E₀ - β⁻¹ log (2 cosh (β a u))`, smooth with slope `-a tanh (β a u)`, and it squeezes
to the cornered value `E₀ - a|u|` as `β → ∞`.
Additional hypothesis: the configuration space is restricted to the two minimizers;
this is a two-state model, not the Gibbs measure of the continuous design energy.
-/

noncomputable section
namespace RoundTrip05
open Real Filter Topology LinearInputObservation

/-- Two-state free energy. -/
def freeEnergy (β e₁ e₂ : ℝ) : ℝ := -log (exp (-β * e₁) + exp (-β * e₂)) / β

theorem freeEnergy_le_min {β : ℝ} (hβ : 0 < β) (e₁ e₂ : ℝ) :
    freeEnergy β e₁ e₂ ≤ min e₁ e₂ := by
  unfold freeEnergy
  have hS : exp (-β * min e₁ e₂) ≤ exp (-β * e₁) + exp (-β * e₂) := by
    rcases min_choice e₁ e₂ with h | h <;> rw [h] <;>
      linarith [exp_pos (-β * e₁), exp_pos (-β * e₂)]
  have hlog : -β * min e₁ e₂ ≤ log (exp (-β * e₁) + exp (-β * e₂)) := by
    rw [← log_exp (-β * min e₁ e₂)]
    exact log_le_log (exp_pos _) hS
  rw [div_le_iff₀ hβ]
  linarith

theorem min_sub_log_two_le_freeEnergy {β : ℝ} (hβ : 0 < β) (e₁ e₂ : ℝ) :
    min e₁ e₂ - log 2 / β ≤ freeEnergy β e₁ e₂ := by
  unfold freeEnergy
  have h₁ : exp (-β * e₁) ≤ exp (-β * min e₁ e₂) :=
    (Elastica.exp_neg_mul_le_exp_neg_mul_iff hβ).2 (min_le_left _ _)
  have h₂ : exp (-β * e₂) ≤ exp (-β * min e₁ e₂) :=
    (Elastica.exp_neg_mul_le_exp_neg_mul_iff hβ).2 (min_le_right _ _)
  have hlog : log (exp (-β * e₁) + exp (-β * e₂)) ≤ log 2 + -β * min e₁ e₂ := by
    rw [← log_exp (-β * min e₁ e₂), ← log_mul (by norm_num) (exp_pos _).ne']
    exact log_le_log (by positivity) (by linarith)
  have hrw : min e₁ e₂ - log 2 / β = (β * min e₁ e₂ - log 2) / β := by
    field_simp
  rw [hrw, div_le_div_iff_of_pos_right hβ]
  linarith

/-- Symmetric Maxwell pair: closed form with `cosh`. -/
theorem freeEnergy_maxwell (β E₀ a u : ℝ) (hβ : β ≠ 0) :
    freeEnergy β (E₀ - a * u) (E₀ + a * u) =
      E₀ - log (2 * cosh (β * a * u)) / β := by
  unfold freeEnergy
  have : exp (-β * (E₀ - a * u)) + exp (-β * (E₀ + a * u)) =
      exp (-β * E₀) * (2 * cosh (β * a * u)) := by
    rw [cosh_eq]
    rw [show -β * (E₀ - a * u) = -β * E₀ + β * a * u by ring,
      show -β * (E₀ + a * u) = -β * E₀ + -(β * a * u) by ring, exp_add, exp_add]
    ring
  rw [this, log_mul (exp_pos _).ne' (by positivity), log_exp]
  field_simp
  ring

/-- The smoothed corner: slope `-a tanh (β a u)` (the Gibbs mean of the observable). -/
theorem hasDerivAt_freeEnergy_maxwell {β : ℝ} (hβ : β ≠ 0) (E₀ a u : ℝ) :
    HasDerivAt (fun t => freeEnergy β (E₀ - a * t) (E₀ + a * t))
      (-a * (sinh (β * a * u) / cosh (β * a * u))) u := by
  have hfun : (fun t => freeEnergy β (E₀ - a * t) (E₀ + a * t)) =
      fun t => E₀ - log (2 * cosh (β * a * t)) / β := by
    funext t; exact freeEnergy_maxwell β E₀ a t hβ
  rw [hfun]
  have hc : HasDerivAt (fun t => 2 * cosh (β * a * t)) (2 * (sinh (β * a * u) * (β * a))) u :=
    ((hasDerivAt_cosh (β * a * u)).comp u ((hasDerivAt_id u).const_mul (β * a))).const_mul 2
      |>.congr_deriv (by simp)
  have hpos : 0 < 2 * cosh (β * a * u) := by positivity
  have hl := (hc.log hpos.ne').div_const β
  convert (hasDerivAt_const u E₀).sub hl using 1
  field_simp
  ring

/-- Susceptibility at the Maxwell point: `β a²`, which diverges as `β → ∞`. -/
theorem susceptibility_at_zero (β a : ℝ) :
    HasDerivAt (fun u => a * (sinh (β * a * u) / cosh (β * a * u))) (β * a ^ 2) 0 := by
  have hs : HasDerivAt (fun u => sinh (β * a * u)) (cosh (β * a * 0) * (β * a)) 0 :=
    (hasDerivAt_sinh _).comp 0 ((hasDerivAt_id 0).const_mul (β * a)) |>.congr_deriv (by simp)
  have hc : HasDerivAt (fun u => cosh (β * a * u)) (sinh (β * a * 0) * (β * a)) 0 :=
    (hasDerivAt_cosh _).comp 0 ((hasDerivAt_id 0).const_mul (β * a)) |>.congr_deriv (by simp)
  have h := (hs.div hc (by simp)).const_mul a
  convert h using 1
  simp
  ring

/-- Squeeze: the free energy converges to the cornered two-state value as `β → ∞`. -/
theorem tendsto_freeEnergy_maxwell (E₀ a u : ℝ) :
    Tendsto (fun β => freeEnergy β (E₀ - a * u) (E₀ + a * u)) atTop
      (𝓝 (min (E₀ - a * u) (E₀ + a * u))) := by
  have hlow : Tendsto (fun β : ℝ => min (E₀ - a * u) (E₀ + a * u) - log 2 / β) atTop
      (𝓝 (min (E₀ - a * u) (E₀ + a * u))) := by
    simpa using (tendsto_const_nhds (x := min (E₀ - a * u) (E₀ + a * u))).sub
      ((tendsto_const_nhds (x := log 2)).div_atTop tendsto_id)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with β hβ
    exact min_sub_log_two_le_freeEnergy hβ _ _
  · filter_upwards [eventually_gt_atTop 0] with β hβ
    exact freeEnergy_le_min hβ _ _

/-- The limit is exactly the round-4 corner: not differentiable at `u = 0` when `a ≠ 0`. -/
theorem limit_not_differentiableAt (E₀ : ℝ) {a : ℝ} (ha : a ≠ 0) :
    ¬ DifferentiableAt ℝ (fun u => min (E₀ - a * u) (E₀ + a * u)) 0 := by
  refine RoundTrip04.not_differentiableAt_of_two_minimizers (fun _ : Bool => E₀)
    (fun b => if b then a else -a) _ (fun u b => ?_) (z₁ := true) (z₂ := false)
    (by simp [energy]) (by simp [energy]) (by simp; intro h; exact ha (by linarith))
  cases b
  · exact (min_le_right _ _).trans (le_of_eq (by simp [energy]; ring))
  · exact (min_le_left _ _).trans (le_of_eq (by simp [energy]; ring))

end RoundTrip05
