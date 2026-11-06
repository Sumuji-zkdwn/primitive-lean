/-!
# Round trip 12: formal group law → Tsallis (q-deformed) energy → Gibbs weight

Input: round 11 (`powerLog p` sends products to `⊕ₚ`) and round 5 (Gibbs weights).
Translation (non-extensive statistics): define the deformed energy
`E_p = -powerLog p (exp(-β E)) / β = (1 - e^{-pβE})/(pβ)`. Because the baseline weight is
multiplicative over arclength pieces, `E_p` is additive only up to the cross term
`-pβ E_p(I) E_p(J)`, i.e. it composes by `⊕_{-pβ}`. Back-translation: this law is exactly
the baseline `powerLog_exponentialWeight_split` read through round 11, the order of
curves is preserved (baseline `energy_le_iff_powerLog_exponentialWeight_le`), and `p → 0`
returns the additive energy (baseline `tendsto_powerLog_exponentialWeight_zero`).
-/

noncomputable section
namespace RoundTrip12
open Real Filter Topology Elastica RoundTrip11

/-- Deformed (Tsallis-type) energy of a real energy value. -/
def deform (p β e : ℝ) : ℝ := -powerLog p (exp (-β * e)) / β

/-- Closed form for `p ≠ 0`. -/
theorem deform_eq {p β : ℝ} (hp : p ≠ 0) (e : ℝ) :
    deform p β e = (1 - exp (-(p * β * e))) / (p * β) := by
  unfold deform powerLog
  rw [if_neg hp, ← exp_mul]
  by_cases hβ : β = 0
  · subst hβ; simp
  · rw [show -β * e * p = -(p * β * e) by ring]
    field_simp
    ring

/-- Non-additivity: `E_p(e₁ + e₂) = E_p(e₁) ⊕_{-pβ} E_p(e₂)` (`β ≠ 0`). -/
theorem deform_add {p β : ℝ} (hβ : β ≠ 0) (e₁ e₂ : ℝ) :
    deform p β (e₁ + e₂) = fgl (-(p * β)) (deform p β e₁) (deform p β e₂) := by
  unfold deform
  rw [show -β * (e₁ + e₂) = -β * e₁ + -β * e₂ by ring, exp_add,
    powerLog_hom p (exp_pos _) (exp_pos _)]
  unfold fgl
  field_simp
  ring

/-- The baseline split identity in deformed-energy form. -/
theorem deform_energy_split {ε θ : ℝ → ℝ} (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ)
    {β : ℝ} (hβ : β ≠ 0) (p a ℓ : ℝ) :
    -powerLog p (exponentialWeight β ε θ ℓ) / β =
      fgl (-(p * β)) (deform p β (∫ s in 0..a, ε (deriv θ s)))
        (deform p β (∫ s in a..ℓ, ε (deriv θ s))) := by
  rw [powerLog_exponentialWeight_split hε hθ p β a ℓ]
  unfold deform fgl exponentialWeight energy
  field_simp
  ring

/-- For `pβ > 0` and nonnegative pieces, the deformed energy is subadditive. -/
theorem deform_subadditive {p β e₁ e₂ : ℝ} (hβ : 0 < β) (hp : 0 < p)
    (h₁ : 0 ≤ e₁) (h₂ : 0 ≤ e₂) :
    deform p β (e₁ + e₂) ≤ deform p β e₁ + deform p β e₂ := by
  rw [deform_add hβ.ne']
  unfold fgl
  have hd : ∀ e, 0 ≤ e → 0 ≤ deform p β e := by
    intro e he
    rw [deform_eq hp.ne']
    apply div_nonneg _ (by positivity)
    have : exp (-(p * β * e)) ≤ 1 := exp_le_one_iff.2 (by
      have := mul_nonneg (mul_nonneg hp.le hβ.le) he; linarith)
    linarith
  have := mul_nonneg (mul_nonneg (mul_nonneg hp.le hβ.le) (hd e₁ h₁)) (hd e₂ h₂)
  nlinarith

/-- Order of curves is unchanged by the deformation (baseline comparison theorem). -/
theorem deform_order (p : ℝ) {β : ℝ} (hβ : 0 < β) (ε θ ψ : ℝ → ℝ) (ℓ : ℝ) :
    energy ε θ ℓ ≤ energy ε ψ ℓ ↔
      deform p β (energy ε θ ℓ) ≤ deform p β (energy ε ψ ℓ) := by
  rw [energy_le_iff_powerLog_exponentialWeight_le p hβ ε θ ψ ℓ]
  unfold deform exponentialWeight
  rw [div_le_div_iff_of_pos_right hβ, neg_le_neg_iff]

/-- `p → 0` recovers the additive energy (baseline limit). -/
theorem deform_tendsto {β : ℝ} (hβ : β ≠ 0) (ε θ : ℝ → ℝ) (ℓ : ℝ) :
    Tendsto (fun p => deform p β (energy ε θ ℓ)) (𝓝 0) (𝓝 (energy ε θ ℓ)) := by
  have h := (tendsto_powerLog_exponentialWeight_zero β ε θ ℓ).neg.div_const β
  unfold deform
  convert h using 2
  field_simp

end RoundTrip12
