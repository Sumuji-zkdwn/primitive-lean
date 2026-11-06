/-!
# Round trip 11: power-law energy scaling → multiplicative formal group law → powerLog

Input: round 10 (energy of a rescaled curve is multiplied by a power of the scale; the
baseline `energy_scaling_of_homogeneous` gives `a^(1-m)` for an `m`-homogeneous density).
Translation (algebra): composing scalings multiplies factors; the relative change
`ρ(a) = a^p - 1` (`p = 1 - m`) obeys `ρ(ab) = ρ(a) + ρ(b) + ρ(a)ρ(b)`, and the baseline
`powerLog p` turns multiplication into the multiplicative formal group law
`x ⊕ₚ y = x + y + p x y`. Back-translation: the relative energy change under composed
scalings is governed by `⊕ₚ`; for the quadratic elastica (`m = 2`, `p = -1`) the energy-loss
fraction `1 - 1/a = powerLog (-1) a` composes like the probability of a union of
independent events.
-/

noncomputable section
namespace RoundTrip11
open Real Elastica

/-- The multiplicative formal group law with parameter `p`. -/
def fgl (p x y : ℝ) : ℝ := x + y + p * x * y

theorem fgl_comm (p x y : ℝ) : fgl p x y = fgl p y x := by unfold fgl; ring
theorem fgl_assoc (p x y z : ℝ) : fgl p (fgl p x y) z = fgl p x (fgl p y z) := by
  unfold fgl; ring
theorem fgl_zero (p x : ℝ) : fgl p x 0 = x := by unfold fgl; ring

/-- Inverse elements exist off the singular value `1 + p x = 0`. -/
theorem fgl_inv {p x : ℝ} (hx : 1 + p * x ≠ 0) : fgl p x (-x / (1 + p * x)) = 0 := by
  unfold fgl
  have hx' : 1 + x * p ≠ 0 := by rwa [mul_comm x p]
  field_simp
  ring

/-- Linearization: `x ↦ 1 + p x` conjugates `⊕ₚ` to multiplication. -/
theorem one_add_mul_fgl (p x y : ℝ) : 1 + p * fgl p x y = (1 + p * x) * (1 + p * y) := by
  unfold fgl; ring

/-- At `p = 0` the law is ordinary addition (the additive formal group of `log`). -/
theorem fgl_zero_param (x y : ℝ) : fgl 0 x y = x + y := by unfold fgl; ring

/-- Baseline `powerLog_mul` is a homomorphism `(ℝ_{>0}, ·) → (ℝ, ⊕ₚ)`. -/
theorem powerLog_hom (p : ℝ) {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    powerLog p (z * w) = fgl p (powerLog p z) (powerLog p w) := by
  rw [powerLog_mul p hz hw]; unfold fgl; ring

/-- The power is recovered from `powerLog` (all `p`, including `p = 0`). -/
theorem rpow_eq_one_add_powerLog (p z : ℝ) :
    z ^ p = 1 + p * powerLog p z := by
  by_cases hp : p = 0
  · subst hp; simp
  · unfold powerLog
    rw [if_neg hp]
    field_simp
    ring

/-- Relative energy change under one scaling (baseline homogeneous scaling law). -/
theorem energy_relative_change {ε θ : ℝ → ℝ} (hθ : Differentiable ℝ θ) {a m : ℝ} (ha : 0 < a)
    (hε : ∀ t : ℝ, 0 < t → ∀ q : ℝ, ε (t * q) = t ^ m * ε q) (ℓ : ℝ) :
    energy ε (fun s => θ (s / a)) (a * ℓ) - energy ε θ ℓ =
      (1 - m) * powerLog (1 - m) a * energy ε θ ℓ := by
  rw [energy_scaling_of_homogeneous hθ ha hε, rpow_eq_one_add_powerLog (1 - m) a]
  ring

/-- Composition of two scalings: relative changes combine by `⊕₁`, and the `powerLog`
values combine by `⊕ₚ` with `p = 1 - m`. -/
theorem energy_composed_scaling {ε θ : ℝ → ℝ} (hθ : Differentiable ℝ θ) {a b m : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hε : ∀ t : ℝ, 0 < t → ∀ q : ℝ, ε (t * q) = t ^ m * ε q) (ℓ : ℝ) :
    energy ε (fun s => θ (s / (a * b))) ((a * b) * ℓ) =
        (1 + (1 - m) * fgl (1 - m) (powerLog (1 - m) a) (powerLog (1 - m) b)) * energy ε θ ℓ ∧
      (a * b) ^ (1 - m) - 1 = fgl 1 (a ^ (1 - m) - 1) (b ^ (1 - m) - 1) := by
  constructor
  · rw [energy_scaling_of_homogeneous hθ (mul_pos ha hb) hε, rpow_eq_one_add_powerLog (1 - m) (a * b),
      powerLog_hom _ ha hb]
  · rw [mul_rpow ha.le hb.le]; unfold fgl; ring

/-- The two-step scaling is the composition of the baseline one-step scalings. -/
theorem scaling_compose (θ : ℝ → ℝ) (a b : ℝ) :
    (fun s => (fun t => θ (t / a)) (s / b)) = fun s => θ (s / (a * b)) := by
  funext s; show θ (s / b / a) = θ (s / (a * b)); rw [div_div, mul_comm b a]

/-- Quadratic elastica: the energy-loss fraction is `powerLog (-1) a = 1 - 1/a`. -/
theorem quadratic_loss_fraction {θ : ℝ → ℝ} (hθ : Differentiable ℝ θ) {a : ℝ} (ha : 0 < a)
    (k ℓ : ℝ) :
    energy (fun q => k * q ^ 2 / 2) θ ℓ - energy (fun q => k * q ^ 2 / 2) (fun s => θ (s / a)) (a * ℓ) =
      powerLog (-1) a * energy (fun q => k * q ^ 2 / 2) θ ℓ ∧ powerLog (-1) a = 1 - 1 / a := by
  have hpl : powerLog (-1) a = 1 - 1 / a := by
    unfold powerLog
    rw [if_neg (by norm_num), rpow_neg_one]
    field_simp
    ring
  refine ⟨?_, hpl⟩
  rw [energy_scaling_quadratic hθ ha, hpl]
  field_simp

/-- Loss fractions compose like `P(A ∪ B) = P(A) + P(B) - P(A)P(B)` (law `⊕₋₁`). -/
theorem loss_fraction_union {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    powerLog (-1) (a * b) = powerLog (-1) a + powerLog (-1) b - powerLog (-1) a * powerLog (-1) b := by
  rw [powerLog_hom _ ha hb]; unfold fgl; ring

end RoundTrip11
