import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Comparison with the independent GPT-side probe

The GPT-side script (`gpt/primitive_465_roundtrip_experiment.py`) integrates
`z' = -γ (E - target) ∇E + b J ∇E`, `J (gx, gy) = (-gy, gx)`, observes
`p = 1 / (1 + exp (β e))` with `e = E - target`, and its binary entropy `H`.
It states `e' = -γ e |∇E|²`, `p' = βγ e |∇E|² p (1 - p)`, `H' = β²γ e² |∇E|² p (1 - p) ≥ 0`
and reports that the H′ formula was not proved in Lean. This file proves those formulas
from the initial baseline only, and proves the exact identities that connect (or fail to
connect) the probe with rounds R01–R13. Nothing in R01–R13 is changed.
-/

noncomputable section
namespace RoundTripCompare
open Real Set LinearInputDesign LinearInputGradient

/-! ## A. The GPT formulas, proved from the baseline -/

/-- GPT's energy-gap identity is the baseline `hasDerivAt_energy_of_velocity` at fixed input. -/
theorem gpt_energy_gap_derivative {x y : ℝ → ℝ} {t : ℝ} (lam r u gamma target b : ℝ)
    (hx : HasDerivAt x (-gamma * (E lam r u (x t) (y t) - target) * gx lam r u (x t) (y t)
      - b * gy (x t) (y t)) t)
    (hy : HasDerivAt y (-gamma * (E lam r u (x t) (y t) - target) * gy (x t) (y t)
      + b * gx lam r u (x t) (y t)) t) :
    HasDerivAt (fun s => E lam r u (x s) (y s) - target)
      (-gamma * (E lam r u (x t) (y t) - target) * gSq lam r u (x t) (y t)) t := by
  have h := hasDerivAt_energy_of_velocity (u := fun _ => u) (u' := 0) lam r gamma target b
    hx hy (hasDerivAt_const t u)
  simpa using h.sub_const target

/-- GPT's normalized observer. -/
def logistic (β e : ℝ) : ℝ := 1 / (1 + exp (β * e))

/-- Binary entropy. -/
def binEntropy (p : ℝ) : ℝ := -(p * log p + (1 - p) * log (1 - p))

theorem logistic_pos (β e : ℝ) : 0 < logistic β e := by unfold logistic; positivity

theorem logistic_lt_one (β e : ℝ) : logistic β e < 1 := by
  unfold logistic
  rw [div_lt_one (by positivity)]
  linarith [exp_pos (β * e)]

theorem one_sub_logistic (β e : ℝ) : 1 - logistic β e = logistic β (-e) := by
  unfold logistic
  rw [show β * -e = -(β * e) by ring, exp_neg]
  have := exp_pos (β * e)
  field_simp
  ring

theorem hasDerivAt_logistic (β e : ℝ) :
    HasDerivAt (logistic β) (-β * logistic β e * (1 - logistic β e)) e := by
  have hl : HasDerivAt (fun t => β * t) β e := (hasDerivAt_id e).const_mul β |>.congr_deriv (by simp)
  have h := (hasDerivAt_const e (1 : ℝ)).div (((hasDerivAt_exp _).comp e hl).const_add 1)
    (by positivity : (1 + exp (β * e)) ≠ 0)
  unfold logistic
  convert h using 1
  have := exp_pos (β * e)
  simp only [Function.comp]
  field_simp
  ring

/-- Closed form of the observer's entropy. -/
theorem entropy_logistic (β e : ℝ) :
    binEntropy (logistic β e) = β * e * logistic β e + log (1 + exp (-(β * e))) := by
  have ha := exp_pos (β * e)
  have h1 : 1 - logistic β e = exp (β * e) / (1 + exp (β * e)) := by
    unfold logistic; field_simp; ring
  have hlog1 : log (logistic β e) = -log (1 + exp (β * e)) := by
    unfold logistic; rw [one_div, log_inv]
  have hlog2 : log (1 - logistic β e) = β * e - log (1 + exp (β * e)) := by
    rw [h1, log_div ha.ne' (by positivity), log_exp]
  have hlog3 : log (1 + exp (-(β * e))) = log (1 + exp (β * e)) - β * e := by
    rw [exp_neg, show 1 + (exp (β * e))⁻¹ = (1 + exp (β * e)) / exp (β * e) by field_simp; ring,
      log_div (by positivity) ha.ne', log_exp]
  unfold binEntropy
  rw [hlog1, hlog2, hlog3]
  ring

/-- The observer's entropy as a function of the energy gap has derivative `-β² e p (1-p)`. -/
theorem hasDerivAt_entropy_logistic (β e : ℝ) :
    HasDerivAt (fun e => binEntropy (logistic β e))
      (-β ^ 2 * e * logistic β e * (1 - logistic β e)) e := by
  have hfun : (fun e => binEntropy (logistic β e)) =
      fun e => β * e * logistic β e + log (1 + exp (-(β * e))) := funext (entropy_logistic β)
  rw [hfun]
  have hl : HasDerivAt (fun t => -(β * t)) (-β) e := by
    simpa using ((hasDerivAt_id e).const_mul β).neg
  have hq : HasDerivAt (fun t => 1 + exp (-(β * t))) (exp (-(β * e)) * -β) e :=
    ((hasDerivAt_exp _).comp e hl).const_add 1
  have hlog := hq.log (by positivity)
  have hprod := (((hasDerivAt_id e).const_mul β).mul (hasDerivAt_logistic β e))
  convert hprod.add hlog using 1
  have hp : exp (-(β * e)) / (1 + exp (-(β * e))) = logistic β e := by
    unfold logistic
    rw [exp_neg]
    have := exp_pos (β * e)
    field_simp
    ring
  have : exp (-(β * e)) * -β / (1 + exp (-(β * e))) = -β * logistic β e := by
    rw [← hp]; ring
  rw [this]
  simp
  ring

/-- GPT's `H′` formula and its sign, now a Lean theorem. -/
theorem gpt_entropy_derivative {x y : ℝ → ℝ} {t : ℝ} (lam r u gamma target b β : ℝ)
    (hx : HasDerivAt x (-gamma * (E lam r u (x t) (y t) - target) * gx lam r u (x t) (y t)
      - b * gy (x t) (y t)) t)
    (hy : HasDerivAt y (-gamma * (E lam r u (x t) (y t) - target) * gy (x t) (y t)
      + b * gx lam r u (x t) (y t)) t) :
    HasDerivAt (fun s => binEntropy (logistic β (E lam r u (x s) (y s) - target)))
      (β ^ 2 * gamma * (E lam r u (x t) (y t) - target) ^ 2 * gSq lam r u (x t) (y t) *
        logistic β (E lam r u (x t) (y t) - target) *
        (1 - logistic β (E lam r u (x t) (y t) - target))) t := by
  have h := (hasDerivAt_entropy_logistic β _).comp t
    (gpt_energy_gap_derivative lam r u gamma target b hx hy)
  convert h using 1
  ring

theorem gpt_entropy_derivative_nonneg {gamma : ℝ} (hg : 0 ≤ gamma) (β e G : ℝ) (hG : 0 ≤ G) :
    0 ≤ β ^ 2 * gamma * e ^ 2 * G * logistic β e * (1 - logistic β e) := by
  have h1 := logistic_pos β e
  have h2 := sub_pos.mpr (logistic_lt_one β e)
  positivity

/-! ## B. Same structure, different representation: entropy is a function of `|e|` -/

theorem entropy_even (β e : ℝ) : binEntropy (logistic β (-e)) = binEntropy (logistic β e) := by
  rw [← one_sub_logistic]
  unfold binEntropy
  ring_nf

theorem entropy_strictAntiOn {β : ℝ} (hβ : β ≠ 0) :
    StrictAntiOn (fun e => binEntropy (logistic β e)) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact (fun e _ => (hasDerivAt_entropy_logistic β e).continuousAt.continuousWithinAt)
  · intro e he
    rw [interior_Ici] at he
    rw [(hasDerivAt_entropy_logistic β e).deriv]
    have h1 := logistic_pos β e
    have h2 := sub_pos.mpr (logistic_lt_one β e)
    have hb : 0 < β ^ 2 := by positivity
    have : 0 < β ^ 2 * e * logistic β e * (1 - logistic β e) := by
      have := he.out; positivity
    linarith

/-- GPT's entropy order is exactly the reversed order of `|e|` (for `β ≠ 0`). Hence
"H increases along the flow" is a reparametrization of the baseline statement that
`e²` decreases (`LinearInputInvariance.squared_error_antitone`). -/
theorem entropy_le_iff_abs {β : ℝ} (hβ : β ≠ 0) (e₁ e₂ : ℝ) :
    binEntropy (logistic β e₁) ≤ binEntropy (logistic β e₂) ↔ |e₂| ≤ |e₁| := by
  have habs : ∀ e, binEntropy (logistic β e) = binEntropy (logistic β |e|) := by
    intro e
    rcases abs_choice e with h | h <;> rw [h]
    rw [entropy_even]
  rw [habs e₁, habs e₂]
  exact (entropy_strictAntiOn hβ).le_iff_ge (mem_Ici.2 (abs_nonneg _)) (mem_Ici.2 (abs_nonneg _))

/-! ## C. Exact link with R05 (two-state Gibbs free energy) -/

theorem logistic_eq_gibbs (β e : ℝ) :
    logistic β e = exp (-β * e) / (exp (-β * e) + exp (-β * 0)) := by
  unfold logistic
  rw [mul_zero, exp_zero, show -β * e = -(β * e) by ring, exp_neg]
  have := exp_pos (β * e)
  field_simp

/-- The observer is the derivative of R05's free energy in the first energy. -/
theorem hasDerivAt_freeEnergy_fst {β : ℝ} (hβ : β ≠ 0) (e : ℝ) :
    HasDerivAt (fun e => RoundTrip05.freeEnergy β e 0) (logistic β e) e := by
  unfold RoundTrip05.freeEnergy
  have hl : HasDerivAt (fun t => -β * t) (-β) e := by
    simpa using (hasDerivAt_id e).const_mul (-β)
  have hq : HasDerivAt (fun t => exp (-β * t) + exp (-β * 0)) (exp (-β * e) * -β) e :=
    ((hasDerivAt_exp _).comp e hl).add_const _
  have h := (hq.log (by positivity)).neg.div_const β
  convert h using 1
  rw [logistic_eq_gibbs]
  field_simp

/-- Thermodynamic identity: entropy = β (mean energy − free energy). -/
theorem entropy_eq_beta_U_minus_F {β : ℝ} (hβ : β ≠ 0) (e : ℝ) :
    binEntropy (logistic β e) = β * (logistic β e * e - RoundTrip05.freeEnergy β e 0) := by
  rw [entropy_logistic]
  unfold RoundTrip05.freeEnergy
  rw [mul_zero, exp_zero, show -β * e = -(β * e) by ring, add_comm (exp _) 1]
  field_simp
  ring

/-- R05's slope `a tanh(βau)` is the mean observable under GPT's logistic observer
evaluated at the energy difference `-2au` of the two Maxwell states. -/
theorem r05_tanh_eq_logistic_mean (β a u : ℝ) :
    a * (2 * logistic β (-2 * a * u) - 1) = a * (sinh (β * a * u) / cosh (β * a * u)) := by
  congr 1
  unfold logistic
  rw [sinh_eq, cosh_eq, show β * (-2 * a * u) = -(β * a * u) - β * a * u by ring, exp_sub, exp_neg]
  have := exp_pos (β * a * u)
  field_simp
  ring

/-! ## D. The independence counterexample, exactly -/

theorem logistic_odds (β e : ℝ) : (1 - logistic β e) / logistic β e = exp (β * e) := by
  unfold logistic
  have := exp_pos (β * e)
  field_simp
  ring

/-- Odds multiply (because the baseline-type weight `exp(-βe)` multiplies). -/
theorem logistic_compose (β e₁ e₂ : ℝ) :
    logistic β (e₁ + e₂) = logistic β e₁ * logistic β e₂ /
      (logistic β e₁ * logistic β e₂ + (1 - logistic β e₁) * (1 - logistic β e₂)) := by
  unfold logistic
  rw [mul_add, exp_add]
  have key : ∀ a b : ℝ, 0 < a → 0 < b → 1 / (1 + a * b) =
      1 / (1 + a) * (1 / (1 + b)) /
        (1 / (1 + a) * (1 / (1 + b)) + (1 - 1 / (1 + a)) * (1 - 1 / (1 + b))) := by
    intro a b ha hb
    have h1 : 1 - 1 / (1 + a) = a / (1 + a) := by field_simp; ring
    have h2 : 1 - 1 / (1 + b) = b / (1 + b) := by field_simp; ring
    rw [h1, h2, div_mul_div_comm, div_mul_div_comm, one_mul, ← add_div,
      div_div_div_cancel_right₀ (by positivity)]
  exact key _ _ (exp_pos _) (exp_pos _)

/-- GPT's numerical counterexample holds for every pair: the product is always smaller. -/
theorem logistic_mul_lt (β e₁ e₂ : ℝ) :
    logistic β e₁ * logistic β e₂ < logistic β (e₁ + e₂) := by
  unfold logistic
  rw [mul_add, exp_add]
  have h1 := exp_pos (β * e₁)
  have h2 := exp_pos (β * e₂)
  rw [div_mul_div_comm, one_mul, div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
  nlinarith

/-- In the coordinate `ρ = (1 - 2p)/p` the logistic composition is R11's law `⊕₁`. -/
theorem logistic_fgl (β e₁ e₂ : ℝ) :
    (1 - 2 * logistic β (e₁ + e₂)) / logistic β (e₁ + e₂) =
      RoundTrip11.fgl 1 ((1 - 2 * logistic β e₁) / logistic β e₁)
        ((1 - 2 * logistic β e₂) / logistic β e₂) := by
  have key : ∀ e, (1 - 2 * logistic β e) / logistic β e = exp (β * e) - 1 := by
    intro e
    rw [show 1 - 2 * logistic β e = (1 - logistic β e) - logistic β e by ring, sub_div,
      logistic_odds, div_self (logistic_pos β e).ne']
  rw [key, key, key, mul_add, exp_add]
  unfold RoundTrip11.fgl
  ring

/-! ## E. The circulation term is the baseline curvature phase flow -/

/-- With `γ = 0`, `b = -1`, `λ = 1/2`, `r = -σ/k`, GPT's vector field is exactly the
baseline curvature phase velocity of `CurvatureBridge`. -/
theorem circulation_is_curvature_flow {k σ u target s : ℝ} {κ : ℝ → ℝ}
    (hk : k ≠ 0) (hκ : ContDiff ℝ 2 κ)
    (heq : k * deriv (deriv κ) s + k * (κ s) ^ 3 / 2 - σ * κ s = k * u) :
    HasDerivAt κ (-0 * (E (1 / 2) (-σ / k) u (κ s) (deriv κ s + Real.sqrt 2 * κ s) - target) *
        gx (1 / 2) (-σ / k) u (κ s) (deriv κ s + Real.sqrt 2 * κ s)
        - (-1) * gy (κ s) (deriv κ s + Real.sqrt 2 * κ s)) s ∧
    HasDerivAt (fun t => deriv κ t + Real.sqrt 2 * κ t)
      (-0 * (E (1 / 2) (-σ / k) u (κ s) (deriv κ s + Real.sqrt 2 * κ s) - target) *
        gy (κ s) (deriv κ s + Real.sqrt 2 * κ s)
        + (-1) * gx (1 / 2) (-σ / k) u (κ s) (deriv κ s + Real.sqrt 2 * κ s)) s := by
  obtain ⟨h1, h2⟩ := LinearInputCurvatureBridge.forced_phase_hasDerivAt hk hκ heq
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- Hence R07's soliton is a (non-dissipative) baseline trajectory of the GPT family. -/
theorem soliton_isTrajectory (c target : ℝ) :
    LinearInputRegularBand.IsTrajectory (1 / 2) (-(1 * c ^ 2) / 1) 0 0 target
      (RoundTrip07.soliton c)
      (fun t => deriv (RoundTrip07.soliton c) t + Real.sqrt 2 * RoundTrip07.soliton c t)
      (fun _ => -1) := by
  intro s _
  have := circulation_is_curvature_flow (u := 0) (target := target) one_ne_zero
    (RoundTrip07.contDiff_soliton c)
    (by simpa using RoundTrip07.soliton_curvature_equation 1 c s)
  simpa using this

/-! ## F. Regime: the GPT parameters exclude R04's corner mechanism -/

/-- For `λ > 0`, `r > 0` the design energy has a unique global minimizer for every `u`,
so R04's hypothesis (two minimizers with different `x`) is never met. -/
theorem unique_minimizer_of_r_pos {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (u : ℝ) :
    ∃! z : ℝ × ℝ, ∀ w : ℝ × ℝ, E lam r u z.1 z.2 ≤ E lam r u w.1 w.2 := by
  by_cases hu : u = 0
  · subst hu
    have hE : ∀ x y : ℝ, E lam r 0 x y =
        lam * x ^ 4 / 4 + r * x ^ 2 / 2 + (y - Real.sqrt 2 * x) ^ 2 / 2 := by
      intro x y; simp only [E, f]; ring
    refine ⟨(0, 0), fun w => ?_, fun z hz => ?_⟩
    · rw [hE, hE]
      have : 0 ≤ lam * w.1 ^ 4 / 4 + r * w.1 ^ 2 / 2 + (w.2 - Real.sqrt 2 * w.1) ^ 2 / 2 := by
        positivity
      simpa using this
    · have h := hz (0, 0)
      rw [hE, hE] at h
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
        sub_self, add_zero] at h
      have t1 : 0 ≤ lam * z.1 ^ 4 / 4 := by positivity
      have t2 : 0 ≤ (z.2 - Real.sqrt 2 * z.1) ^ 2 / 2 := by positivity
      have t3 : 0 ≤ r * z.1 ^ 2 / 2 := by positivity
      have hx2 : r * z.1 ^ 2 = 0 := by linarith
      have hx : z.1 = 0 := by
        have := (mul_eq_zero.mp hx2).resolve_left hr.ne'
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have hy2 : (z.2 - Real.sqrt 2 * z.1) ^ 2 = 0 := by linarith
      have hy : z.2 = 0 := by
        rw [hx, mul_zero, sub_zero] at hy2
        exact pow_eq_zero_iff (by norm_num) |>.mp hy2
      exact Prod.ext hx hy
  · exact LinearInputRegularBand.exists_unique_global_minimum_of_input_ne_zero hlam hu

/-! ## G. Scaling conjugacy: GPT's `λ = 1` orbits are `λ = 1/2` orbits -/

theorem E_scale {α : ℝ} (hα : α ≠ 0) (lam r u x y : ℝ) :
    E lam r u (α * x) (α * y) = α ^ 2 * E (lam * α ^ 2) r (u / α) x y := by
  unfold E f
  field_simp

theorem gx_scale {α : ℝ} (hα : α ≠ 0) (lam r u x y : ℝ) :
    gx lam r u x y = α * gx (lam * α ^ 2) r (u / α) (x / α) (y / α) := by
  unfold gx
  field_simp

theorem gy_scale {α : ℝ} (hα : α ≠ 0) (x y : ℝ) : gy x y = α * gy (x / α) (y / α) := by
  unfold gy
  field_simp

/-- A non-dissipative (`γ = 0`) trajectory for `(λ, r, u, b)` divided by `α` is a
trajectory for `(λα², r, u/α, b)` with the same time. -/
theorem circulation_scale {x y : ℝ → ℝ} {t α : ℝ} (hα : α ≠ 0) (lam r u b : ℝ)
    (hx : HasDerivAt x (-b * gy (x t) (y t)) t)
    (hy : HasDerivAt y (b * gx lam r u (x t) (y t)) t) :
    HasDerivAt (fun s => x s / α) (-b * gy (x t / α) (y t / α)) t ∧
      HasDerivAt (fun s => y s / α)
        (b * gx (lam * α ^ 2) r (u / α) (x t / α) (y t / α)) t := by
  constructor
  · convert hx.div_const α using 1
    rw [gy_scale hα (x t) (y t)]
    field_simp
  · convert hy.div_const α using 1
    rw [gx_scale hα lam r u (x t) (y t)]
    field_simp

end RoundTripCompare
