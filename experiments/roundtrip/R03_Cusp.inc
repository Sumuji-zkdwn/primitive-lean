/-!
# Round trip 3: concave envelope of the quartic design → cusp catastrophe → design

Input: round 2 (minimum value of an observation pencil) applied to the baseline design
energy `LinearInputDesign.E`, which is itself such a pencil with observable `x`.
Translation: `f = λx⁴/4 + r x²/2 - u x` is the cusp normal form. Equilibria form the
surface `u = input λ r a`; local minima need `3λa² + r ≥ 0`; the baseline global
certificate is `λa² + r ≥ 0`. The gap between the two is a metastable band, the
margin-zero locus is the Maxwell set `u = 0`, and the folds give the discriminant.
-/

noncomputable section
namespace RoundTrip03
open LinearInputDesign LinearInputObservation

/-- The design energy is an observation pencil on the plane with observable `x`. -/
theorem design_is_pencil (lam r u x y : ℝ) :
    E lam r u x y =
      energy (fun z : ℝ × ℝ => E lam r 0 z.1 z.2) (fun z => z.1) u (x, y) := by
  simp [E, f, energy]
  ring

/-- Every input of the pencil lies on the equilibrium surface: `u = a·margin`. -/
theorem input_eq_mul_margin (lam r a : ℝ) : input lam r a = a * (lam * a ^ 2 + r) := by
  unfold input
  ring

/-- Maxwell set: a zero margin forces the zero input. -/
theorem maxwell_input_zero {lam r a : ℝ} (h : lam * a ^ 2 + r = 0) : input lam r a = 0 := by
  rw [input_eq_mul_margin, h, mul_zero]

/-- On the Maxwell set the two reflected targets are both global minimizers. -/
theorem maxwell_two_global_minimizers {lam r a : ℝ} (hlam : 0 < lam)
    (h : lam * a ^ 2 + r = 0) :
    GlobalMin lam r a ∧ GlobalMin lam r (-a) ∧ input lam r (-a) = input lam r a := by
  refine ⟨(globalMin_iff_margin hlam).2 (by rw [h]),
    (globalMin_iff_margin hlam).2 (by nlinarith), ?_⟩
  have : lam * (-a) ^ 2 + r = 0 := by nlinarith
  rw [input_eq_mul_margin, input_eq_mul_margin, this, h]
  ring

/-- Metastable band: strict local quadratic stability without the global certificate.
Here `a` is a local minimizer of the scalar potential, yet not a global one. -/
theorem metastable_local_not_global {lam r a : ℝ} (hlam : 0 < lam)
    (hloc : 0 < 3 * lam * a ^ 2 + r) (hglob : lam * a ^ 2 + r < 0) :
    IsLocalMin (f lam r (input lam r a)) a ∧ ¬ GlobalMin lam r a := by
  refine ⟨?_, fun hg => by linarith [(globalMin_iff_margin hlam).1 hg]⟩
  have hc : Continuous (fun x : ℝ => lam / 4 * (x + a) ^ 2 + (lam * a ^ 2 + r) / 2) := by
    fun_prop
  have hpos : 0 < lam / 4 * (a + a) ^ 2 + (lam * a ^ 2 + r) / 2 := by nlinarith
  have hev := hc.continuousAt.eventually (lt_mem_nhds hpos)
  filter_upwards [hev] with x hx
  have hg := scalar_gap lam r a x
  have : 0 ≤ (x - a) ^ 2 * (lam / 4 * (x + a) ^ 2 + (lam * a ^ 2 + r) / 2) :=
    mul_nonneg (sq_nonneg _) hx.le
  linarith

/-- Folds: a double root of the stationary cubic lies on the discriminant curve. -/
theorem fold_discriminant {lam r a : ℝ} (hfold : 3 * lam * a ^ 2 + r = 0) :
    4 * r ^ 3 + 27 * lam * (input lam r a) ^ 2 = 0 := by
  have hr : r = -3 * lam * a ^ 2 := by linarith
  subst hr
  unfold input
  ring

/-- Conversely, off the cusp point every discriminant point is a fold. -/
theorem discriminant_fold {lam r u : ℝ} (hr : r ≠ 0)
    (hdisc : 4 * r ^ 3 + 27 * lam * u ^ 2 = 0) :
    ∃ a : ℝ, input lam r a = u ∧ 3 * lam * a ^ 2 + r = 0 := by
  refine ⟨3 * u / (2 * r), ?_, ?_⟩
  · have h2 : lam * (3 * u / (2 * r)) ^ 2 = -r / 3 := by
      field_simp
      nlinarith
    unfold input
    have : lam * (3 * u / (2 * r)) ^ 3 = (3 * u / (2 * r)) * (-r / 3) := by
      rw [← h2]; ring
    rw [this]
    field_simp
    ring
  · field_simp
    nlinarith

/-- Trigonometric section of the equilibrium surface at `(λ, r) = (4, -3)`:
the input map is the Chebyshev polynomial `T₃`. (Chebyshev structures appear in later
supplements of the repository; this identity is derived here from the baseline `input`.) -/
theorem input_chebyshev (φ : ℝ) : input 4 (-3) (Real.cos φ) = Real.cos (3 * φ) := by
  unfold input
  rw [Real.cos_three_mul]
  ring

/-- At `(4, -3)` the folds sit at `a = ±1/2` with critical inputs `∓1`, and the global
certificate holds exactly for `a² ≥ 3/4`. -/
theorem chebyshev_folds_and_margin (a : ℝ) :
    (3 * 4 * a ^ 2 + (-3) = 0 ↔ a = 1 / 2 ∨ a = -1 / 2) ∧
      input 4 (-3) (1 / 2) = -1 ∧ input 4 (-3) (-1 / 2) = 1 ∧
      (GlobalMin 4 (-3) a ↔ 3 / 4 ≤ a ^ 2) := by
  refine ⟨⟨fun h => ?_, ?_⟩, by norm_num [input], by norm_num [input], ?_⟩
  · have : (a - 1 / 2) * (a + 1 / 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
  · rw [globalMin_iff_margin (by norm_num : (0 : ℝ) < 4)]
    constructor <;> intro h <;> linarith

end RoundTrip03
