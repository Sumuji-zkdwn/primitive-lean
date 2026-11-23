/-!
Constant-curvature area-constrained local minima meet the ternary Chebyshev
fibers.  Actual local minimality supplies one pressure `p` and tension `σ`
through the existing main result; constant curvature removes `κ''`, so the
curvature is a real root of the stationary cubic of the same quartic phase
energy.  For `σ > 0` the existing Chebyshev normalization identifies these
roots with real inverse images of `T(y) = 4y³ - 3y`, and the existing exact
fiber counts give the number of roots.  The multipliers of an arc need not be
unique; every count below is for one fixed multiplier pair.  No minimizing
curve is constructed beyond the existing unit circle.
-/

noncomputable section
open Real Set

namespace LinearInputArcChebyshev

open LinearInputDesign LinearInputBranchForgetting

/-- Constant curvatures compatible with one fixed pair of multipliers: the curvature
equation `k κ'' + k κ³ / 2 - σ κ = p` with `κ'' = 0`. -/
def arcCubicSet (k σ p : ℝ) : Set ℝ := {K : ℝ | k * K ^ 3 / 2 - σ * K = p}

/-- The positive scale that turns the stationary cubic into `T(y) = 4y³ - 3y`. -/
def chebyshevScale (k σ : ℝ) : ℝ := sqrt (8 * σ / (3 * k))

/-- The Chebyshev level of the pressure after that normalization. -/
def chebyshevLevel (k σ p : ℝ) : ℝ := 8 * p / (k * chebyshevScale k σ ^ 3)

theorem chebyshevScale_pos {k σ : ℝ} (hk : 0 < k) (hσ : 0 < σ) :
    0 < chebyshevScale k σ :=
  sqrt_pos.mpr (by positivity)

theorem chebyshevScale_sq {k σ : ℝ} (hk : 0 < k) (hσ : 0 < σ) :
    chebyshevScale k σ ^ 2 = 8 * σ / (3 * k) :=
  sq_sqrt (by positivity)

/-- The constant-curvature cubic is the stationary-input equation of the quartic
design family at the phase parameters `λ = 1/2`, `r = -σ/k`, `u = p/k`. -/
theorem mem_arcCubicSet_iff_input {k σ p K : ℝ} (hk : 0 < k) :
    K ∈ arcCubicSet k σ p ↔ input (1 / 2) (-σ / k) K = p / k := by
  simp only [arcCubicSet, mem_ofPred_eq, input]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/-- Actual area-constrained local minimality with constant curvature `K` forces
`K` to solve the stationary cubic with the same pressure and tension that the
main result attaches to the curve. -/
theorem locallyMinimizing_constant_curvature_cubic {θ : ℝ → ℝ} {k ℓ K : ℝ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hmin : LinearInputAreaMinimum.LocallyMinimizing k θ ℓ)
    (hK : ∀ s ∈ Ioo 0 ℓ, deriv θ s = K) :
    ∃ p σ : ℝ, LinearInputPressureStationary.Stationary k p θ ℓ ∧
      K ∈ arcCubicSet k σ p ∧ input (1 / 2) (-σ / k) K = p / k := by
  obtain ⟨p, σ, _c, hp, hchain⟩ :=
    LinearInputMainResult.locallyMinimizing_pressure_curvature_phase hℓ hk hθ hmin
  have h2 : ∀ s ∈ Ioo 0 ℓ, deriv (deriv θ) s = 0 := by
    intro s hs
    have he : deriv θ =ᶠ[nhds s] fun _ => K :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs) (fun t ht => hK t ht)
    rw [he.deriv_eq, deriv_const]
  have h3 : ∀ s ∈ Ioo 0 ℓ, deriv (deriv (deriv θ)) s = 0 := by
    intro s hs
    have he : deriv (deriv θ) =ᶠ[nhds s] fun _ => (0 : ℝ) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs) (fun t ht => h2 t ht)
    rw [he.deriv_eq, deriv_const]
  have hs₀ : ℓ / 2 ∈ Ioo 0 ℓ := ⟨by linarith, by linarith⟩
  have hcubic : K ∈ arcCubicSet k σ p := by
    have h := (hchain (ℓ / 2) hs₀).1
    rw [h3 _ hs₀, hK _ hs₀] at h
    show k * K ^ 3 / 2 - σ * K = p
    linarith
  exact ⟨p, σ, hp, hcubic, (mem_arcCubicSet_iff_input hk).mp hcubic⟩

/-- For positive tension, the existing Chebyshev normalization identifies the
constant-curvature cubic with the Chebyshev equation `T(K / s) = c`. -/
theorem mem_arcCubicSet_iff_chebyshev {k σ p K : ℝ} (hk : 0 < k) (hσ : 0 < σ) :
    K ∈ arcCubicSet k σ p ↔
      chebyshevThree (K / chebyshevScale k σ) = chebyshevLevel k σ p := by
  have hs := chebyshevScale_pos hk hσ
  have hs2 := chebyshevScale_sq hk hσ
  set s := chebyshevScale k σ with hsdef
  have hr : -3 * (1 / 2 : ℝ) * s ^ 2 / 4 = -σ / k := by
    rw [hs2]
    field_simp
    ring
  have hnorm := input_normalization (1 / 2) s (K / s)
  rw [hr, mul_div_cancel₀ K hs.ne'] at hnorm
  rw [mem_arcCubicSet_iff_input hk, hnorm, chebyshevLevel, ← hsdef]
  have hs3 : 0 < s ^ 3 := by positivity
  constructor
  · intro h
    field_simp
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- The constant-curvature roots are the scaled real inverse images of the
first ternary iterate. -/
theorem arcCubicSet_eq_image {k σ p : ℝ} (hk : 0 < k) (hσ : 0 < σ) :
    arcCubicSet k σ p =
      (fun y => chebyshevScale k σ * y) ''
        {y : ℝ | ternaryIterate 1 y = chebyshevLevel k σ p} := by
  have hs := chebyshevScale_pos hk hσ
  ext K
  constructor
  · intro hK
    refine ⟨K / chebyshevScale k σ, ?_, mul_div_cancel₀ K hs.ne'⟩
    show ternaryIterate 1 (K / chebyshevScale k σ) = chebyshevLevel k σ p
    simpa [ternaryIterate] using (mem_arcCubicSet_iff_chebyshev hk hσ).mp hK
  · rintro ⟨y, hy, rfl⟩
    apply (mem_arcCubicSet_iff_chebyshev hk hσ).mpr
    rw [mul_div_cancel_left₀ y hs.ne']
    simpa [ternaryIterate] using hy

/-- The square of the Chebyshev level is the classical cubic discriminant ratio. -/
theorem chebyshevLevel_sq {k σ p : ℝ} (hk : 0 < k) (hσ : 0 < σ) :
    chebyshevLevel k σ p ^ 2 = 27 * k * p ^ 2 / (8 * σ ^ 3) := by
  have hs := chebyshevScale_pos hk hσ
  have hs2 := chebyshevScale_sq hk hσ
  have h6 : chebyshevScale k σ ^ 6 = (8 * σ / (3 * k)) ^ 3 := by
    rw [← hs2]
    ring
  have hl : chebyshevLevel k σ p ^ 2 = 64 * p ^ 2 / (k ^ 2 * chebyshevScale k σ ^ 6) := by
    unfold chebyshevLevel
    field_simp
    ring
  rw [hl, h6]
  field_simp
  ring

theorem chebyshevLevel_abs_lt_one {k σ p : ℝ} (hk : 0 < k) (hσ : 0 < σ)
    (hdisc : 27 * k * p ^ 2 < 8 * σ ^ 3) :
    -1 < chebyshevLevel k σ p ∧ chebyshevLevel k σ p < 1 := by
  have hσ3 : 0 < 8 * σ ^ 3 := by positivity
  have hsq : chebyshevLevel k σ p ^ 2 < 1 := by
    rw [chebyshevLevel_sq hk hσ, div_lt_one hσ3]
    exact hdisc
  exact abs_lt.mp (sq_lt_one_iff_abs_lt_one _ |>.mp hsq)

theorem chebyshevLevel_sq_eq_one {k σ p : ℝ} (hk : 0 < k) (hσ : 0 < σ)
    (hdisc : 27 * k * p ^ 2 = 8 * σ ^ 3) :
    chebyshevLevel k σ p = 1 ∨ chebyshevLevel k σ p = -1 := by
  have hσ3 : 0 < 8 * σ ^ 3 := by positivity
  have hsq : chebyshevLevel k σ p ^ 2 = 1 := by
    rw [chebyshevLevel_sq hk hσ, hdisc, div_self hσ3.ne']
  have hf : (chebyshevLevel k σ p - 1) * (chebyshevLevel k σ p + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Inside the discriminant region exactly three constant curvatures are compatible
with the fixed multipliers; the count is the existing `n = 1` regular fiber count. -/
theorem arcCubicSet_ncard_three {k σ p : ℝ} (hk : 0 < k) (hσ : 0 < σ)
    (hdisc : 27 * k * p ^ 2 < 8 * σ ^ 3) :
    (arcCubicSet k σ p).ncard = 3 := by
  have hs := chebyshevScale_pos hk hσ
  obtain ⟨h0, h1⟩ := chebyshevLevel_abs_lt_one hk hσ hdisc
  rw [arcCubicSet_eq_image hk hσ,
    Set.ncard_image_of_injective _ (mul_right_injective₀ hs.ne'),
    LinearInputBranchFibers.real_inverse_card_regular 1 h0 h1]
  norm_num

/-- On the discriminant boundary exactly two constant curvatures remain; the count
is the existing critical fiber count `(3 + 1) / 2`. -/
theorem arcCubicSet_ncard_two {k σ p : ℝ} (hk : 0 < k) (hσ : 0 < σ)
    (hdisc : 27 * k * p ^ 2 = 8 * σ ^ 3) :
    (arcCubicSet k σ p).ncard = 2 := by
  have hs := chebyshevScale_pos hk hσ
  rw [arcCubicSet_eq_image hk hσ,
    Set.ncard_image_of_injective _ (mul_right_injective₀ hs.ne')]
  rcases chebyshevLevel_sq_eq_one hk hσ hdisc with h | h
  · rw [h, LinearInputBranchFibers.real_inverse_card_one 1]
    norm_num
  · rw [h, LinearInputBranchFibers.real_inverse_card_neg_one 1]
    norm_num

/-- Composition: an actual constant-curvature area-constrained local minimum has
multipliers `p, σ` from the main result, its curvature is a normalized Chebyshev
inverse image when `σ > 0`, and it lies in a set of exactly three (inside the
discriminant region) or two (on its boundary) compatible constant curvatures. -/
theorem locallyMinimizing_arc_chebyshev_fiber {θ : ℝ → ℝ} {k ℓ K : ℝ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hmin : LinearInputAreaMinimum.LocallyMinimizing k θ ℓ)
    (hK : ∀ s ∈ Ioo 0 ℓ, deriv θ s = K) :
    ∃ p σ : ℝ, LinearInputPressureStationary.Stationary k p θ ℓ ∧
      K ∈ arcCubicSet k σ p ∧
      (0 < σ → chebyshevThree (K / chebyshevScale k σ) = chebyshevLevel k σ p) ∧
      (0 < σ → 27 * k * p ^ 2 < 8 * σ ^ 3 → (arcCubicSet k σ p).ncard = 3) ∧
      (0 < σ → 27 * k * p ^ 2 = 8 * σ ^ 3 → (arcCubicSet k σ p).ncard = 2) := by
  obtain ⟨p, σ, hp, hcubic, -⟩ :=
    locallyMinimizing_constant_curvature_cubic hℓ hk hθ hmin hK
  exact ⟨p, σ, hp, hcubic,
    fun hσ => (mem_arcCubicSet_iff_chebyshev hk hσ).mp hcubic,
    fun hσ hd => arcCubicSet_ncard_three hk hσ hd,
    fun hσ hd => arcCubicSet_ncard_two hk hσ hd⟩

/-- The existing unit circle with zero pressure: its multiplier pair `p = 0`,
`σ = 1/2` is allowed by the actual first variation, and the compatible constant
curvatures are exactly the straight line and the two unit circles. -/
theorem circle_zero_pressure_fiber {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    LinearInputPressureStationary.Stationary 1 0 (fun s => s) ℓ ∧
      arcCubicSet 1 (1 / 2) 0 = {-1, 0, 1} ∧
      (arcCubicSet 1 (1 / 2) 0).ncard = 3 := by
  refine ⟨LinearInputMainResult.circle_pressure_stationary hℓ 0, ?_,
    arcCubicSet_ncard_three (by norm_num) (by norm_num) (by norm_num)⟩
  ext K
  simp only [arcCubicSet, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    have hf : K * (K + 1) * (K - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hf with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact Or.inr (Or.inl h'')
      · exact Or.inl (by linarith)
    · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

end LinearInputArcChebyshev
