/-! Exact ground energy and its odd-sector equality condition on the first approximant. -/

noncomputable section

namespace LinearInputLaaksoSignedMinimum

open LinearInputLaaksoFiniteGraph LinearInputLaaksoSigned LinearInputLaaksoSignedEnergy
open LinearInputLaaksoSignedGauge

/-- Excess over the constant term, allocated to one outer vertex and half
of its adjacent middle vertex. The final square has positive coefficient. -/
def leafExcess (p c : ℝ × ℝ) : ℝ :=
  p.1 ^ 4 / 4 + c.1 ^ 4 / 8 +
    (p.1 - Real.sqrt 2 * p.2 / 2 - c.1 / 2) ^ 2 +
    (p.2 - Real.sqrt 2 * c.1 / 2 - c.2) ^ 2 / 2 +
    3 / 4 * (c.1 - 2 * Real.sqrt 2 * c.2 / 3) ^ 2 + c.2 ^ 2 / 12

theorem leafExcess_nonneg (p c : ℝ × ℝ) : 0 ≤ leafExcess p c := by
  unfold leafExcess
  positivity

theorem leafExcess_eq_zero (p c : ℝ × ℝ) :
    leafExcess p c = 0 ↔ p = (0, 0) ∧ c = (0, 0) := by
  rcases p with ⟨x, y⟩
  rcases c with ⟨a, b⟩
  constructor
  · intro h
    simp only [leafExcess] at h
    have hx4 : 0 ≤ x ^ 4 := by positivity
    have ha4 : 0 ≤ a ^ 4 := by positivity
    have hs₁ := sq_nonneg (x - Real.sqrt 2 * y / 2 - a / 2)
    have hs₂ := sq_nonneg (y - Real.sqrt 2 * a / 2 - b)
    have hs₃ := sq_nonneg (a - 2 * Real.sqrt 2 * b / 3)
    have hs₄ := sq_nonneg b
    have hx : x ^ 4 = 0 := by linarith
    have ha : a ^ 4 = 0 := by linarith
    have hb : b ^ 2 = 0 := by linarith
    have x0 : x = 0 := by simpa using hx
    have a0 : a = 0 := by simpa using ha
    have b0 : b = 0 := by simpa using hb
    subst x
    subst a
    subst b
    simp at h ⊢
    nlinarith [sq_nonneg (Real.sqrt 2 * y / 2), sq_nonneg y]
  · rintro ⟨h, k⟩
    simp_all [leafExcess]

/-- The two opposite middle-edge signs cancel all cross terms between
vertices 4 and 5. Each of the other four edges contributes one block. -/
theorem flipped_energy_decomposition (q : State) :
    energy flipped q = 3 / 2 + (leafExcess (q 0) (q 4) + leafExcess (q 1) (q 4) +
      leafExcess (q 2) (q 5) + leafExcess (q 3) (q 5)) := by
  rw [energy_expansion]
  simp [localPotential, edgeEnergy, flipped, sign, firstSource, firstTarget, leafExcess,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem flipped_minimum (q : State) : 3 / 2 ≤ energy flipped q := by
  rw [flipped_energy_decomposition]
  linarith [leafExcess_nonneg (q 0) (q 4), leafExcess_nonneg (q 1) (q 4),
    leafExcess_nonneg (q 2) (q 5), leafExcess_nonneg (q 3) (q 5)]

theorem flipped_minimum_iff (q : State) :
    energy flipped q = 3 / 2 ↔ q = fun _ => (0, 0) := by
  rw [flipped_energy_decomposition]
  constructor
  · intro h
    have hz : leafExcess (q 0) (q 4) + leafExcess (q 1) (q 4) +
        leafExcess (q 2) (q 5) + leafExcess (q 3) (q 5) = 0 := by linarith
    have hn₀ := leafExcess_nonneg (q 0) (q 4)
    have hn₁ := leafExcess_nonneg (q 1) (q 4)
    have hn₂ := leafExcess_nonneg (q 2) (q 5)
    have hn₃ := leafExcess_nonneg (q 3) (q 5)
    rw [add_eq_zero_iff_of_nonneg (add_nonneg (add_nonneg hn₀ hn₁) hn₂) hn₃,
      add_eq_zero_iff_of_nonneg (add_nonneg hn₀ hn₁) hn₂,
      add_eq_zero_iff_of_nonneg hn₀ hn₁] at hz
    simp only [leafExcess_eq_zero] at hz
    funext v
    fin_cases v <;> tauto
  · rintro rfl
    norm_num [leafExcess]

/-- At the origin every edge term vanishes, and each of the six vertices costs 1/4. -/
theorem energy_zero_state (τ : Twist) : energy τ (fun _ => (0, 0)) = 3 / 2 := by
  rw [energy_expansion]
  norm_num [localPotential, edgeEnergy]

/-- Switching the labels fixes the origin and reflects equality to it. -/
theorem switchState_eq_zero_iff (g : Spin) (q : State) :
    switchState g q = (fun _ => (0, 0)) ↔ q = fun _ => (0, 0) := by
  constructor
  · intro h
    funext v
    have hv := congrFun h v
    cases hg : g v <;> simpa [switchState, hg, Prod.ext_iff] using hv
  · rintro rfl
    funext v
    cases hg : g v <;> simp [switchState, hg]

theorem odd_minimum {τ : Twist} (h : middleParity τ = true) (q : State) :
    3 / 2 ≤ energy τ q := by
  rw [← energy_switch (treeGauge τ) τ q, tree_normal_form, h]
  exact flipped_minimum _

theorem odd_minimum_iff {τ : Twist} (h : middleParity τ = true) (q : State) :
    energy τ q = 3 / 2 ↔ q = fun _ => (0, 0) := by
  rw [← energy_switch (treeGauge τ) τ q, tree_normal_form, h]
  exact (flipped_minimum_iff _).trans (switchState_eq_zero_iff _ _)

/-- For all 64 signatures the parity-dependent lower bound is attained. -/
theorem least_energy (τ : Twist) :
    IsLeast (Set.range (energy τ)) (if middleParity τ then 3 / 2 else 0) := by
  cases h : middleParity τ with
  | false =>
    exact ⟨(zero_energy_iff τ).2 h, fun _ ⟨q, hq⟩ => hq ▸ energy_nonneg τ q⟩
  | true =>
    exact ⟨⟨_, energy_zero_state τ⟩, fun _ ⟨q, hq⟩ => hq ▸ odd_minimum h q⟩

end LinearInputLaaksoSignedMinimum

end
