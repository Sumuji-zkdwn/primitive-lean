/-!
# Round trip 13: deformed energy → order-theoretic invariants → the Maxwell corner again

Input: round 12 (every deformation `deform p β` preserves order but breaks additivity)
and round 4 (the design value function has a corner at the Maxwell point `u = 0`).
Translation (order theory / smooth conjugacy): `deform p β` is a strictly increasing
smooth bijection onto its image with a smooth inverse, so it commutes with minimization
and cannot remove a corner. Back-translation: for every exponent `p` and `β > 0`, the
deformed value of the baseline design energy is the minimum of the deformed energies and
is still not differentiable at `u = 0` when `λ > 0 > r`. The phase transition belongs to
the order structure, not to the additive structure.
-/

noncomputable section
namespace RoundTrip13
open Real Elastica LinearInputDesign RoundTrip12

theorem deform_strictMono (p : ℝ) {β : ℝ} (hβ : 0 < β) : StrictMono (deform p β) := by
  intro x y hxy
  have := strictAnti_powerLog_exp_neg_mul p hβ hxy
  unfold deform
  rw [div_lt_div_iff_of_pos_right hβ, neg_lt_neg_iff]
  exact this

theorem deform_zero {β : ℝ} (hβ : β ≠ 0) (e : ℝ) : deform 0 β e = e := by
  unfold deform
  rw [powerLog_zero, log_exp]
  field_simp

/-- Smooth left inverse for `p ≠ 0`. -/
theorem deform_left_inverse {p β : ℝ} (hp : p ≠ 0) (hβ : β ≠ 0) (e : ℝ) :
    -log (1 - p * β * deform p β e) / (p * β) = e ∧ 0 < 1 - p * β * deform p β e := by
  rw [deform_eq hp]
  have hpb : p * β ≠ 0 := mul_ne_zero hp hβ
  have h1 : 1 - p * β * ((1 - exp (-(p * β * e))) / (p * β)) = exp (-(p * β * e)) := by
    field_simp; ring
  rw [h1, log_exp]
  exact ⟨by field_simp, exp_pos _⟩

/-- A corner survives every deformation. -/
theorem not_differentiableAt_deform {φ : ℝ → ℝ} {u₀ : ℝ} (p : ℝ) {β : ℝ} (hβ : β ≠ 0)
    (h : ¬ DifferentiableAt ℝ φ u₀) :
    ¬ DifferentiableAt ℝ (fun u => deform p β (φ u)) u₀ := by
  intro hd
  by_cases hp : p = 0
  · subst hp
    simp only [deform_zero hβ] at hd
    exact h hd
  · apply h
    have hne : 1 - p * β * deform p β (φ u₀) ≠ 0 := (deform_left_inverse hp hβ _).2.ne'
    have hg : DifferentiableAt ℝ (fun u => -log (1 - p * β * deform p β (φ u)) / (p * β)) u₀ :=
      ((((differentiableAt_const _).sub (hd.const_mul (p * β))).log hne).neg).div_const _
    have heq : (fun u => -log (1 - p * β * deform p β (φ u)) / (p * β)) = φ :=
      funext fun u => (deform_left_inverse hp hβ (φ u)).1
    rwa [heq] at hg

/-- The deformed value is the value of the deformed problem (order commutes with `inf`). -/
theorem deform_value_is_min (p : ℝ) {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (r u : ℝ) :
    (∀ x y, deform p β (RoundTrip04.value lam r u) ≤ deform p β (E lam r u x y)) ∧
      ∃ x y, deform p β (RoundTrip04.value lam r u) = deform p β (E lam r u x y) := by
  refine ⟨fun x y => (deform_strictMono p hβ).monotone (RoundTrip04.value_le hlam r u x y), ?_⟩
  obtain ⟨z, hz⟩ := LinearInputCoercivity.exists_global_minimum hlam r u
  refine ⟨z.1, z.2, congrArg _ ?_⟩
  exact le_antisymm (RoundTrip04.value_le hlam r u z.1 z.2) (le_ciInf hz)

/-- The composite result of rounds 2–4 and 11–13: every deformed design value function has
the Maxwell corner at `u = 0` when `λ > 0 > r`. -/
theorem deformed_maxwell_corner (p : ℝ) {β lam r : ℝ} (hβ : β ≠ 0) (hlam : 0 < lam)
    (hr : r < 0) :
    ¬ DifferentiableAt ℝ (fun u => deform p β (RoundTrip04.value lam r u)) 0 :=
  not_differentiableAt_deform p hβ (RoundTrip04.value_not_differentiableAt_zero hlam hr)

end RoundTrip13
