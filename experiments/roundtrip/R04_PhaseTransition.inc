/-!
# Round trip 4: Maxwell set + supergradients → first-order phase transition → design

Input: round 2 (supergradients `-X z`) and round 3 (two global minimizers `±a₀` on the
Maxwell set). Translation (Landau theory): two minimizers with different order
parameter `X` force a corner in the value function, i.e. a first-order transition.
Back-translation: the actual infimum of the baseline design energy is not differentiable
at `u = 0` when `λ > 0 > r`, and minimizers on either side are separated by `2a₀`.
-/

noncomputable section
namespace RoundTrip04
open LinearInputDesign LinearInputObservation RoundTrip02

/-- General corner theorem: any lower bound of the pencil attained by two states with
different observables at `u₀` is not differentiable at `u₀`. -/
theorem not_differentiableAt_of_two_minimizers {S : Type*} (A X : S → ℝ) (φ : ℝ → ℝ)
    (hφ : ∀ u z, φ u ≤ energy A X u z) {u₀ : ℝ} {z₁ z₂ : S}
    (h₁ : φ u₀ = energy A X u₀ z₁) (h₂ : φ u₀ = energy A X u₀ z₂)
    (hX : X z₁ ≠ X z₂) : ¬ DifferentiableAt ℝ φ u₀ := by
  intro hd
  have key : ∀ z, φ u₀ = energy A X u₀ z → deriv φ u₀ = -X z := by
    intro z hz
    have hmax : IsLocalMax (fun u => φ u + (u - u₀) * X z) u₀ := by
      refine Filter.Eventually.of_forall fun u => ?_
      have := hφ u z
      simp only [energy] at this hz ⊢
      linarith
    have hder : HasDerivAt (fun u => φ u + (u - u₀) * X z) (deriv φ u₀ + X z) u₀ := by
      have := ((hasDerivAt_id u₀).sub_const u₀).mul_const (X z)
      simpa using hd.hasDerivAt.add this
    have := hmax.hasDerivAt_eq_zero hder
    linarith
  exact hX (by linarith [key z₁ h₁, key z₂ h₂])

theorem pencil_apply (lam r u : ℝ) (z : ℝ × ℝ) :
    energy (fun z : ℝ × ℝ => E lam r 0 z.1 z.2) (fun z => z.1) u z = E lam r u z.1 z.2 :=
  (RoundTrip03.design_is_pencil lam r u z.1 z.2).symm

theorem input_neg_of_margin {lam r a : ℝ} (h : lam * a ^ 2 + r = 0) : input lam r (-a) = 0 := by
  rw [RoundTrip03.input_eq_mul_margin, neg_sq, h, mul_zero]

/-- The actual value function of the baseline design energy. -/
def value (lam r u : ℝ) : ℝ := ⨅ z : ℝ × ℝ, E lam r u z.1 z.2

theorem value_bddBelow {lam : ℝ} (hlam : 0 < lam) (r u : ℝ) :
    BddBelow (Set.range fun z : ℝ × ℝ => E lam r u z.1 z.2) := by
  refine ⟨-LinearInputCoercivity.lowerBoundConstant lam r u, ?_⟩
  rintro _ ⟨z, rfl⟩
  have := LinearInputCoercivity.coercive_lower_bound hlam r u z.1 z.2
  nlinarith [sq_nonneg z.1, sq_nonneg (z.2 - Real.sqrt 2 * z.1)]

theorem value_le {lam : ℝ} (hlam : 0 < lam) (r u x y : ℝ) : value lam r u ≤ E lam r u x y :=
  ciInf_le (value_bddBelow hlam r u) (x, y)

/-- At a certified global minimum the infimum is attained. -/
theorem value_eq_of_globalMin {lam r a : ℝ} (hlam : 0 < lam) (h : GlobalMin lam r a) :
    value lam r (input lam r a) = E lam r (input lam r a) a (Real.sqrt 2 * a) :=
  le_antisymm (value_le hlam _ _ _ _) (le_ciInf fun z => h z.1 z.2)

/-- First-order transition of the actual design energy at the Maxwell point `u = 0`. -/
theorem value_not_differentiableAt_zero {lam r : ℝ} (hlam : 0 < lam) (hr : r < 0) :
    ¬ DifferentiableAt ℝ (value lam r) 0 := by
  set a := Real.sqrt (-r / lam)
  have hq : 0 < -r / lam := div_pos (neg_pos.mpr hr) hlam
  have ha : 0 < a := Real.sqrt_pos.2 hq
  have hmargin : lam * a ^ 2 + r = 0 := by
    rw [Real.sq_sqrt hq.le]; field_simp; ring
  obtain ⟨hP, hM, -⟩ := RoundTrip03.maxwell_two_global_minimizers hlam hmargin
  have hu : input lam r a = 0 := RoundTrip03.maxwell_input_zero hmargin
  have hu' : input lam r (-a) = 0 := input_neg_of_margin hmargin
  have eP := value_eq_of_globalMin hlam hP
  have eM := value_eq_of_globalMin hlam hM
  rw [hu] at eP
  rw [hu'] at eM
  refine not_differentiableAt_of_two_minimizers
    (fun z : ℝ × ℝ => E lam r 0 z.1 z.2) (fun z => z.1) (value lam r)
    (fun u z => ?_) (z₁ := (a, Real.sqrt 2 * a)) (z₂ := (-a, Real.sqrt 2 * (-a)))
    ?_ ?_ (by simp; linarith)
  · rw [pencil_apply]; exact value_le hlam r u z.1 z.2
  · rw [pencil_apply]; exact eP
  · rw [pencil_apply]; exact eM

/-- Order-parameter jump: every global minimizer for `u > 0` has `x ≥ a₀`, and for
`u < 0` has `x ≤ -a₀`, where `a₀ = √(-r/λ)` (via the monotone supergradients). -/
theorem order_parameter_jump {lam r u x y : ℝ} (hlam : 0 < lam) (hr : r < 0)
    (hmin : ∀ x' y', E lam r u x y ≤ E lam r u x' y') :
    (0 < u → Real.sqrt (-r / lam) ≤ x) ∧ (u < 0 → x ≤ -Real.sqrt (-r / lam)) := by
  set a := Real.sqrt (-r / lam)
  have hq : 0 < -r / lam := div_pos (neg_pos.mpr hr) hlam
  have hmargin : lam * a ^ 2 + r = 0 := by
    rw [Real.sq_sqrt hq.le]; field_simp; ring
  obtain ⟨hP, hM, -⟩ := RoundTrip03.maxwell_two_global_minimizers hlam hmargin
  have hu : input lam r a = 0 := RoundTrip03.maxwell_input_zero hmargin
  have hu' : input lam r (-a) = 0 := input_neg_of_margin hmargin
  let A := fun z : ℝ × ℝ => E lam r 0 z.1 z.2
  let X := fun z : ℝ × ℝ => z.1
  have hz : IsMinimizer A X u (x, y) := fun w => by
    simp only [A, X, pencil_apply]; exact hmin w.1 w.2
  have hzP : IsMinimizer A X 0 (a, Real.sqrt 2 * a) := fun w => by
    simp only [A, X, pencil_apply]; have := hP w.1 w.2; rwa [hu] at this
  have hzM : IsMinimizer A X 0 (-a, Real.sqrt 2 * (-a)) := fun w => by
    simp only [A, X, pencil_apply]; have := hM w.1 w.2; rwa [hu'] at this
  have mP := observable_monotone A X hzP hz
  have mM := observable_monotone A X hz hzM
  simp only [X] at mP mM
  constructor
  · intro hpos; by_contra hn; have hn := lt_of_not_ge hn; nlinarith
  · intro hneg; by_contra hn; have hn := lt_of_not_ge hn; nlinarith

end RoundTrip04
