/-!
Chebyshev normalization and loss of states under minimum-only observation.
Both connections start from the existing primitive linear-input definitions.
The normalization and the choice to iterate it are explicit model choices.
-/

noncomputable section
open Real

namespace LinearInputBranchForgetting

def chebyshevThree (x : ℝ) : ℝ := 4 * x ^ 3 - 3 * x

/-- The cubic is the existing design input at an explicit parameter choice. -/
theorem chebyshevThree_eq_input (x : ℝ) :
    chebyshevThree x = LinearInputDesign.input 4 (-3) x := by
  unfold chebyshevThree LinearInputDesign.input
  ring

/-- A general scaled family, without dividing by a possibly zero scale. -/
theorem input_normalization (lam s x : ℝ) :
    LinearInputDesign.input lam (-3 * lam * s ^ 2 / 4) (s * x) =
      lam * s ^ 3 / 4 * chebyshevThree x := by
  unfold LinearInputDesign.input chebyshevThree
  ring

/-- Connect to the actual derivative theorem, not an assumed stationary equation. -/
theorem stationary_iff_chebyshev (u x : ℝ) :
    deriv (LinearInputCalculus.potential 4 (-3) u) x = 0 ↔
      u = chebyshevThree x := by
  simpa only [chebyshevThree, sub_eq_add_neg, neg_mul, one_mul] using
    (LinearInputCalculus.stationary_iff_input 4 (-3) u x)

theorem chebyshevThree_cos (t : ℝ) :
    chebyshevThree (cos t) = cos (3 * t) := by
  exact (Real.cos_three_mul t).symm

/-- Iterating the stationary-input polynomial is an explicitly chosen operation. -/
def ternaryIterate : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => chebyshevThree (ternaryIterate n x)

theorem ternaryIterate_cos (n : ℕ) (t : ℝ) :
    ternaryIterate n (cos t) = cos ((3 : ℝ) ^ n * t) := by
  induction n with
  | zero => simp [ternaryIterate]
  | succ n ih =>
    rw [ternaryIterate, ih, chebyshevThree_cos, pow_succ]
    congr 1
    ring

/-- Every displayed inverse candidate solves the iterated equation.
This does not claim that different labels are distinct at critical values. -/
theorem iterated_inverse_candidate (n : ℕ) (t : ℝ) (j : ℕ) :
    ternaryIterate n (cos ((t + j * (2 * π)) / (3 : ℝ) ^ n)) = cos t := by
  rw [ternaryIterate_cos]
  have hn : (3 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have harg : (3 : ℝ) ^ n * ((t + j * (2 * π)) / (3 : ℝ) ^ n) =
      t + j * (2 * π) := by field_simp
  rw [harg, Real.cos_add_nat_mul_two_pi]

/-- A count of branch words, separately from distinct geometric images. -/
theorem ternary_word_count (n : ℕ) :
    Fintype.card (Fin n → Fin 3) = 3 ^ n := by
  simp

/-- A state above the chord of two (observable, base-energy) pairs cannot
lower the minimum energy at any linear input. -/
theorem hidden_state_above_chord {S : Type*} (A X : S → ℝ)
    (p q r : S) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hX : X q = (1 - t) * X p + t * X r)
    (hA : (1 - t) * A p + t * A r ≤ A q) (u : ℝ) :
    min (LinearInputObservation.energy A X u p)
        (LinearInputObservation.energy A X u r) ≤
      LinearInputObservation.energy A X u q := by
  have hp := min_le_left (LinearInputObservation.energy A X u p)
    (LinearInputObservation.energy A X u r)
  have hr := min_le_right (LinearInputObservation.energy A X u p)
    (LinearInputObservation.energy A X u r)
  have hb := add_le_add (mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr ht1))
    (mul_le_mul_of_nonneg_left hr ht0)
  have he : (1 - t) * LinearInputObservation.energy A X u p +
      t * LinearInputObservation.energy A X u r ≤
        LinearInputObservation.energy A X u q := by
    unfold LinearInputObservation.energy
    rw [hX]
    nlinarith
  nlinarith

/-- Adding the hidden state leaves the entire input-to-minimum function unchanged. -/
theorem minimum_forgets_hidden_state {S : Type*} (A X : S → ℝ)
    (p q r : S) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hX : X q = (1 - t) * X p + t * X r)
    (hA : (1 - t) * A p + t * A r ≤ A q) :
    (fun u => min (min (LinearInputObservation.energy A X u p)
        (LinearInputObservation.energy A X u r))
        (LinearInputObservation.energy A X u q)) =
      (fun u => min (LinearInputObservation.energy A X u p)
        (LinearInputObservation.energy A X u r)) := by
  funext u
  exact min_eq_left (hidden_state_above_chord A X p q r t ht0 ht1 hX hA u)

end LinearInputBranchForgetting
