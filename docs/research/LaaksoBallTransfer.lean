import Mathlib.Tactic

/-!
# Conditional doubling transfer for gate-quotient metrics

This proves the measure-theoretic reduction used in the A-track manuscript.
Neither a Laakso path-distance comparison nor the one-dimensional doubling
of the specifically constructed tent density is proved here. Those geometric
hypotheses must be supplied to apply the theorem.

The ball families are abstract sets, so no metric or quotient properties are
smuggled into the Lean statement.
-/

namespace LaaksoBallTransfer

universe u
variable {X : Type u}

def Doubles (B : X → ℝ → Set X) (mass : Set X → ℝ) (C : ℝ) : Prop :=
  ∀ (x : X) (r : ℝ), 0 < r → mass (B x (2 * r)) ≤ C * mass (B x r)

/-- Repeated doubling gives a universal bound under 2^n radius expansion. -/
theorem iterated_doubling (B : X → ℝ → Set X) (mass : Set X → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hB : Doubles B mass C)
    (x : X) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    mass (B x ((2 : ℝ) ^ n * r)) ≤ C ^ n * mass (B x r) := by
  induction n with
  | zero =>
      simpa using (le_refl (mass (B x r)))
  | succ n ih =>
      have hpow : 0 < (2 : ℝ) ^ n * r :=
        mul_pos (pow_pos (by norm_num) _) hr
      have hrewrite : (2 : ℝ) ^ (n + 1) * r =
          2 * ((2 : ℝ) ^ n * r) := by
        rw [pow_succ]
        ring
      calc
        mass (B x ((2 : ℝ) ^ (n + 1) * r)) =
            mass (B x (2 * ((2 : ℝ) ^ n * r))) :=
          congrArg (fun t : ℝ => mass (B x t)) hrewrite
        _ ≤ C * mass (B x ((2 : ℝ) ^ n * r)) := hB x _ hpow
        _ ≤ C * (C ^ n * mass (B x r)) :=
          mul_le_mul_of_nonneg_left ih hC
        _ = C ^ (n + 1) * mass (B x r) := by
          rw [pow_succ]
          ring

/-- An exact conditional transfer of a doubling bound.  The key geometric
hypothesis is the uniform ball sandwich (no hidden metric assumptions).
This is the step available for kernel certification independently of the
hard Laakso-specific proof of that sandwich. -/
theorem doubling_of_uniform_ball_sandwich
    (B N : X → ℝ → Set X) (mass : Set X → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hmono : ∀ A A' : Set X, A ⊆ A' → mass A ≤ mass A')
    (hB : Doubles B mass C)
    (hsandwich : ∀ (x : X) (r : ℝ), 0 < r →
      ∃ t : ℝ, 0 < t ∧ B x t ⊆ N x r ∧
        N x (2 * r) ⊆ B x ((2 : ℝ) ^ k * t)) :
    Doubles N mass (C ^ k) := by
  intro x r hr
  rcases hsandwich x r hr with ⟨t, ht, hinner, houter⟩
  calc
    mass (N x (2 * r)) ≤ mass (B x ((2 : ℝ) ^ k * t)) :=
      hmono _ _ houter
    _ ≤ C ^ k * mass (B x t) :=
      iterated_doubling B mass C hC hB x t ht k
    _ ≤ C ^ k * mass (N x r) :=
      mul_le_mul_of_nonneg_left (hmono _ _ hinner) (pow_nonneg hC _)

#print axioms iterated_doubling
#print axioms doubling_of_uniform_ball_sandwich

end LaaksoBallTransfer
