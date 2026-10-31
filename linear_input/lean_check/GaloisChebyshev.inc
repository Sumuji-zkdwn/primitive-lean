/-!
# Chebyshev branches through cyclotomic and Kummer data

This is an additive algebraic bridge to the existing real-valued Chebyshev
branch and F0 retraction proofs.  The Joukowski map has an involution
z ↦ z⁻¹; its fibers and the cubic identity can be stated over ℂ without
trigonometric arguments.  Primitive roots of unity give Kummer root labels,
and ZMod carries the elementary rotation/reflection operations.

Scope: this file proves elementary algebraic bridges and reuses the existing
critical-fiber kernels.  It does NOT identify the full Galois group of
T_(3^n)(X) - y, construct a field extension, or assert that its label actions
are automorphisms of that extension.  Those require separate hypotheses and
future proofs.
-/

noncomputable section

namespace LinearInputGaloisChebyshev

/-- The quotient of the multiplicative coordinate by inversion. -/
def joukowski (z : ℂ) : ℂ := (z + z⁻¹) / 2

/-- The complex polynomial corresponding to the existing real cubic. -/
def cubic (x : ℂ) : ℂ := 4 * x ^ 3 - 3 * x

/-- Candidate roots of z^m = w, indexed by powers of a root of unity. -/
def kummerCandidate (ζ z : ℂ) (j : ℕ) : ℂ := ζ ^ j * z

/-- Addition of a label modulo m (the rotation part). -/
def shiftLabel (m : ℕ) (a j : ZMod m) : ZMod m := j + a

/-- Reflection for the critical fiber over +1. -/
def zeroReflection (m : ℕ) (j : ZMod m) : ZMod m := -j

/-- Reflection for the critical fiber over -1. -/
def piReflection (m : ℕ) (j : ZMod m) : ZMod m := -j - 1

theorem joukowski_inversion (z : ℂ) :
    joukowski z⁻¹ = joukowski z := by
  simp [joukowski, add_comm]

theorem cubic_real (x : ℝ) :
    cubic (x : ℂ) =
      (LinearInputBranchForgetting.chebyshevThree x : ℂ) := by
  unfold cubic LinearInputBranchForgetting.chebyshevThree
  push_cast
  ring

/-- The fundamental T₃(J(z)) = J(z³) identity, away from z = 0. -/
theorem cubic_joukowski (z : ℂ) (hz : z ≠ 0) :
    cubic (joukowski z) = joukowski (z ^ 3) := by
  unfold cubic joukowski
  field_simp [hz]
  <;> ring

/-- Clearing denominators exposes the exact collision factorization. -/
theorem collision_identity (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (joukowski a - joukowski b) * (2 * a * b) =
      (a - b) * (a * b - 1) := by
  unfold joukowski
  field_simp [ha, hb]
  <;> ring

/-- Distinct nonzero multiplicative labels collide iff they are inverses. -/
theorem joukowski_eq_iff (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    joukowski a = joukowski b ↔ a = b ∨ a * b = 1 := by
  have hab : 2 * a * b ≠ (0 : ℂ) :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
  constructor
  · intro h
    have hf := collision_identity a b ha hb
    rw [h, sub_self, zero_mul] at hf
    rcases mul_eq_zero.mp hf.symm with hleft | hright
    · exact Or.inl (sub_eq_zero.mp hleft)
    · exact Or.inr (sub_eq_zero.mp hright)
  · rintro (h | h)
    · rw [h]
    · have hprod : (a - b) * (a * b - 1) = 0 := by
        rw [h]
        ring
      have hf := (collision_identity a b ha hb).trans hprod
      exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hab)

/-- A primitive m-th root is a root of the m-th cyclotomic polynomial. -/
theorem primitive_cyclotomic_root {m : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) :
    (Polynomial.cyclotomic m ℂ).IsRoot ζ :=
  hζ.isRoot_cyclotomic

/-- Kummer label rotation preserves the equation z^m = w. -/
theorem kummer_candidate_pow {m j : ℕ} {ζ z w : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hz : z ^ m = w) :
    (kummerCandidate ζ z j) ^ m = w := by
  calc
    (kummerCandidate ζ z j) ^ m = (ζ ^ m) ^ j * z ^ m := by
      unfold kummerCandidate
      rw [mul_pow, ← pow_mul, mul_comm j m, pow_mul]
    _ = w := by rw [hζ.pow_eq_one, one_pow, one_mul, hz]

theorem shiftLabel_comp (m : ℕ) (a b j : ZMod m) :
    shiftLabel m b (shiftLabel m a j) = shiftLabel m (a + b) j := by
  simp [shiftLabel, add_assoc]

theorem zeroReflection_involutive (m : ℕ) (j : ZMod m) :
    zeroReflection m (zeroReflection m j) = j := by
  simp [zeroReflection]

theorem piReflection_involutive (m : ℕ) (j : ZMod m) :
    piReflection m (piReflection m j) = j := by
  dsimp [piReflection]
  ring

/-- A reflection conjugates label translation to its inverse. -/
theorem zeroReflection_shift (m : ℕ) (a j : ZMod m) :
    zeroReflection m (shiftLabel m a j) =
      shiftLabel m (-a) (zeroReflection m j) := by
  simp [zeroReflection, shiftLabel, neg_add]

/-- Direct bridge to the existing idempotent critical-fiber kernel (+1). -/
theorem branchZero_kernel_iff (m : ℕ) (j k : Fin (2 * m + 1)) :
    LinearInputF0.branchZeroK m j = LinearInputF0.branchZeroK m k ↔
      j = k ∨ (j : ℕ) + (k : ℕ) = 2 * m + 1 := by
  exact (LinearInputF0.branchZero_kernel m j k).trans
    (LinearInputBranchFibers.candidate_eq_zero_iff (by omega) j k)

/-- Direct bridge to the existing idempotent critical-fiber kernel (-1). -/
theorem branchPi_kernel_iff (m : ℕ) (j k : Fin (2 * m + 1)) :
    LinearInputF0.branchPiK m j = LinearInputF0.branchPiK m k ↔
      j = k ∨ (j : ℕ) + (k : ℕ) + 1 = 2 * m + 1 := by
  exact (LinearInputF0.branchPi_kernel m j k).trans
    (LinearInputBranchFibers.candidate_eq_pi_iff (by omega) j k)

end LinearInputGaloisChebyshev
