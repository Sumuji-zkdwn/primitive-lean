import Mathlib

/-!
# Orbit trace: independently checked polynomial identities

This is an additive formalization. General Vieta traces, change-of-variable
integrals and Jordan decompositions are stated separately in the research note.
No sorry or new axioms.
-/

namespace OrbitTrace

private def cubicP (x : ℝ) : ℝ := x ^ 3 - 3 * x + 1
private def quadQ (x : ℝ) : ℝ := x ^ 2 - x

theorem cubic_orbit_numerator (x : ℝ) :
    x ^ 2 * (x - 1) ^ 2 + x ^ 2 + (x - 1) ^ 2 =
      (x ^ 2 - x + 1) ^ 2 := by
  ring

theorem original_primitive_derivative_numerator (x : ℝ) :
    (1 - 2 * x) * cubicP x - (x - x ^ 2) * (3 * x ^ 2 - 3) =
      (x ^ 2 - x + 1) ^ 2 := by
  unfold cubicP
  ring

theorem simplest_cubic_family (x s : ℝ) :
    cubicP x - s * quadQ x = x ^ 3 - s * x ^ 2 + (s - 3) * x + 1 := by
  unfold cubicP quadQ
  ring

theorem simplest_cubic_discriminant (s : ℝ) :
    (-s) ^ 2 * (s - 3) ^ 2 - 4 * (s - 3) ^ 3 -
      4 * (-s) ^ 3 - 27 + 18 * (-s) * (s - 3) =
      (s ^ 2 - 3 * s + 9) ^ 2 := by
  ring

def linearE (z : ℝ × ℝ) : ℝ × ℝ := (z.2, z.2 - z.1)

def quadraticInv (z : ℝ × ℝ) : ℝ := z.1 ^ 2 - z.1 * z.2 + z.2 ^ 2

theorem linearE_cube (z : ℝ × ℝ) :
    linearE (linearE (linearE z)) = (-z.1, -z.2) := by
  rcases z with ⟨u, v⟩
  apply Prod.ext
  · dsimp [linearE]
    ring
  · dsimp [linearE]
    ring

theorem linearE_quadratic_invariant (z : ℝ × ℝ) :
    quadraticInv (linearE z) = quadraticInv z := by
  rcases z with ⟨u, v⟩
  dsimp [linearE, quadraticInv]
  ring

def shear (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + z.2 ^ 3, z.2)
def unshear (z : ℝ × ℝ) : ℝ × ℝ := (z.1 - z.2 ^ 3, z.2)

theorem shear_unshear (z : ℝ × ℝ) : shear (unshear z) = z := by
  rcases z with ⟨u, v⟩
  apply Prod.ext
  · dsimp [shear, unshear]
    ring
  · dsimp [shear, unshear]

theorem unshear_shear (z : ℝ × ℝ) : unshear (shear z) = z := by
  rcases z with ⟨u, v⟩
  apply Prod.ext
  · dsimp [shear, unshear]
    ring
  · dsimp [shear, unshear]

def nonlinearE (z : ℝ × ℝ) : ℝ × ℝ :=
  unshear (linearE (shear z))

def nonlinearInv (z : ℝ × ℝ) : ℝ := quadraticInv (shear z)

theorem nonlinearE_invariant (z : ℝ × ℝ) :
    nonlinearInv (nonlinearE z) = nonlinearInv z := by
  simp only [nonlinearInv, nonlinearE, shear_unshear]
  exact linearE_quadratic_invariant (shear z)

theorem nonlinearE_cube (z : ℝ × ℝ) :
    nonlinearE (nonlinearE (nonlinearE z)) = (-z.1, -z.2) := by
  calc
    nonlinearE (nonlinearE (nonlinearE z)) =
        unshear (linearE (linearE (linearE (shear z)))) := by
          simp only [nonlinearE, shear_unshear]
    _ = unshear (-(shear z).1, -(shear z).2) := by
          rw [linearE_cube]
    _ = (-z.1, -z.2) := by
          rcases z with ⟨u, v⟩
          apply Prod.ext
          · dsimp [shear, unshear]
            ring
          · dsimp [shear, unshear]

-- The algebraic determinant identity, with separately derived partials.
theorem shear_jacobian_polynomial_identity (u U V : ℝ) :
    (1 + 6 * u ^ 2 * V) * (1 - 6 * U ^ 2 * V) -
      (2 * V) * (3 * u ^ 2 - 3 * U ^ 2 * (1 + 6 * u ^ 2 * V)) = 1 := by
  ring

universe u
variable {α : Type u}

def trajectory (E : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => E (trajectory E n x)

def coboundarySum (E : α → α) (G : α → ℝ) : ℕ → α → ℝ
  | 0, _ => 0
  | n + 1, x =>
      coboundarySum E G n x +
        (G (trajectory E n x) - G (trajectory E (n + 1) x))

theorem coboundary_telescope (E : α → α) (G : α → ℝ)
    (n : ℕ) (x : α) :
    coboundarySum E G n x = G x - G (trajectory E n x) := by
  induction n with
  | zero => simp [coboundarySum, trajectory]
  | succ n ih =>
      calc
        coboundarySum E G (n + 1) x =
            coboundarySum E G n x +
              (G (trajectory E n x) - G (trajectory E (n + 1) x)) := rfl
        _ = G x - G (trajectory E (n + 1) x) := by rw [ih]; ring

theorem cyclic_coboundary_vanishes (E : α → α) (G : α → ℝ)
    (n : ℕ) (x : α) (h : trajectory E n x = x) :
    coboundarySum E G n x = 0 := by
  rw [coboundary_telescope, h]
  ring

#print axioms OrbitTrace.cubic_orbit_numerator
#print axioms OrbitTrace.original_primitive_derivative_numerator
#print axioms OrbitTrace.simplest_cubic_discriminant
#print axioms OrbitTrace.nonlinearE_invariant
#print axioms OrbitTrace.nonlinearE_cube
#print axioms OrbitTrace.coboundary_telescope

end OrbitTrace
