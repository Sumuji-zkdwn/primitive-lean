import Mathlib

/-!
# Explicit degree-3 Jordan chains in the p=3 algebraic trace model

For residue r = 0,1,2,3, in monomial coordinates
  (x^r, x^(r+4), x^(r+8)),
the matrix of N = L - I calculated from the polynomial trace formula is

  [ 0, -(r+1)a, binom(r+2,2)*a^2 ]
  [ 0,      0, -(r+5)a          ]
  [ 0,      0,       0           ]

The algebraic matrix identities are proved here. The derivation of these
coordinates from the full general polynomial remainder operator still needs
an additional Lean bridge; do not conflate this matrix certificate with
a full general-Jordan classification theorem.
-/

namespace OrbitTrace

structure Triple where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ

def jordanBlockN (r : ℕ) (a : ℚ) (v : Triple) : Triple :=
  { c0 := -(((r : ℚ) + 1) * a) * v.c1 +
       (((r : ℚ) + 1) * ((r : ℚ) + 2) / 2) * a ^ 2 * v.c2
    c1 := -(((r : ℚ) + 5) * a) * v.c2
    c2 := 0 }

theorem jordanBlockN_square_top (r : ℕ) (a : ℚ) (v : Triple) :
    (jordanBlockN r a (jordanBlockN r a v)).c0 =
      ((r : ℚ) + 1) * ((r : ℚ) + 5) * a ^ 2 * v.c2 := by
  simp only [jordanBlockN]
  ring

theorem jordanBlockN_cube_zero (r : ℕ) (a : ℚ) (v : Triple) :
    jordanBlockN r a (jordanBlockN r a (jordanBlockN r a v)) =
      ⟨0, 0, 0⟩ := by
  apply Triple.ext <;> simp [jordanBlockN] <;> ring

def blockTop : Triple := ⟨0, 0, 1⟩

theorem jordanBlockN_square_top_nonzero (r : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (jordanBlockN r a (jordanBlockN r a blockTop)).c0 ≠ 0 := by
  rw [jordanBlockN_square_top]
  simp only [blockTop]
  have hr1 : ((r : ℚ) + 1) ≠ 0 := by positivity
  have hr5 : ((r : ℚ) + 5) ≠ 0 := by positivity
  exact mul_ne_zero (mul_ne_zero hr1 hr5) (pow_ne_zero 2 ha)

def fourBlocks (a : ℚ) (v : Fin 4 → Triple) : Fin 4 → Triple :=
  fun i => jordanBlockN i.val a (v i)

theorem fourBlocks_cube_zero (a : ℚ) (v : Fin 4 → Triple) :
    fourBlocks a (fourBlocks a (fourBlocks a v)) =
      fun _ => ⟨0, 0, 0⟩ := by
  funext i
  exact jordanBlockN_cube_zero i.val a (v i)

#print axioms OrbitTrace.jordanBlockN_cube_zero
#print axioms OrbitTrace.jordanBlockN_square_top_nonzero
#print axioms OrbitTrace.fourBlocks_cube_zero

end OrbitTrace
