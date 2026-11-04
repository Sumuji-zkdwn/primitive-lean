import Mathlib

/-!
# Uniform three-layer Jordan companion, for arbitrary pole order p

This is the exact coordinate form predicted by the first two moment shells
of x + a/x^p. Each residue r = 0,...,p has a block of length 3:
  N(v0,v1,v2) =
    ( -(r+1)a*v1 + binomial(r+2,2)*a^2*v2,
      -(p+2+r)a*v2, 0).
The polynomial-observable bridge is a separate proof obligation; this file
formalizes the universal block identities, not arbitrary-degree similarity.
-/

namespace OrbitTrace

structure ThreeCoordinates where
  low : ℚ
  middle : ℚ
  high : ℚ

def generalThreeBlock (p r : ℕ) (a : ℚ)
    (v : ThreeCoordinates) : ThreeCoordinates :=
  { low := -((r : ℚ) + 1) * a * v.middle +
        (((r : ℚ) + 1) * ((r : ℚ) + 2) / 2) * a ^ 2 * v.high
    middle := -((p : ℚ) + 2 + (r : ℚ)) * a * v.high
    high := 0 }

theorem generalThreeBlock_square_low (p r : ℕ) (a : ℚ)
    (v : ThreeCoordinates) :
    (generalThreeBlock p r a (generalThreeBlock p r a v)).low =
      ((r : ℚ) + 1) * ((p : ℚ) + 2 + (r : ℚ)) * a ^ 2 * v.high := by
  simp only [generalThreeBlock]
  ring

theorem generalThreeBlock_cube_zero (p r : ℕ) (a : ℚ)
    (v : ThreeCoordinates) :
    generalThreeBlock p r a
      (generalThreeBlock p r a (generalThreeBlock p r a v)) =
        ⟨0, 0, 0⟩ := by
  cases v
  simp [generalThreeBlock]

def generalThreeTop : ThreeCoordinates := ⟨0, 0, 1⟩

theorem generalThreeBlock_square_nonzero (p r : ℕ) (a : ℚ)
    (ha : a ≠ 0) :
    (generalThreeBlock p r a
      (generalThreeBlock p r a generalThreeTop)).low ≠ 0 := by
  rw [generalThreeBlock_square_low]
  have hr : ((r : ℚ) + 1) ≠ 0 := by positivity
  have hp : ((p : ℚ) + 2 + (r : ℚ)) ≠ 0 := by positivity
  have hn : ((r : ℚ) + 1) * ((p : ℚ) + 2 + (r : ℚ)) * a ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hr hp) (pow_ne_zero 2 ha)
  simpa [generalThreeTop] using hn

def generalThreeBlocks (p : ℕ) (a : ℚ)
    (v : Fin (p + 1) → ThreeCoordinates) :
    Fin (p + 1) → ThreeCoordinates :=
  fun i => generalThreeBlock p i.val a (v i)

theorem generalThreeBlocks_cube_zero (p : ℕ) (a : ℚ)
    (v : Fin (p + 1) → ThreeCoordinates) :
    generalThreeBlocks p a
      (generalThreeBlocks p a (generalThreeBlocks p a v)) =
      fun _ => ⟨0, 0, 0⟩ := by
  funext i
  exact generalThreeBlock_cube_zero p i.val a (v i)

#print axioms OrbitTrace.generalThreeBlock_cube_zero
#print axioms OrbitTrace.generalThreeBlock_square_nonzero
#print axioms OrbitTrace.generalThreeBlocks_cube_zero

end OrbitTrace
