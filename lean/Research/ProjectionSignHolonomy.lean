import Mathlib.Tactic

/-!
# Projection sign holonomy: finite signed-edge core

Orthogonal projection from a unit vector u to the line of v has transfer
coefficient <u,v>. Its absolute value determines the length loss, while the
sign survives around a closed path. For the equiangular icosahedral example
all nontrivial coefficients have the same magnitude.

This file formalizes abstract symmetric signed gains, reversal on triangles,
four-cycle gauge invariance, a universal K4 sign constraint, and the six
four-cycle outcomes. The companion exact Python checker handles the
golden-ratio coordinates and finite enumeration.

This Lean file DOES NOT formally establish a projective-space topological
holonomy theorem, irrational coordinates, or physical dynamics.
-/

namespace ProjectionSignHolonomy

variable {ι : Type*} {R : Type*} [CommRing R]

/-- Signed gain around a triangle. -/
def cycle3 (g : ι → ι → R) (a b c : ι) : R :=
  g a b * g b c * g c a

/-- Signed gain along a four-step closed walk. -/
def cycle4 (g : ι → ι → R) (a b c d : ι) : R :=
  g a b * g b c * g c d * g d a

/-- A choice of new line representatives (signs eps). -/
def switch (g : ι → ι → R) (eps : ι → R) (a b : ι) : R :=
  eps a * g a b * eps b

/-- For symmetric overlaps, reversing a three-line circuit changes nothing. -/
theorem triangle_reverse (g : ι → ι → R)
    (hsym : ∀ a b, g a b = g b a) (a b c : ι) :
    cycle3 g a b c = cycle3 g a c b := by
  dsimp [cycle3]
  calc
    g a b * g b c * g c a = g b a * g c b * g a c := by
      rw [hsym a b, hsym b c, hsym c a]
    _ = g a c * g c b * g b a := by ring

/-- Four-step signed holonomy is unchanged when any line direction is flipped. -/
theorem cycle4_switch_invariant (g : ι → ι → R) (eps : ι → R)
    (heps : ∀ i, eps i * eps i = 1) (a b c d : ι) :
    cycle4 (switch g eps) a b c d = cycle4 g a b c d := by
  dsimp [cycle4, switch]
  calc
    (eps a * g a b * eps b) * (eps b * g b c * eps c) *
      (eps c * g c d * eps d) * (eps d * g d a * eps a) =
        (eps a * eps a) * (eps b * eps b) *
        (eps c * eps c) * (eps d * eps d) *
        (g a b * g b c * g c d * g d a) := by ring
    _ = g a b * g b c * g c d * g d a := by
      simp [heps]

/-- Three undirected Hamiltonian four-cycles have total gain +1.
Thus the six directed orders have either zero or four negative signs. -/
theorem three_four_cycles_product (g : ι → ι → R)
    (hsym : ∀ a b, g a b = g b a)
    (hsq : ∀ a b, g a b * g a b = 1) (a b c d : ι) :
    cycle4 g a b c d * cycle4 g a b d c * cycle4 g a c b d = 1 := by
  dsimp [cycle4]
  calc
    (g a b * g b c * g c d * g d a) *
      (g a b * g b d * g d c * g c a) *
      (g a c * g c b * g b d * g d a) =
      (g a b * g a b) * (g b c * g b c) *
      (g c d * g c d) * (g d a * g d a) *
      (g b d * g b d) * (g a c * g a c) := by
        rw [hsym d c, hsym c a, hsym c b]
        ring
    _ = 1 := by simp [hsq]

/-- Signs of the six equiangular lines in the icosahedral realization.
The diagonal is conventionally +1; distinct off-diagonal entries match
the exact algebraic coordinate calculation in the companion Python checker. -/
def sign6 (i j : Fin 6) : ℤ :=
  if i = j then 1 else
  if (i.val, j.val) ∈
      ([(0, 1), (1, 0), (0, 3), (3, 0), (0, 5), (5, 0),
        (1, 3), (3, 1), (1, 4), (4, 1), (2, 3), (3, 2)] : List (ℕ × ℕ))
  then -1 else 1

theorem abcda_negative : cycle4 sign6 0 1 2 3 = -1 := by decide
theorem acbda_positive : cycle4 sign6 0 2 1 3 = 1 := by decide
theorem abdca_negative : cycle4 sign6 0 1 3 2 = -1 := by decide
theorem acdba_negative : cycle4 sign6 0 2 3 1 = -1 := by decide
theorem adbca_positive : cycle4 sign6 0 3 1 2 = 1 := by decide
theorem adcba_negative : cycle4 sign6 0 3 2 1 = -1 := by decide

end ProjectionSignHolonomy
