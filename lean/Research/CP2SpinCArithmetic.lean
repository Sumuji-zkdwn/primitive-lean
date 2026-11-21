import Mathlib.Tactic

/-!
# Spin-c index arithmetic for the canonical complex geometry of CP2

This is an arithmetic companion to the conventional 4D Spin-c index theorem:
  ind(D_L) = (c₁(L)^2 - signature(M)) / 8.
For CP2, signature=1 and the canonical determinant line is O(3). Twisting by
O(k) changes the determinant to O(3+2k).

**Only the polynomial identities below are Lean formalized.** Neither the
Atiyah--Singer theorem, the topology of CP2, nor a constructed spinor bundle
is Lean proved here. The separate research note describes those assumptions.
-/

namespace CP2SpinCArithmetic

def determinantChernCoefficient (k : ℤ) : ℤ := 2 * k + 3

def indexNumerator (k : ℤ) : ℤ :=
  determinantChernCoefficient k ^ 2 - 1

/-- The numerator is divisible by 8 because (k+1)(k+2) is even. -/
theorem numerator_factorization (k : ℤ) :
    indexNumerator k = 4 * (k + 1) * (k + 2) := by
  dsimp [indexNumerator, determinantChernCoefficient]
  ring

/-- The canonical complex Spin-c determinant O(3) gives index 1 by the
    standard index formula; this is the arithmetic step only. -/
theorem canonical_numerator : indexNumerator 0 = 8 := by
  norm_num [indexNumerator, determinantChernCoefficient]

theorem first_twist_numerator : indexNumerator 1 = 24 := by
  norm_num [indexNumerator, determinantChernCoefficient]

theorem negative_first_twist_numerator : indexNumerator (-1) = 0 := by
  norm_num [indexNumerator, determinantChernCoefficient]

/-- The index numerator moves by a multiple of eight under a unit twist. -/
theorem numerator_step (k : ℤ) :
    indexNumerator (k + 1) - indexNumerator k = 8 * (k + 2) := by
  dsimp [indexNumerator, determinantChernCoefficient]
  ring

end CP2SpinCArithmetic
