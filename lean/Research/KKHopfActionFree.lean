import Mathlib.Tactic
import Research.KKHopfGlobalAlgebra

/-!
# Freeness and metric invariance of the diagonal Hopf circle action

These are algebraic theorems on S³, not a Mathlib quotient-manifold atlas.
-/
namespace KKHopfActionFree
open KKHopfGlobalAlgebra

def dot4 (X Y : X4) : ℝ :=
  X 0*Y 0+X 1*Y 1+X 2*Y 2+X 3*Y 3

/-- The inner product of X with its rotated image is C*|X|². -/
theorem dot_rotate (C S : ℝ) (X : X4) :
    dot4 X (rotate C S X) = C * radiusSq X := by
  simp [dot4, rotate, radiusSq]
  ring

/-- A unit diagonal rotation preserves every real four-dimensional dot product. -/
theorem rotate_dot (C S : ℝ) (X Y : X4) :
    dot4 (rotate C S X) (rotate C S Y) =
      (C^2+S^2) * dot4 X Y := by
  simp [dot4, rotate]
  ring

/-- The stabilizer of every X on the unit sphere is the identity phase. -/
theorem free_circle_action (C S : ℝ) (X : X4)
    (hunit : C^2+S^2=1) (hX : radiusSq X = 1)
    (hfix : rotate C S X = X) : C=1 ∧ S=0 := by
  have hd := dot_rotate C S X
  rw [hfix] at hd
  have hself : dot4 X X = radiusSq X := by
    simp [dot4, radiusSq]
    ring
  rw [hself,hX] at hd
  have hc : C=1 := by nlinarith [hd]
  have hs : S=0 := by nlinarith [hunit]
  exact ⟨hc,hs⟩

end KKHopfActionFree
