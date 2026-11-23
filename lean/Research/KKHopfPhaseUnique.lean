import Mathlib.Tactic
import Research.KKHopfGlobalAlgebra
import Research.KKHopfActionFree

/-!
# Hopf phase uniqueness on the unit three-sphere

The circle action is free; here we additionally extract its phase using
explicit dot and skew products. This yields a constructive unique overlap
transition once the two local section values have equal Hopf images.
-/
namespace KKHopfPhaseUnique
open KKHopfGlobalAlgebra

def skew (X Y : X4) : ℝ :=
  X 0 * Y 1 - X 1 * Y 0 + X 2 * Y 3 - X 3 * Y 2

/-- For any R4 vector the skew product recovers the sine coefficient. -/
theorem skew_rotate (C S : ℝ) (X : X4) :
    skew X (rotate C S X) = S * radiusSq X := by
  simp [skew,rotate,radiusSq]
  ring

/-- The unit circle phase acting on a unit Hopf fibre is unique. -/
theorem phase_unique_on_sphere (C S D T : ℝ) (X : X4)
    (hX : radiusSq X = 1)
    (heq : rotate C S X = rotate D T X) : C = D ∧ S = T := by
  have hc : C = D := by
    have h := congrArg (KKHopfActionFree.dot4 X) heq
    rw [KKHopfActionFree.dot_rotate,KKHopfActionFree.dot_rotate,hX] at h
    nlinarith
  have hs : S = T := by
    have h := congrArg (skew X) heq
    rw [skew_rotate,skew_rotate,hX] at h
    nlinarith
  exact ⟨hc,hs⟩

end KKHopfPhaseUnique
