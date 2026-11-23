import ObservedQuotient
import Mathlib.Tactic

/-!
# Exact bridge to PR #171's actual finiteStep / WalkCost

The finite operational state includes height, m Boolean labels and circle phase.
This module defines its height+bit projection and a phase-free step relation
with the *same* horizontal and gate costs as ObservedSandpile.finiteStep.

A full path projects to a horizontal/bit path at no greater cost; a projected
path lifts to the full model while holding phase fixed with exactly the same
cost. Therefore the two walkDistance expressions agree at equal phases.

The new statements concern the actual ENNReal-cost WalkCost and finiteStep
in ObservedQuotient, not the separate real-cost model in PR #211.
No infinite inverse-limit distance or global PI conclusion is assumed.
-/

namespace ObservedSandpile.FiniteStepHorizontalBridge

open ObservedSandpile
open scoped ENNReal

abbrev HeightBits (m : ℕ) := H × (Fin m → Bool)

def projection {m : ℕ} (x : FiniteState m) : HeightBits m :=
  (x.1, x.2.1)

def withPhase {m : ℕ} (x : HeightBits m) (p : Phase) : FiniteState m :=
  (x.1, x.2, p)

@[simp] theorem projection_withPhase {m : ℕ} (x : HeightBits m) (p : Phase) :
    projection (withPhase x p) = x := rfl

/-- Horizontal movement and free gate flips, without angular transitions. -/
def horizontalGateStep (m : ℕ) (x y : HeightBits m) (c : ℝ≥0∞) : Prop :=
  (x.2 = y.2 ∧ c = ENNReal.ofReal |x.1.1 - y.1.1|) ∨
  (x.1 = y.1 ∧ c = 0 ∧ ∃ k : Fin m, ternary x.1 k.val ∧
    ∀ i, y.2 i = (if i = k then !(x.2 i) else x.2 i))

/-- One phase-free step lifts to a full finiteStep with constant phase. -/
theorem lift_step {m : ℕ} (p : Phase)
    {x y : HeightBits m} {c : ℝ≥0∞}
    (h : horizontalGateStep m x y c) :
    finiteStep m (withPhase x p) (withPhase y p) c := by
  rcases h with ⟨hb, hc⟩ | ⟨hh, hc, k, hk, hflip⟩
  · left
    refine ⟨?_, hc⟩
    exact congrArg (fun b => (b, p)) hb
  · right
    right
    exact ⟨hh, rfl, hc, ⟨k, hk, hflip⟩⟩

/-- A phase-free walk lifts to a full walk without changing its cost. -/
theorem lift_walk {m : ℕ} (p : Phase)
    {x y : HeightBits m} {c : ℝ≥0∞}
    (h : WalkCost (horizontalGateStep m) x y c) :
    WalkCost (finiteStep m) (withPhase x p) (withPhase y p) c := by
  induction h with
  | stop x => exact .stop _
  | next hs ht ih => exact .next (lift_step p hs) ih

/-- Project any full finiteStep walk, deleting angular transitions.
The cost can only decrease; this is stronger than merely a relation
between the allowed single-step predicates. -/
theorem project_walk {m : ℕ}
    {x y : FiniteState m} {c : ℝ≥0∞}
    (h : WalkCost (finiteStep m) x y c) :
    ∃ d : ℝ≥0∞,
      WalkCost (horizontalGateStep m) (projection x) (projection y) d ∧
      d ≤ c := by
  induction h with
  | stop x =>
      exact ⟨0, WalkCost.stop _, le_rfl⟩
  | @next x y z c e hs ht ih =>
      rcases ih with ⟨d, hd, hle⟩
      rcases hs with ⟨hbits, hcost⟩ | ⟨hheight, hbits, hcost⟩ |
        ⟨hheight, hphase, hcost, k, hk, hflip⟩
      · have hstep : horizontalGateStep m (projection x) (projection y) c :=
          Or.inl ⟨congrArg Prod.fst hbits, hcost⟩
        exact ⟨c + d, WalkCost.next hstep hd, add_le_add_left hle _⟩
      · have heq : projection x = projection y := by
          exact Prod.ext hheight hbits
        refine ⟨d, ?_, ?_⟩
        · rw [heq]
          exact hd
        · calc
            d = 0 + d := (zero_add _).symm
            _ ≤ c + e := add_le_add (zero_le c) hle
      · have hstep : horizontalGateStep m (projection x) (projection y) c :=
          Or.inr ⟨hheight, hcost, ⟨k, hk, hflip⟩⟩
        exact ⟨c + d, WalkCost.next hstep hd, add_le_add_left hle _⟩

theorem horizontal_distance_le_full {m : ℕ}
    (x y : FiniteState m) :
    walkDistance (horizontalGateStep m) (projection x) (projection y) ≤
      walkDistance (finiteStep m) x y := by
  unfold walkDistance
  apply le_sInf
  intro c hc
  obtain ⟨d, hd, hle⟩ := project_walk hc
  exact (sInf_le ⟨d, hd⟩).trans hle

theorem full_distance_le_horizontal {m : ℕ}
    (x y : HeightBits m) (p : Phase) :
    walkDistance (finiteStep m) (withPhase x p) (withPhase y p) ≤
      walkDistance (horizontalGateStep m) x y := by
  unfold walkDistance
  apply le_sInf
  intro c hc
  exact sInf_le ⟨c, lift_walk p hc⟩

/-- Exact identification of the real, actual PR #171 finiteStep distance
at equal phases with the phase-free height+bit walk distance. -/
theorem finiteStep_same_phase_distance {m : ℕ}
    (x y : HeightBits m) (p : Phase) :
    walkDistance (finiteStep m) (withPhase x p) (withPhase y p) =
      walkDistance (horizontalGateStep m) x y := by
  apply le_antisymm
  · exact full_distance_le_horizontal x y p
  · simpa [projection_withPhase] using
      (horizontal_distance_le_full (withPhase x p) (withPhase y p))

#print axioms lift_step
#print axioms lift_walk
#print axioms project_walk
#print axioms horizontal_distance_le_full
#print axioms full_distance_le_horizontal
#print axioms finiteStep_same_phase_distance

end ObservedSandpile.FiniteStepHorizontalBridge
