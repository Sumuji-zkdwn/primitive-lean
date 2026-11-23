import Std

/-!
Finite Lean law witnesses for PRIMITIVE / ROGUE 465.

The source catalog contains 465 actual original Lean theorem declarations
(Elastica 214 and LinearInput 251). This file independently checks discrete
instances of some gameplay laws. It does not verify the JavaScript runtime,
nor does the original theorem corpus imply the balancing rules for items.
-/

namespace Rogue465

/-- Integer instance of E(u,z) = A(z) - u*X(z). -/
def observation (A X u : Int) : Int := A - u * X

/-- Two measurements recover a hidden coordinate. -/
theorem two_probe_recovers (A X : Int) :
    observation A X 0 - observation A X 1 = X := by
  simp [observation]
  omega

/-- Travel in a signed two-sheet lift changes the sheet by XOR. -/
def signedTravel (layer flip : Bool) : Bool := xor layer flip

theorem travel_twice (layer flip : Bool) :
    signedTravel (signedTravel layer flip) flip = layer := by
  cases layer <;> cases flip <;> decide

theorem positive_edge_preserves_layer (layer : Bool) :
    signedTravel layer false = layer := by
  cases layer <;> decide

theorem negative_edge_switches_layer (layer : Bool) :
    signedTravel layer true = !layer := by
  cases layer <;> decide

def middleParity (e2 e3 : Bool) : Bool := xor e2 e3

theorem flipping_one_middle_edge_changes_parity (a b : Bool) :
    middleParity a (!b) = !(middleParity a b) := by
  cases a <;> cases b <;> decide

/-- A sandpile firing consumes four grains at its center. -/
def afterFiring (grains : Nat) : Nat := grains - 4

theorem firing_decreases (grains : Nat) :
    afterFiring grains ≤ grains := Nat.sub_le _ _

theorem four_grain_site_emits_four : afterFiring 4 = 0 := by decide

/-- Rule 481: weighted central bit 1, cardinal neighbors 2 each. -/
def localRule (c n e s w : Bool) : Bool :=
  let score : Nat :=
    (if c then 1 else 0) +
      2 * ((if n then 1 else 0) + (if e then 1 else 0) +
           (if s then 1 else 0) + (if w then 1 else 0))
  decide (score = 0 ∨ score = 5 ∨ score = 6 ∨ score = 7 ∨ score = 8)

theorem localRule_mirror (c n e s w : Bool) :
    localRule c n e s w = localRule c n w s e := by
  cases c <;> cases n <;> cases e <;> cases s <;> cases w <;> decide

theorem localRule_complement (c n e s w : Bool) :
    localRule (!c) (!n) (!e) (!s) (!w) = !(localRule c n e s w) := by
  cases c <;> cases n <;> cases e <;> cases s <;> cases w <;> decide

theorem localRule_two_cycle :
    localRule false false false false false = true ∧
    localRule true true true true true = false := by decide

/-- Fighting uses saturating subtraction rather than signed HP. -/
def wound (hp power : Nat) : Nat := hp - power

theorem wound_le_original (hp power : Nat) : wound hp power ≤ hp :=
  Nat.sub_le _ _

theorem wound_after_kill (hp : Nat) : wound hp hp = 0 := by simp [wound]

example : observation 11 (-2) 0 - observation 11 (-2) 1 = -2 := by decide
example : signedTravel false true = true := by decide

#print axioms two_probe_recovers
#print axioms localRule_complement
#print axioms wound_le_original

end Rogue465
