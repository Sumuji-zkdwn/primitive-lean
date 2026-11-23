import Std

/-!
PRIMITIVE FOUNDRY: finite accounting and transport laws.

The browser factory implements an independent JavaScript engine. This Lean file
formalizes conservative local moves and recipes as a mathematical kernel.
It does not claim to verify the whole browser simulation or its scheduling,
energy model or interface.

The research tree in tech.json references the actual file-level proof
dependency inventory; tech effects are not consequences of those theorems.
-/

namespace PrimitiveFoundry

structure Bin where
  source : Nat
  target : Nat
  deriving Repr, DecidableEq

/-- A conservative one-item conveyor transfer. An empty source cannot move. -/
def beltStep (b : Bin) : Bin :=
  if 0 < b.source
  then ⟨b.source - 1, b.target + 1⟩
  else b

/-- A one-item transfer preserves total item count. -/
theorem beltStep_preserves_total (b : Bin) :
    (beltStep b).source + (beltStep b).target = b.source + b.target := by
  by_cases h : 0 < b.source
  · simp only [beltStep, if_pos h]
    omega
  · simp [beltStep, h]

/-- Empty source cells do not spontaneously manufacture items. -/
theorem beltStep_empty (b : Bin) (h : b.source = 0) :
    beltStep b = b := by
  simp [beltStep, h]

/-- The same local accounting applies to miner reserve and mined ore stock. -/
def miningStep (b : Bin) : Bin :=
  if 0 < b.source
  then ⟨b.source - 1, b.target + 1⟩
  else b

theorem miningStep_preserves_total (b : Bin) :
    (miningStep b).source + (miningStep b).target = b.source + b.target := by
  unfold miningStep
  by_cases h : 0 < b.source
  · simp only [if_pos h]; omega
  · simp [h]

/-- One ore is converted to one plate; no conversion without ore. -/
def furnaceStep (b : Bin) : Bin :=
  if 0 < b.source then ⟨b.source - 1,b.target + 1⟩ else b

theorem furnaceStep_preserves_units (b : Bin) :
    (furnaceStep b).source + (furnaceStep b).target = b.source + b.target := by
  unfold furnaceStep
  by_cases h : 0 < b.source
  · simp only [if_pos h]; omega
  · simp [h]

structure Assembly where
  gears : Nat
  wires : Nat
  circuits : Nat
  deriving Repr, DecidableEq

/-- The explicit game recipe: one gear plus two wires gives one circuit. -/
def assemble (a : Assembly) : Assembly :=
  if 0 < a.gears ∧ 2 ≤ a.wires
  then ⟨a.gears - 1, a.wires - 2, a.circuits + 1⟩
  else a

/-- With the ingredient-weighted count, production is conservative.
This is a recipe bookkeeping law, NOT an energy conservation statement. -/
theorem assemble_preserves_ingredients (a : Assembly) :
    2 * (assemble a).gears + (assemble a).wires + 4 * (assemble a).circuits =
    2 * a.gears + a.wires + 4 * a.circuits := by
  unfold assemble
  by_cases h : 0 < a.gears ∧ 2 ≤ a.wires
  · simp only [if_pos h]
    omega
  · simp [h]

theorem assemble_needs_inputs (a : Assembly)
    (h : a.gears = 0 ∨ a.wires < 2) : assemble a = a := by
  unfold assemble
  have notReady : ¬ (0 < a.gears ∧ 2 ≤ a.wires) := by
    rcases h with hG | hW
    · omega
    · omega
  simp [notReady]

/-- A finite fact about an actual refinery's data domain. -/
example : beltStep ⟨5, 2⟩ = ⟨4, 3⟩ := by decide
example : assemble ⟨3, 6, 0⟩ = ⟨2, 4, 1⟩ := by decide
example : assemble ⟨0, 6, 0⟩ = ⟨0, 6, 0⟩ := by decide

#print axioms beltStep_preserves_total
#print axioms assemble_preserves_ingredients
#print axioms assemble_needs_inputs

end PrimitiveFoundry
