/-!
# Rule 481: local reflection/complement symmetry and a toroidal witness

This encodes the five-cell von Neumann, outer-totalistic binary rule.
A neighbor is weighted 2 and the center is weighted 1.  Bits
0,5,6,7,8 (of the rule number 481) produce True.  The finite
3x3 torus is a symmetry/periodicity witness, NOT the growing
infinite lattice from OEIS A272457 (34634 at its reported index).
-/

noncomputable section

namespace LinearInputRule481

def bit (b : Bool) : ℕ := if b then 1 else 0

def rule (c n e s w : Bool) : Bool :=
  let score := bit c + 2 * (bit n + bit e + bit s + bit w)
  decide (score = 0 ∨ score = 5 ∨ score = 6 ∨ score = 7 ∨ score = 8)

/-- Swapping east/west neighbors is a reflection symmetry. -/
theorem reflect_ew (c n e s w : Bool) :
    rule c n e s w = rule c n w s e := by
  cases c <;> cases n <;> cases e <;> cases s <;> cases w <;> decide

/-- Swapping north/south neighbors is a reflection symmetry. -/
theorem reflect_ns (c n e s w : Bool) :
    rule c n e s w = rule c s e n w := by
  cases c <;> cases n <;> cases e <;> cases s <;> cases w <;> decide

/-- Simultaneous complementation of all five inputs complements the output. -/
theorem complement (c n e s w : Bool) :
    rule (!c) (!n) (!e) (!s) (!w) = !(rule c n e s w) := by
  cases c <;> cases n <;> cases e <;> cases s <;> cases w <;> decide

theorem all_zero_birth : rule false false false false false = true := by decide
theorem all_one_death : rule true true true true true = false := by decide

/-- A small periodic arena, deliberately different from the growing OEIS grid. -/
abbrev Grid := ZMod 3 → ZMod 3 → Bool

def mirrorNS (g : Grid) : Grid := fun i j => g (-i) j

def solid (b : Bool) : Grid := fun _ _ => b

def step (g : Grid) : Grid := fun i j =>
  rule (g i j) (g (i - 1) j) (g i (j + 1)) (g (i + 1) j) (g i (j - 1))

theorem mirror_involutive (g : Grid) : mirrorNS (mirrorNS g) = g := by
  funext i j
  simp [mirrorNS]

/-- The global synchronous update is equivariant for a spatial mirror. -/
theorem step_mirror (g : Grid) : step (mirrorNS g) = mirrorNS (step g) := by
  funext i j
  change rule (g (-i) j) (g (-(i - 1)) j) (g (-i) (j + 1))
      (g (-(i + 1)) j) (g (-i) (j - 1)) =
    rule (g (-i) j) (g (-i - 1) j) (g (-i) (j + 1))
      (g (-i + 1) j) (g (-i) (j - 1))
  have hn : -(i - 1) = -i + 1 := by ring
  have hs : -(i + 1) = -i - 1 := by ring
  rw [hn, hs]
  exact reflect_ns (g (-i) j) (g (-i + 1) j) (g (-i) (j + 1))
    (g (-i - 1) j) (g (-i) (j - 1))

/-- Instantiation of the generic symmetry-preservation theorem from F0 descent. -/
theorem step_preserves_mirror (g : Grid) (hg : mirrorNS g = g) :
    mirrorNS (step g) = step g := by
  exact LinearInputF0Descent.equivariant_preserves_fixed
    (M := mirrorNS) (U := step) (fun x => step_mirror x) hg

theorem step_solid_false : step (solid false) = solid true := by
  funext i j
  rfl

theorem step_solid_true : step (solid true) = solid false := by
  funext i j
  rfl

theorem step_two_cycle :
    step (step (solid false)) = solid false := by
  rw [step_solid_false, step_solid_true]

/-- The Rule 481 update is not itself an F0-style idempotent forgetting. -/
theorem step_not_idempotent : ¬ LinearInputF0.Idempotent step := by
  intro h
  have he := h (solid false)
  rw [step_solid_false, step_solid_true] at he
  have hb := congrFun (congrFun he (0 : ZMod 3)) (0 : ZMod 3)
  cases hb

end LinearInputRule481
