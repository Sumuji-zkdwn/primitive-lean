/-!
# Hull inflation under volume-preserving symmetries: a finite countermodel

The issue is NOT the same as transport of a single region. Even when a
symmetry preserves each individual region's volume, the hull of the union
of several images may have strictly larger volume.

The rectangle model uses coordinatewise joins and natural-number area.
It is a counterexample to a general inference, NOT a model of a Hodge
theater, a p-adic log-shell, or a proof that IUT Ind2 defects are positive.
-/

namespace LinearInputPilotHullInflation

structure Rect where
  width : ℕ
  height : ℕ
deriving DecidableEq, Repr

def area (r : Rect) : ℕ := r.width * r.height

/-- Swapping coordinates preserves the individual area's value. -/
def swap (r : Rect) : Rect := ⟨r.height, r.width⟩

/-- Coordinatewise smallest containing rectangle for two rectangles. -/
def hull (a b : Rect) : Rect :=
  ⟨max a.width b.width, max a.height b.height⟩

theorem swap_preserves_area (r : Rect) : area (swap r) = area r := by
  simp [area, swap, mul_comm]

theorem swap_involutive (r : Rect) : swap (swap r) = r := by
  cases r
  rfl

/-- A hull of two rectangle regions has at least the area of either one. -/
theorem hull_area_ge_left (a b : Rect) : area a ≤ area (hull a b) := by
  change a.width * a.height ≤
    max a.width b.width * max a.height b.height
  exact Nat.mul_le_mul (le_max_left _ _) (le_max_left _ _)

theorem hull_area_ge_right (a b : Rect) : area b ≤ area (hull a b) := by
  change b.width * b.height ≤
    max a.width b.width * max a.height b.height
  exact Nat.mul_le_mul (le_max_right _ _) (le_max_right _ _)

/-- A 2-by-1 rectangle and its swapped image have equal area 2, but
their coordinatewise hull has area 4. -/
def witness : Rect := ⟨2, 1⟩

theorem witness_equal_areas : area (swap witness) = area witness :=
  swap_preserves_area witness

theorem witness_hull_area_is_four :
    area (hull witness (swap witness)) = 4 := by
  decide

theorem witness_individual_area_is_two : area witness = 2 := by
  decide

/-- Exact formal counterexample to the invalid step: every individual
volume is preserved, therefore the hull over the orbit preserves volume. -/
theorem volume_preserving_hull_can_inflate :
    ∃ r : Rect,
      area (swap r) = area r ∧
      area r < area (hull r (swap r)) := by
  refine ⟨witness, swap_preserves_area witness, ?_⟩
  decide

/-- Inflation is not automatic: square rectangles are fixed by the swap. -/
theorem square_orbit_no_inflation (n : ℕ) :
    area (hull ⟨n, n⟩ (swap ⟨n, n⟩)) = area ⟨n, n⟩ := by
  simp [hull, swap, area]

end LinearInputPilotHullInflation
