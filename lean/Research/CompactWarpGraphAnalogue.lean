import Mathlib.Tactic

/-!
# Finite harmonic obstruction and the role of boundaries

This is an exact 3-site graph analogue of the maximum-principle step used in
compact vacuum warped-product no-go arguments. The general theorem for all
finite connected graphs and the Riemannian Bochner theorem are not formalized
here; see the research note.
-/

namespace CompactWarpGraphAnalogue

abbrev Profile := Fin 3 → ℚ

/-- Nearest-neighbor graph Laplacian on the path 0--1--2. -/
def lap (u : Profile) (i : Fin 3) : ℚ :=
  if i = 0 then u 1 - u 0
  else if i = 1 then u 0 - 2 * u 1 + u 2
  else u 1 - u 2

/-- With no boundary and no source, every harmonic profile is constant. -/
theorem closed_harmonic_constant (u : Profile)
    (h : ∀ i, lap u i = 0) :
    u 0 = u 1 ∧ u 1 = u 2 := by
  have h0 : u 1 - u 0 = 0 := by simpa [lap] using h 0
  have h2 : u 1 - u 2 = 0 := by simpa [lap] using h 2
  constructor <;> linarith

/-- A fixed boundary permits a nonconstant function harmonic at the interior. -/
def boundaryProfile : Profile := fun i =>
  if i = 0 then 0 else if i = 1 then 1 else 2

theorem boundary_harmonic :
    lap boundaryProfile 1 = 0 ∧ boundaryProfile 0 ≠ boundaryProfile 2 := by
  constructor
  · norm_num [lap, boundaryProfile]
  · norm_num [boundaryProfile]

/-- The same nonconstant profile is not harmonic at every site. -/
theorem boundary_not_closed : lap boundaryProfile 0 ≠ 0 := by
  norm_num [lap, boundaryProfile]

end CompactWarpGraphAnalogue
