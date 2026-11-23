import Mathlib.Tactic
import Research.KKHopfSouthHomeo
import Research.KKHopfTwoSections

/-!
# Exact Hopf north/south transition on the entire overlap

On S², for -1<w<1, the local square-root sections N and S differ by
the *unique* unit phase C+iS, with
C=2u/(sqrt(2(1+w))*sqrt(2(1-w))),
S=-2v/(sqrt(2(1+w))*sqrt(2(1-w))).

This file proves the unit circle property and the four coordinates
of rotate(C,S,N)=S. The restriction to the actual overlap ensures
the square-root denominators are strictly positive.

It does NOT prove the topological degree/winding number or first
Chern class of the transition function.
-/
namespace KKHopfTransitionAlgebra
open KKHopfGlobalAlgebra

def formalNorth (u v w dn : ℝ) : X4 := fun i =>
  if i = 0 then (1+w)/dn else if i = 1 then 0
  else if i = 2 then u/dn else v/dn

def formalSouth (u v w ds : ℝ) : X4 := fun i =>
  if i = 0 then u/ds else if i = 1 then -v/ds
  else if i = 2 then (1-w)/ds else 0

def transitionC (u dn ds : ℝ) : ℝ := 2*u/(dn*ds)
def transitionS (v dn ds : ℝ) : ℝ := -2*v/(dn*ds)

/-- The north/south rational transition phase has unit norm for
square-root denominators obeying the two defining equations. -/
theorem transition_unit (u v w dn ds : ℝ)
    (hSphere : u^2+v^2+w^2=1)
    (hn : dn^2 = 2*(1+w))
    (hs : ds^2 = 2*(1-w))
    (hdn : dn ≠ 0) (hds : ds ≠ 0) :
    (transitionC u dn ds)^2 + (transitionS v dn ds)^2 = 1 := by
  have hprod : (dn*ds)^2 = 4*(u^2+v^2) := by
    calc
      _ = dn^2*ds^2 := by ring
      _ = (2*(1+w))*(2*(1-w)) := by rw [hn,hs]
      _ = 4*(u^2+v^2) := by nlinarith [hSphere]
  have hden : (dn*ds)^2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hdn hds)
  change (2*u/(dn*ds))^2 + (-2*v/(dn*ds))^2 = 1
  calc
    _ = 4*(u^2+v^2)/(dn*ds)^2 := by ring
    _ = (dn*ds)^2/(dn*ds)^2 := by rw [← hprod]
    _ = 1 := div_self hden

/-- All four component equations of the exact overlap rotation,
with no special restriction to the equator w=0. -/
theorem transition_reconstruct (u v w dn ds : ℝ)
    (hSphere : u^2+v^2+w^2=1)
    (hn : dn^2 = 2*(1+w))
    (hdn : dn ≠ 0) (hds : ds ≠ 0) :
    rotate (transitionC u dn ds) (transitionS v dn ds)
      (formalNorth u v w dn) = formalSouth u v w ds := by
  have hu : 2*u*(1+w) = u*dn^2 := by rw [hn]; ring
  have hv : 2*v*(1+w) = v*dn^2 := by rw [hn]; ring
  have hw : 2*(u^2+v^2) = (1-w)*dn^2 := by rw [hn]; nlinarith [hSphere]
  funext i
  fin_cases i
  · change (2*u/(dn*ds))*((1+w)/dn) - (-2*v/(dn*ds))*0 = u/ds
    field_simp [hdn,hds]
    nlinarith [hu]
  · change (-2*v/(dn*ds))*((1+w)/dn) + (2*u/(dn*ds))*0 = -v/ds
    field_simp [hdn,hds]
    nlinarith [hv]
  · change (2*u/(dn*ds))*(u/dn) - (-2*v/(dn*ds))*(v/dn) = (1-w)/ds
    field_simp [hdn,hds]
    nlinarith [hw]
  · change (-2*v/(dn*ds))*(u/dn) + (2*u/(dn*ds))*(v/dn) = 0
    field_simp [hdn,hds]
    ring

/-- Genuine sqrt-section identity valid on the whole connected
overlap of the north and south Hopf base patches. -/
theorem full_overlap_transition (u v w : ℝ)
    (hSphere : u^2+v^2+w^2=1)
    (hN : 0 < 1+w) (hS : 0 < 1-w) :
    let dn := Real.sqrt (2*(1+w))
    let ds := Real.sqrt (2*(1-w))
    (transitionC u dn ds)^2 + (transitionS v dn ds)^2 = 1 ∧
    rotate (transitionC u dn ds) (transitionS v dn ds)
      (KKHopfSurjective.northVec u v w) =
      KKHopfTwoSections.southVec u v w := by
  let dn : ℝ := Real.sqrt (2*(1+w))
  let ds : ℝ := Real.sqrt (2*(1-w))
  have hnpos : 0 < 2*(1+w) := mul_pos (by norm_num) hN
  have hspos : 0 < 2*(1-w) := mul_pos (by norm_num) hS
  have hdn : dn ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
  have hds : ds ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hspos)
  have hn2 : dn^2 = 2*(1+w) := Real.sq_sqrt (le_of_lt hnpos)
  have hs2 : ds^2 = 2*(1-w) := Real.sq_sqrt (le_of_lt hspos)
  have hu := transition_unit u v w dn ds hSphere hn2 hs2 hdn hds
  have hr := transition_reconstruct u v w dn ds hSphere hn2 hdn hds
  refine ⟨hu, ?_⟩
  change rotate (transitionC u dn ds) (transitionS v dn ds)
    (formalNorth u v w dn) = formalSouth u v w ds
  exact hr

end KKHopfTransitionAlgebra
