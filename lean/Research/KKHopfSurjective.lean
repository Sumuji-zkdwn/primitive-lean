import Mathlib.Tactic
import Research.KKHopfGlobalAlgebra

/-!
# Hopf projection covers S²: explicit local sections

A constructive, set-theoretic surjectivity theorem using a real square-root
chart and a separate south-pole case. This is not a smooth quotient theorem.
The base and total sphere conditions are equations in R³ and R⁴.
-/
namespace KKHopfSurjective
open KKHopfGlobalAlgebra

/-- A north stereographic section; w ≠ -1 and u²+v²+w²=1. -/
noncomputable def northVec (u v w : ℝ) : X4 :=
  let d := Real.sqrt (2*(1+w))
  fun i => if i=0 then (1+w)/d else if i=1 then 0
           else if i=2 then u/d else v/d

/-- A lift of the south pole of S². -/
def southPole : X4 := fun i => if i=2 then 1 else 0

theorem southPole_data :
    radiusSq southPole = 1 ∧
    hopfX southPole = 0 ∧
    hopfY southPole = 0 ∧
    hopfZ southPole = -1 := by
  norm_num [southPole, radiusSq, hopfX, hopfY, hopfZ]

/-- The explicit formula gives a unit 3-sphere element over every
point of S² other than the south pole. -/
theorem north_chart (u v w : ℝ)
    (hsphere : u^2+v^2+w^2=1) (hpos : 0 < 1+w) :
    radiusSq (northVec u v w) = 1 ∧
    hopfX (northVec u v w) = u ∧
    hopfY (northVec u v w) = v ∧
    hopfZ (northVec u v w) = w := by
  let d : ℝ := Real.sqrt (2*(1+w))
  have harg : 0 ≤ 2*(1+w) := by positivity
  have hdpos : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hd2 : d^2 = 2*(1+w) := Real.sq_sqrt harg
  have hwne : 1+w ≠ 0 := ne_of_gt hpos
  have hsum : (1+w)^2+u^2+v^2=2*(1+w) := by nlinarith [hsphere]
  have hdiff : (1+w)^2-u^2-v^2=2*w*(1+w) := by nlinarith [hsphere]
  refine ⟨?_,?_,?_,?_⟩
  · change ((1+w)/d)^2 + (0:ℝ)^2 + (u/d)^2 + (v/d)^2 = 1
    calc
      _ = ((1+w)^2+u^2+v^2)/d^2 := by ring
      _ = 1 := by rw [hsum, hd2]; field_simp [hwne]
  · change 2*((1+w)/d*(u/d)+(0:ℝ)*(v/d))=u
    calc
      _ = (2*(1+w)*u)/d^2 := by ring
      _ = u := by rw [hd2]; field_simp [hwne]
  · change 2*((1+w)/d*(v/d)-(0:ℝ)*(u/d))=v
    calc
      _ = (2*(1+w)*v)/d^2 := by ring
      _ = v := by rw [hd2]; field_simp [hwne]
  · change ((1+w)/d)^2 + (0:ℝ)^2 - (u/d)^2-(v/d)^2 = w
    calc
      _ = ((1+w)^2-u^2-v^2)/d^2 := by ring
      _ = w := by rw [hdiff,hd2]; field_simp [hwne]

/-- The real polynomial Hopf map is surjective S³ → S². -/
theorem hopf_surjective_on_unit_spheres
    (u v w : ℝ) (hsphere : u^2+v^2+w^2=1) :
    ∃ X : X4, radiusSq X = 1 ∧
      hopfX X = u ∧ hopfY X = v ∧ hopfZ X = w := by
  by_cases hw : 1+w=0
  · have hwm : w=-1 := by linarith
    have hu : u=0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v=0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    refine ⟨southPole, ?_, ?_, ?_, ?_⟩
    · exact southPole_data.1
    · simpa [hu] using southPole_data.2.1
    · simpa [hv] using southPole_data.2.2.1
    · simpa [hwm] using southPole_data.2.2.2
  · have hpos : 0 < 1+w := by
      have hnonneg : 0 ≤ 1+w := by
        by_contra hneg
        have hlt : w < -1 := by linarith
        nlinarith [sq_nonneg u, sq_nonneg v]
      rcases lt_or_eq_of_le hnonneg with hp | he
      · exact hp
      · exact False.elim (hw he.symm)
    obtain ⟨hunit, hx, hy, hz⟩ := north_chart u v w hsphere hpos
    exact ⟨northVec u v w, hunit, hx, hy, hz⟩

end KKHopfSurjective
