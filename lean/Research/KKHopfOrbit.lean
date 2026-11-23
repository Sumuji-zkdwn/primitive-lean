import Mathlib.Tactic
import Research.KKHopfGlobalAlgebra

/-!
# Hopf fibres are exactly unit-circle orbits on S³: a polynomial-algebra bridge

This is set-theoretic fibre completeness, not a smooth manifold quotient,
a Chern degree computation, or an arbitrary GH curvature theorem.
-/
namespace KKHopfOrbit

open KKHopfGlobalAlgebra

/-- Explicit phase reconstruction on the chart where the first complex
coordinate is nonzero. The variables are all arbitrary real scalars. -/
theorem phase_from_first
    (a b c d e f g h : ℝ)
    (ha : a^2+b^2 ≠ 0)
    (h0 : a^2+b^2 = e^2+f^2)
    (hx : a*c+b*d = e*g+f*h)
    (hy : a*d-b*c = e*h-f*g) :
    ∃ C S : ℝ,
      C^2+S^2=1 ∧
      C*a-S*b=e ∧ S*a+C*b=f ∧
      C*c-S*d=g ∧ S*c+C*d=h := by
  let den : ℝ := a^2+b^2
  have hden : den ≠ 0 := ha
  let C : ℝ := (a*e+b*f)/den
  let S : ℝ := (a*f-b*e)/den
  have hc0 : (a*e+b*f)*a-(a*f-b*e)*b=den*e := by
    dsimp [den]
    ring
  have hs0 : (a*f-b*e)*a+(a*e+b*f)*b=den*f := by
    dsimp [den]
    ring
  have hc1 : (a*e+b*f)*c-(a*f-b*e)*d=den*g := by
    calc
      _ = e*(a*c+b*d)-f*(a*d-b*c) := by ring
      _ = e*(e*g+f*h)-f*(e*h-f*g) := by rw [hx,hy]
      _ = (e^2+f^2)*g := by ring
      _ = den*g := by rw [←h0]; rfl
  have hs1 : (a*f-b*e)*c+(a*e+b*f)*d=den*h := by
    calc
      _ = f*(a*c+b*d)+e*(a*d-b*c) := by ring
      _ = f*(e*g+f*h)+e*(e*h-f*g) := by rw [hx,hy]
      _ = (e^2+f^2)*h := by ring
      _ = den*h := by rw [←h0]; rfl
  have hnorm : (a*e+b*f)^2+(a*f-b*e)^2=den^2 := by
    calc
      _ = (a^2+b^2)*(e^2+f^2) := by ring
      _ = den^2 := by rw [←h0]; dsimp [den]; ring
  refine ⟨C,S,?_,?_,?_,?_,?_⟩
  · dsimp [C,S]
    calc
      ((a*e+b*f)/den)^2+((a*f-b*e)/den)^2 =
          ((a*e+b*f)^2+(a*f-b*e)^2)/(den^2) := by ring
      _ = den^2/den^2 := by rw [hnorm]
      _ = 1 := by field_simp [hden]
  · dsimp [C,S]
    calc
      (a*e+b*f)/den*a-(a*f-b*e)/den*b =
          ((a*e+b*f)*a-(a*f-b*e)*b)/den := by ring
      _ = den*e/den := by rw [hc0]
      _ = e := by field_simp [hden]
  · dsimp [C,S]
    calc
      (a*f-b*e)/den*a+(a*e+b*f)/den*b =
          ((a*f-b*e)*a+(a*e+b*f)*b)/den := by ring
      _ = den*f/den := by rw [hs0]
      _ = f := by field_simp [hden]
  · dsimp [C,S]
    calc
      (a*e+b*f)/den*c-(a*f-b*e)/den*d =
          ((a*e+b*f)*c-(a*f-b*e)*d)/den := by ring
      _ = den*g/den := by rw [hc1]
      _ = g := by field_simp [hden]
  · dsimp [C,S]
    calc
      (a*f-b*e)/den*c+(a*e+b*f)/den*d =
          ((a*f-b*e)*c+(a*e+b*f)*d)/den := by ring
      _ = den*h/den := by rw [hs1]
      _ = h := by field_simp [hden]

/-- On the unit three-sphere, equality of the Hopf projections implies
membership in the same diagonal unit-circle orbit, including both poles. -/
theorem same_hopf_implies_unit_rotation
    (X Y : X4)
    (hX : radiusSq X = 1) (hY : radiusSq Y = 1)
    (hx : hopfX X = hopfX Y)
    (hy : hopfY X = hopfY Y)
    (hz : hopfZ X = hopfZ Y) :
    ∃ C S : ℝ, C^2+S^2=1 ∧ rotate C S X = Y := by
  have hfirst : X 0^2+X 1^2=Y 0^2+Y 1^2 := by
    have hr : X 0^2+X 1^2+X 2^2+X 3^2 =
       Y 0^2+Y 1^2+Y 2^2+Y 3^2 := by
      calc
        _ = radiusSq X := by rfl
        _ = radiusSq Y := by rw [hX,hY]
        _ = _ := by rfl
    have hz' : X 0^2+X 1^2-X 2^2-X 3^2 =
       Y 0^2+Y 1^2-Y 2^2-Y 3^2 := by simpa [hopfZ] using hz
    linarith
  have hsecond : X 2^2+X 3^2=Y 2^2+Y 3^2 := by
    have hr : X 0^2+X 1^2+X 2^2+X 3^2 =
       Y 0^2+Y 1^2+Y 2^2+Y 3^2 := by
      simpa [radiusSq] using (hX.trans hY.symm)
    linarith
  have hcross : X 0*X 2+X 1*X 3 = Y 0*Y 2+Y 1*Y 3 := by
    have hh : 2*(X 0*X 2+X 1*X 3)=2*(Y 0*Y 2+Y 1*Y 3) := by
      simpa [hopfX] using hx
    linarith
  have hcross2 : X 0*X 3-X 1*X 2 = Y 0*Y 3-Y 1*Y 2 := by
    have hh : 2*(X 0*X 3-X 1*X 2)=2*(Y 0*Y 3-Y 1*Y 2) := by
      simpa [hopfY] using hy
    linarith
  by_cases h0 : X 0^2+X 1^2 ≠ 0
  · obtain ⟨C,S,hunit,hc0,hs0,hc1,hs1⟩ :=
      phase_from_first (X 0) (X 1) (X 2) (X 3)
        (Y 0) (Y 1) (Y 2) (Y 3) h0 hfirst hcross hcross2
    refine ⟨C,S,hunit,?_⟩
    funext i
    fin_cases i <;> simp [rotate] <;> assumption
  · have hz0 : X 0 = 0 ∧ X 1 = 0 := by
      have hp : X 0^2+X 1^2=0 := by simpa using h0
      constructor <;> nlinarith [sq_nonneg (X 0),sq_nonneg (X 1)]
    have hy0 : Y 0 = 0 ∧ Y 1 = 0 := by
      have hp : Y 0^2+Y 1^2=0 := by rw [←hfirst]; simpa [hz0.1,hz0.2]
      constructor <;> nlinarith [sq_nonneg (Y 0),sq_nonneg (Y 1)]
    have h2 : X 2^2+X 3^2 ≠ 0 := by
      intro hn
      have hp : X 2^2+X 3^2=0 := by simpa using hn
      have hxnorm := hX
      simp [radiusSq,hz0.1,hz0.2] at hxnorm
      linarith
    obtain ⟨C,S,hunit,hc2,hs2,hc0,hs0⟩ :=
      phase_from_first (X 2) (X 3) (X 0) (X 1)
        (Y 2) (Y 3) (Y 0) (Y 1) h2 hsecond
        (by nlinarith [hcross]) (by nlinarith [hcross2])
    refine ⟨C,S,hunit,?_⟩
    funext i
    fin_cases i <;> simp [rotate,hz0.1,hz0.2,hy0.1,hy0.2] <;> assumption

/-- Exact characterization of Hopf fibres, beyond mere invariance. -/
theorem same_hopf_iff_circle_orbit
    (X Y : X4) (hX : radiusSq X = 1) (hY : radiusSq Y = 1) :
    (hopfX X = hopfX Y ∧
     hopfY X = hopfY Y ∧
     hopfZ X = hopfZ Y) ↔
    ∃ C S : ℝ, C^2+S^2=1 ∧ rotate C S X = Y := by
  constructor
  · rintro ⟨hx,hy,hz⟩
    exact same_hopf_implies_unit_rotation X Y hX hY hx hy hz
  · rintro ⟨C,S,hunit,hrotate⟩
    have hi := hopf_unit_circle_invariant C S X hunit
    rw [←hrotate]
    exact ⟨hi.1.symm, hi.2.1.symm, hi.2.2.1.symm⟩

end KKHopfOrbit
