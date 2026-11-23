import Mathlib.Tactic

/-!
# Universal local Gibbons--Hawking monopole-jet certificates

This file proves the linear exterior-calculus algebra for arbitrary first
and second coordinate jets, NOT an unrestricted smooth Gibbons--Hawking
Ricci-flatness theorem. The full 25-component arbitrary harmonic 2-jet
calculation is performed independently by check_gh_universal_2jet.py.

Coordinates x,y,z, and arbitrary gradient (px,py,pz). The standard
canonical local gauge for a first jet is A = -(x cross grad(H))/2.
The exterior identity dA=*dH means curl(A)=grad(H), and commutation
of second partials entails div(curl A)=Delta H=0.
-/

namespace KKGeneralGHBoundary

/-- One component's second partial derivatives, indexed as (component,d1,d2). -/
abbrev SecondA := Fin 3 → Fin 3 → Fin 3 → ℚ

/-- Universal algebraic certificate: divergence of curl of any smooth
local vector potential is zero when mixed partial derivatives commute. -/
theorem div_curl_zero (ddA : SecondA)
    (hsym : ∀ c i j, ddA c i j = ddA c j i) :
    (ddA 2 0 1 - ddA 1 0 2) +
    (ddA 0 1 2 - ddA 2 1 0) +
    (ddA 1 2 0 - ddA 0 2 1) = 0 := by
  rw [hsym 2 0 1, hsym 0 1 2, hsym 1 2 0]
  ring

/-- The three equations grad(H)=curl(A) imply that the trace of the
Hessian vanishes at any point, provided the mixed partials commute.
Here the three diagonal Hessian components are the actual derivatives
of the components of the assumed curl(A)=grad(H) identity. -/
theorem monopole_equation_forces_harmonicity
    (ddA : SecondA) (hxx hyy hzz : ℚ)
    (hsym : ∀ c i j, ddA c i j = ddA c j i)
    (hx : hxx = ddA 2 0 1 - ddA 1 0 2)
    (hy : hyy = ddA 0 1 2 - ddA 2 1 0)
    (hz : hzz = ddA 1 2 0 - ddA 0 2 1) :
    hxx+hyy+hzz = 0 := by
  have hc := div_curl_zero ddA hsym
  rw [hx,hy,hz]
  exact hc

/-- First derivatives of A = -(x cross p)/2 at the origin, with
coordinate order (x,y,z). -/
def firstA (px py pz : ℚ) : Fin 3 → Fin 3 → ℚ :=
  fun i j =>
    if i = 0 then (if j = 0 then 0 else if j = 1 then -pz/2 else py/2)
    else if i = 1 then (if j = 0 then pz/2 else if j = 1 then 0 else -px/2)
    else (if j = 0 then -py/2 else if j = 1 then px/2 else 0)

/-- This construction has the required magnetic gradient in all
three directions, without assigning the curl as an independent field. -/
theorem canonical_curl_x (px py pz : ℚ) :
    firstA px py pz 2 1 - firstA px py pz 1 2 = px := by
  norm_num [firstA] <;> ring

theorem canonical_curl_y (px py pz : ℚ) :
    firstA px py pz 0 2 - firstA px py pz 2 0 = py := by
  norm_num [firstA] <;> ring

theorem canonical_curl_z (px py pz : ℚ) :
    firstA px py pz 1 0 - firstA px py pz 0 1 = pz := by
  norm_num [firstA] <;> ring

end KKGeneralGHBoundary
