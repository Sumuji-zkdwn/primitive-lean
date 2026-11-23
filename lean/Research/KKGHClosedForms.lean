import Mathlib.Tactic
/-!
# Universal GH 2-form closure in an arbitrary local first jet
The three self-dual candidate 2-forms are
 Omega_i = (dpsi+A) wedge dx_i - H dx_j wedge dx_k.
Their exterior derivatives vanish if curl(A)=grad(H).
This is a full 3*4^3 finite component identity; it is not yet
the global differential-geometric hyperkaehler-to-Ricci theorem.
-/
namespace KKGHClosedForms
abbrev V3 := Fin 3 → ℚ
abbrev V4 := Fin 4 → ℚ
abbrev AJet := Fin 3 → Fin 3 → ℚ

def e (k : Fin 4) : V4 := fun j => if k=j then 1 else 0

def theta (A : V3) : V4 := fun j =>
  if j = 0 then A 0 else if j = 1 then A 1 else if j = 2 then A 2 else 1

def dtheta (DA : AJet) (k : Fin 4) : V4 := fun j =>
  if k = 0 then
    if j = 0 then DA 0 0 else if j = 1 then DA 0 1
    else if j = 2 then DA 0 2 else 0
  else if k = 1 then
    if j = 0 then DA 1 0 else if j = 1 then DA 1 1
    else if j = 2 then DA 1 2 else 0
  else if k = 2 then
    if j = 0 then DA 2 0 else if j = 1 then DA 2 1
    else if j = 2 then DA 2 2 else 0
  else 0

def dH (p : V3) (k : Fin 4) : ℚ :=
  if k = 0 then p 0 else if k = 1 then p 1 else if k = 2 then p 2 else 0

def wedge (u v : V4) (i j : Fin 4) : ℚ := u i*v j-u j*v i

def omega (axis : Fin 3) (H : ℚ) (A : V3) (i j : Fin 4) : ℚ :=
  if axis=0 then wedge (theta A) (e 0) i j - H*wedge (e 1) (e 2) i j
  else if axis=1 then wedge (theta A) (e 1) i j - H*wedge (e 2) (e 0) i j
  else wedge (theta A) (e 2) i j - H*wedge (e 0) (e 1) i j

def partialOmega (axis : Fin 3) (p : V3) (DA : AJet)
    (direction i j : Fin 4) : ℚ :=
  if axis=0 then wedge (dtheta DA direction) (e 0) i j -
      dH p direction*wedge (e 1) (e 2) i j
  else if axis=1 then wedge (dtheta DA direction) (e 1) i j -
      dH p direction*wedge (e 2) (e 0) i j
  else wedge (dtheta DA direction) (e 2) i j -
      dH p direction*wedge (e 0) (e 1) i j

def exterior (axis : Fin 3) (p : V3) (DA : AJet)
    (i j k : Fin 4) : ℚ :=
  partialOmega axis p DA i j k +
  partialOmega axis p DA j k i +
  partialOmega axis p DA k i j

def curlX (DA : AJet) : ℚ := DA 1 2 - DA 2 1
def curlY (DA : AJet) : ℚ := DA 2 0 - DA 0 2
def curlZ (DA : AJet) : ℚ := DA 0 1 - DA 1 0

theorem all_three_forms_closed (p : V3) (DA : AJet)
    (hx : curlX DA = p 0) (hy : curlY DA = p 1)
    (hz : curlZ DA = p 2) :
    ∀ axis : Fin 3, ∀ i j k : Fin 4, exterior axis p DA i j k = 0 := by
  intro axis i j k
  fin_cases axis <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [exterior, partialOmega, dH, dtheta, e, wedge,
      curlX, curlY, curlZ] at * <;> linarith

end KKGHClosedForms
