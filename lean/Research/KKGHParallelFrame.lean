import Mathlib.Tactic
import Research.KKGHClosedForms

/-!
# The hyperkaehler frame-connection uniqueness linear algebra
The triple of standard anti-self-dual 2-forms is an orthonormal
basis. If their Levi-Civita SO(3)-connection 1-forms alpha,beta,gamma
satisfy the closed-form equations (three alternating 3-form equations),
then all 12 connection coefficients vanish.
This is pure finite algebra (a 12x12 matrix of determinant 16),
not a theorem that a particular smooth manifold has that connection.
-/
namespace KKGHParallelFrame
abbrev One := Fin 4 → ℚ

def omega0 (axis : Fin 3) (i j : Fin 4) : ℚ :=
  KKGHClosedForms.omega axis 1 (fun _ => 0) i j

def alt (v : One) (axis : Fin 3) (i j k : Fin 4) : ℚ :=
  v i*omega0 axis j k + v j*omega0 axis k i + v k*omega0 axis i j

/-- General uniqueness of the SO(3) connection given a closed quaternionic triple. -/
theorem connection_forms_vanish (a b c : One)
    (h₁ : ∀ i j k : Fin 4, alt a 1 i j k + alt b 2 i j k = 0)
    (h₂ : ∀ i j k : Fin 4, -alt a 0 i j k + alt c 2 i j k = 0)
    (h₃ : ∀ i j k : Fin 4, -alt b 0 i j k - alt c 1 i j k = 0) :
    a=0 ∧ b=0 ∧ c=0 := by
  have f1 := h₁ 0 1 2
  have f2 := h₁ 0 1 3
  have f3 := h₁ 0 2 3
  have f4 := h₁ 1 2 3
  have f5 := h₂ 0 1 2
  have f6 := h₂ 0 1 3
  have f7 := h₂ 0 2 3
  have f8 := h₂ 1 2 3
  have f9 := h₃ 0 1 2
  have f10 := h₃ 0 1 3
  have f11 := h₃ 0 2 3
  have f12 := h₃ 1 2 3
  simp [alt, omega0, KKGHClosedForms.omega, KKGHClosedForms.theta,
    KKGHClosedForms.wedge, KKGHClosedForms.e] at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  refine ⟨?_, ?_, ?_⟩
  all_goals
    funext i
    fin_cases i <;> norm_num <;>
      linarith [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12]

end KKGHParallelFrame
