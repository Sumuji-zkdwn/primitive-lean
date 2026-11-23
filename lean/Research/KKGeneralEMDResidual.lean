import Mathlib.Tactic

/-!
# Universal algebraic on-shell bridge from local 5D Ricci residuals
# to 4D Einstein--Maxwell--dilaton residuals

This file proves the residual decomposition is an equivalence with no
implicit restriction to a magnetic solution. It takes the *geometric*
normal-coordinate/gauge-jet identity as an explicit hypothesis, rather
than claiming the metric-to-Ricci derivation has been proved by Lean.

The independent universal 2-jet checker computes the decomposition
from the 5D metric for arbitrary off-shell g4, A, q; see
check_emd_universal_jets.py. With E the 4D Ricci-form Einstein
residual, M the 4D Maxwell residual with one index lowered, and
S0=Box(log q)+q^-3 F²/4, the normal-gauge 5D Ricci components are
  R5_mn = E_mn - g_mn*S0/2,
  R5_m5 = -M_m/2, R5_55=S0/q^3.
The code below uses arbitrary four-dimensional g_mn and q != 0.
-/

namespace KKGeneralEMDResidual

abbrev BaseMetric := Matrix (Fin 4) (Fin 4) ℚ
abbrev Einstein := Matrix (Fin 4) (Fin 4) ℚ
abbrev Maxwell := Fin 4 → ℚ

/-- Abstract horizontal component in the gauge A(p)=0. -/
def horizontal (g : BaseMetric) (E : Einstein) (S : ℚ)
    (i j : Fin 4) : ℚ := E i j - g i j * S / 2

/-- Abstract mixed component, with lowered Maxwell residual. -/
def mixed (M : Maxwell) (i : Fin 4) : ℚ := -M i / 2

/-- Abstract vertical component, q=e^(phi/sqrt(3)) != 0. -/
def vertical (q S : ℚ) : ℚ := S / q^3

/-- Conversely, the 5D Ricci components in the normal/gauge frame
are all zero iff the *full* 4D EMD residuals vanish. This is a
universal finite-dimensional algebra statement conditional on the
geometric interpretation of the component functions. -/
theorem ricci_zero_iff_emd_zero
    (q : ℚ) (g : BaseMetric) (E : Einstein) (M : Maxwell) (S : ℚ)
    (hq : q ≠ 0) :
    ((∀ i j : Fin 4, horizontal g E S i j = 0) ∧
     (∀ i : Fin 4, mixed M i = 0) ∧ vertical q S = 0) ↔
    ((∀ i j : Fin 4, E i j = 0) ∧
     (∀ i : Fin 4, M i = 0) ∧ S = 0) := by
  constructor
  · rintro ⟨hE,hM,hS⟩
    have hSq : S = 0 := by
      have : S / q^3 = 0 := hS
      have hq3 : q^3 ≠ 0 := pow_ne_zero 3 hq
      exact (div_eq_zero_iff).mp this |>.resolve_right hq3
    refine ⟨?_, ?_, hSq⟩
    · intro i j
      have h := hE i j
      simpa [horizontal, hSq] using h
    · intro i
      have h := hM i
      simpa [mixed] using h
  · rintro ⟨hE,hM,hS⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      simp [horizontal, hE i j, hS]
    · intro i
      simp [mixed, hM i]
    · simp [vertical, hS]

end KKGeneralEMDResidual
