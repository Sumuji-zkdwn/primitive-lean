import Mathlib.Tactic

/-!
# Gravity-only Einstein-product witness and its breathing-mode tachyon

Scope: algebraic certificates for product Einstein constants and the Taylor
coefficients of the four-dimensional Einstein-frame radion potential. The
geometric Ricci identities of de Sitter, spheres, and Fubini-Study CP2, and
the derivation of the reduced action, are external mathematical premises,
checked separately (for dS4 x S2) by SymPy or standard differential geometry.
This is NOT a kernel proof of complete 6D/12D differential equations,
fermion generation, or a stable compactification.
-/
namespace EinsteinProductRadion

/-- In 4+n dimensions with Ric(g)=lam*g, Einstein-Lambda requires
    Lambda=(n+2)*lam/2. -/
def cosmologicalConstant (n : ℕ) (lam : ℚ) : ℚ :=
  ((n : ℚ) + 2) * lam / 2

/-- Uniform volume mode kinetic coefficient in the 4D Einstein frame. -/
def kineticCoefficient (n : ℕ) : ℚ :=
  (n : ℚ) * ((n : ℚ) + 2) / 2

/-- Constant term of V(beta)=(n+2)*lam*exp(-n*beta)
    -n*lam*exp(-(n+2)*beta). -/
def potentialZero (n : ℕ) (lam : ℚ) : ℚ :=
  ((n : ℚ) + 2) * lam - (n : ℚ) * lam

/-- First derivative of the potential evaluated at beta=0. -/
def potentialPrimeZero (n : ℕ) (lam : ℚ) : ℚ :=
  -(n : ℚ) * ((n : ℚ) + 2) * lam +
    ((n : ℚ) + 2) * (n : ℚ) * lam

/-- Second derivative of the potential evaluated at beta=0. -/
def potentialSecondZero (n : ℕ) (lam : ℚ) : ℚ :=
  (n : ℚ) ^ 2 * ((n : ℚ) + 2) * lam -
    ((n : ℚ) + 2) ^ 2 * (n : ℚ) * lam

theorem potential_value (n : ℕ) (lam : ℚ) :
    potentialZero n lam = 2 * lam := by
  unfold potentialZero
  ring

theorem potential_stationary (n : ℕ) (lam : ℚ) :
    potentialPrimeZero n lam = 0 := by
  unfold potentialPrimeZero
  ring

theorem second_derivative_closed (n : ℕ) (lam : ℚ) :
    potentialSecondZero n lam =
      -2 * (n : ℚ) * ((n : ℚ) + 2) * lam := by
  unfold potentialSecondZero
  ring

theorem twice_kinetic_closed (n : ℕ) :
    2 * kineticCoefficient n = (n : ℚ) * ((n : ℚ) + 2) := by
  unfold kineticCoefficient
  ring

/-- For any positive internal dimension n, the canonically normalized
    radion mass squared equals -2*lam. -/
theorem radion_mass (n : ℕ) (hn : 0 < n) (lam : ℚ) :
    potentialSecondZero n lam / (2 * kineticCoefficient n) = -2 * lam := by
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hk : 2 * kineticCoefficient n ≠ 0 := by
    rw [twice_kinetic_closed]
    exact ne_of_gt (mul_pos hnq (by positivity))
  apply (div_eq_iff hk).2
  rw [second_derivative_closed, twice_kinetic_closed]
  ring

/-- In four external spacetime dimensions H²=lam/3, hence m²=-6H². -/
theorem mass_hubble (lam : ℚ) :
    -2 * lam = -6 * (lam / 3) := by ring

theorem radion_tachyonic (n : ℕ) (hn : 0 < n)
    (lam : ℚ) (hlam : 0 < lam) :
    potentialSecondZero n lam / (2 * kineticCoefficient n) < 0 := by
  rw [radion_mass n hn lam]
  linarith

/-- dS4(L²=3) x S2(a²=1) has common Einstein constant 1
    and solves Ric=2Lambda_6/(6-2)*g for Lambda_6=2. -/
theorem six_dimensional_factor_match :
    (3 : ℚ) / 3 = 1 / 1 ∧ cosmologicalConstant 2 1 = 2 := by
  norm_num [cosmologicalConstant]

/-- With FS normalization Ric(CP2,g_FS)=6g_FS,
    dS4(L²=3) x CP2(6*g_FS) x S2 x S2 has common
    Einstein constant 1, requiring Lambda_12=5. -/
theorem twelve_dimensional_factor_match :
    (3 : ℚ) / 3 = 6 / 6 ∧
    (6 : ℚ) / 6 = 1 / 1 ∧
    (1 : ℚ) / 1 = 1 / 1 ∧
    cosmologicalConstant 8 1 = 5 := by
  norm_num [cosmologicalConstant]

/-- Round S2 restores its SO3, not just U1: 8+3+3=14 vs 12. -/
theorem symmetry_enhancement :
    8 + 3 + 3 = (14 : ℕ) ∧ 8 + 3 + 1 = (12 : ℕ) := by
  omega

theorem two_examples_have_same_radion_mass :
    potentialSecondZero 2 1 / (2 * kineticCoefficient 2) = -2 ∧
    potentialSecondZero 8 1 / (2 * kineticCoefficient 8) = -2 := by
  constructor
  · simpa using radion_mass 2 (by decide) 1
  · simpa using radion_mass 8 (by decide) 1

end EinsteinProductRadion
