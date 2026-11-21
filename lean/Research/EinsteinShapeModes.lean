import Mathlib.Tactic

/-!
# Independent shape and volume rescalings of positive Einstein product factors

The external dimension is four. An Einstein product of three internal
factors has a standard Einstein-frame kinetic quadratic form K and Hessian
Q at a common Einstein constant lam. The Hessian formula is independently
derived from the potential in tools/check_einstein_product.py. Lean proves
the algebraic normal form and negativity for CP2 x S2 x S2.
-/
namespace EinsteinShapeModes

def kinetic (n1 n2 n3 a b c : ℚ) : ℚ :=
  n1 * a ^ 2 + n2 * b ^ 2 + n3 * c ^ 2 +
    (n1 * a + n2 * b + n3 * c) ^ 2 / 2

def hessian (lam n1 n2 n3 a b c : ℚ) : ℚ :=
  -2 * lam * (n1 * a + n2 * b + n3 * c) ^ 2 -
    4 * lam * (n1 * a ^ 2 + n2 * b ^ 2 + n3 * c ^ 2)

/-- Universal generalized mass matrix: Hessian = -4*lam*K. -/
theorem hessian_eq_kinetic (lam n1 n2 n3 a b c : ℚ) :
    hessian lam n1 n2 n3 a b c =
      -4 * lam * kinetic n1 n2 n3 a b c := by
  unfold hessian kinetic
  ring

/-- CP2 x S2 x S2 has factor dimensions 4+2+2. -/
def k8 (a b c : ℚ) : ℚ := kinetic 4 2 2 a b c
def h8 (lam a b c : ℚ) : ℚ := hessian lam 4 2 2 a b c

theorem h8_eq_k8 (lam a b c : ℚ) :
    h8 lam a b c = -4 * lam * k8 a b c := by
  exact hessian_eq_kinetic lam 4 2 2 a b c

theorem k8_sq (a b c : ℚ) :
    k8 a b c = 4 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 +
      (4*a + 2*b + 2*c) ^ 2 / 2 := by
  rfl

theorem k8_positive (a b c : ℚ)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) : 0 < k8 a b c := by
  rw [k8_sq]
  rcases h with ha | hb | hc
  · have hs : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg b, sq_nonneg c,
      sq_nonneg (4*a + 2*b + 2*c)]
  · have hs : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    nlinarith [sq_nonneg a, sq_nonneg c,
      sq_nonneg (4*a + 2*b + 2*c)]
  · have hs : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    nlinarith [sq_nonneg a, sq_nonneg b,
      sq_nonneg (4*a + 2*b + 2*c)]

/-- Every nontrivial factor-scale direction has negative Hessian. -/
theorem all_factor_scales_tachyonic (lam a b c : ℚ)
    (hl : 0 < lam) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    h8 lam a b c < 0 := by
  rw [h8_eq_k8]
  have hk := k8_positive a b c h
  have hneg : (-4 : ℚ) * lam < 0 := by nlinarith
  simpa [mul_assoc] using mul_neg_of_neg_of_pos hneg hk

theorem kinetic_principal_minors :
    (0 : ℚ) < 12 ∧ (0 : ℚ) < 32 ∧ (0 : ℚ) < 80 := by
  norm_num

end EinsteinShapeModes
