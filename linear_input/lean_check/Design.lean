import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Linear input: an actual global-minimum certificate

This independent pilot proves statements about the explicit energy, rather than
assuming an energy-gap identity or a minimizer property. It does not extend the
existing Elastica library or claim a dynamical stability result.
-/

noncomputable section
namespace LinearInputDesign

def f (lam r u x : ℝ) : ℝ := lam * x ^ 4 / 4 + r * x ^ 2 / 2 - u * x

def E (lam r u x y : ℝ) : ℝ :=
  f lam r u x + (y - Real.sqrt 2 * x) ^ 2 / 2

def input (lam r a : ℝ) : ℝ := lam * a ^ 3 + r * a

/-- A global minimum means comparison with every point of the full plane. -/
def GlobalMin (lam r a : ℝ) : Prop :=
  ∀ x y : ℝ, E lam r (input lam r a) a (Real.sqrt 2 * a) ≤
    E lam r (input lam r a) x y

theorem scalar_gap (lam r a x : ℝ) :
    f lam r (input lam r a) x - f lam r (input lam r a) a =
      (x - a) ^ 2 * (lam / 4 * (x + a) ^ 2 + (lam * a ^ 2 + r) / 2) := by
  unfold f input
  ring

theorem energy_gap (lam r a x y : ℝ) :
    E lam r (input lam r a) x y - E lam r (input lam r a) a (Real.sqrt 2 * a) =
      (y - Real.sqrt 2 * x) ^ 2 / 2 +
        (x - a) ^ 2 * (lam / 4 * (x + a) ^ 2 + (lam * a ^ 2 + r) / 2) := by
  unfold E
  rw [sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
  linarith [scalar_gap lam r a x]

/-- A nonnegative certificate gives an actual global minimum. -/
theorem globalMin_of_margin {lam r a : ℝ} (hlam : 0 ≤ lam)
    (hmargin : 0 ≤ lam * a ^ 2 + r) : GlobalMin lam r a := by
  intro x y
  have hb : 0 ≤ lam / 4 * (x + a) ^ 2 + (lam * a ^ 2 + r) / 2 := by
    positivity
  have hp := mul_nonneg (sq_nonneg (x - a)) hb
  have ht : 0 ≤ (y - Real.sqrt 2 * x) ^ 2 / 2 := by positivity
  linarith [energy_gap lam r a x y]

/-- Necessity includes the degenerate target a = 0, via a concrete square-root witness. -/
theorem margin_of_globalMin {lam r a : ℝ} (hlam : 0 < lam)
    (hmin : GlobalMin lam r a) : 0 ≤ lam * a ^ 2 + r := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
    by_contra hn
    have hr : r < 0 := lt_of_not_ge hn
    let t : ℝ := Real.sqrt (-r / lam)
    have hq : 0 < -r / lam := div_pos (neg_pos.mpr hr) hlam
    have ht : 0 < t := Real.sqrt_pos.2 hq
    have ht2 : t ^ 2 = -r / lam := Real.sq_sqrt (le_of_lt hq)
    have hlt : lam * t ^ 2 = -r := by
      rw [ht2]
      field_simp
    have hg := energy_gap lam r 0 t (Real.sqrt 2 * t)
    have hm := hmin t (Real.sqrt 2 * t)
    simp only [mul_zero] at hm
    have hneg : t ^ 2 * r < 0 := mul_neg_of_pos_of_neg (sq_pos_of_pos ht) hr
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add,
      sub_zero, add_zero, mul_zero] at hg
    nlinarith [congrArg (fun q : ℝ => q * t ^ 2) hlt]
  · have hm := hmin (-a) (Real.sqrt 2 * (-a))
    have hg := energy_gap lam r a (-a) (Real.sqrt 2 * (-a))
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    by_contra hn
    have hmarg : lam * a ^ 2 + r < 0 := lt_of_not_ge hn
    have hnprod : a ^ 2 * (lam * a ^ 2 + r) < 0 :=
      mul_neg_of_pos_of_neg ha2 hmarg
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add,
      neg_add_cancel, mul_zero] at hg
    nlinarith

theorem globalMin_iff_margin {lam r a : ℝ} (hlam : 0 < lam) :
    GlobalMin lam r a ↔ 0 ≤ lam * a ^ 2 + r :=
  ⟨margin_of_globalMin hlam, globalMin_of_margin (le_of_lt hlam)⟩

/-- The certificate also controls the squared location error. -/
theorem quadratic_gap_bound {lam r a : ℝ} (hlam : 0 ≤ lam) (x y : ℝ) :
    (lam * a ^ 2 + r) / 2 * (x - a) ^ 2 ≤
      E lam r (input lam r a) x y - E lam r (input lam r a) a (Real.sqrt 2 * a) := by
  have hp : 0 ≤ (x - a) ^ 2 * (lam / 4 * (x + a) ^ 2) := by positivity
  have ht : 0 ≤ (y - Real.sqrt 2 * x) ^ 2 / 2 := by positivity
  linarith [energy_gap lam r a x y]

/-- Positive margin forces every point with the same energy to be the target. -/
theorem unique_of_margin_pos {lam r a : ℝ} (hlam : 0 ≤ lam)
    (hmargin : 0 < lam * a ^ 2 + r) {x y : ℝ}
    (he : E lam r (input lam r a) x y =
      E lam r (input lam r a) a (Real.sqrt 2 * a)) :
    x = a ∧ y = Real.sqrt 2 * a := by
  have hb := quadratic_gap_bound (r := r) (a := a) hlam x y
  have hsq : (x - a) ^ 2 = 0 := by
    have hnonneg := sq_nonneg (x - a)
    nlinarith
  have hx : x = a := by nlinarith [sq_nonneg (x - a)]
  subst x
  have hg := energy_gap lam r a a y
  have hy : (y - Real.sqrt 2 * a) ^ 2 = 0 := by
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at hg
    linarith
  exact ⟨rfl, by nlinarith [sq_nonneg (y - Real.sqrt 2 * a)]⟩

/-- At zero margin the complete equality set is the two reflected targets.
When a = 0 the two descriptions coincide, so this also covers the quartic minimum. -/
theorem equal_energy_iff_of_margin_zero {lam r a : ℝ} (hlam : 0 < lam)
    (hmargin : lam * a ^ 2 + r = 0) (x y : ℝ) :
    E lam r (input lam r a) x y =
      E lam r (input lam r a) a (Real.sqrt 2 * a) ↔
      (x = a ∨ x = -a) ∧ y = Real.sqrt 2 * x := by
  have hg := energy_gap lam r a x y
  rw [hmargin, zero_div, add_zero] at hg
  have hfirst : 0 ≤ (y - Real.sqrt 2 * x) ^ 2 / 2 := by positivity
  have hsecond : 0 ≤ (x - a) ^ 2 * (lam / 4 * (x + a) ^ 2) := by positivity
  constructor
  · intro he
    have hs : (x - a) ^ 2 * (lam / 4 * (x + a) ^ 2) = 0 := by linarith
    have hy0 : (y - Real.sqrt 2 * x) ^ 2 = 0 := by linarith
    have hy : y = Real.sqrt 2 * x := by nlinarith
    refine ⟨?_, hy⟩
    rcases mul_eq_zero.mp hs with hleft | hright
    · left
      nlinarith
    · have hl : lam / 4 ≠ 0 := ne_of_gt (by positivity)
      have hx : (x + a) ^ 2 = 0 := (mul_eq_zero.mp hright).resolve_left hl
      right
      nlinarith
  · rintro ⟨hx | hx, hy⟩
    · subst x
      subst y
      rfl
    · subst x
      subst y
      simp only [sub_self, neg_add_cancel, zero_pow (by decide : 2 ≠ 0),
        zero_div, mul_zero, zero_add] at hg
      linarith

/-- A measured energy error supplies a certified squared position-error bound. -/
theorem squared_position_error {lam r a x y eps : ℝ} (hlam : 0 ≤ lam)
    (hmargin : 0 < lam * a ^ 2 + r)
    (herror : E lam r (input lam r a) x y -
      E lam r (input lam r a) a (Real.sqrt 2 * a) ≤ eps) :
    (x - a) ^ 2 ≤ 2 * eps / (lam * a ^ 2 + r) := by
  apply (le_div_iff₀ hmargin).2
  have hb := quadratic_gap_bound (r := r) (a := a) hlam x y
  nlinarith

/-- The square-root error estimate displayed by the companion is certified too. -/
theorem position_error {lam r a x y eps : ℝ} (hlam : 0 ≤ lam)
    (hmargin : 0 < lam * a ^ 2 + r)
    (herror : E lam r (input lam r a) x y -
      E lam r (input lam r a) a (Real.sqrt 2 * a) ≤ eps) :
    |x - a| ≤ Real.sqrt (2 * eps / (lam * a ^ 2 + r)) := by
  exact Real.abs_le_sqrt (squared_position_error hlam hmargin herror)

end LinearInputDesign
