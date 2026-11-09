import KerrKoopman.ContinuumRelative
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Actual integral tail estimates

Cauchy-Schwarz is derived from positivity of an actual interval integral of
a square. These estimates isolate the true-solution projection tails, rather
than requiring a bound for the approximate solution's spatial derivative.
-/

namespace KerrKoopman.IntegralTail

set_option backward.isDefEq.respectTransparency false

open MeasureTheory intervalIntegral Set
open KerrKoopman.RelativeEnergy KerrKoopman.RelativeDynamics

theorem integral_product_sq_le (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x in a..b, f x * g x) ^ 2 ≤
      (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  have hq (t : ℝ) :
      0 ≤ (∫ x in a..b, f x ^ 2) * (t * t) +
        (2 * ∫ x in a..b, f x * g x) * t + (∫ x in a..b, g x ^ 2) := by
    have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
      (fun x => sq_nonneg (t * f x + g x))
    have he : (fun x => (t * f x + g x) ^ 2) =
        (fun x => (t * t) * f x ^ 2 + (2 * t) * (f x * g x) + g x ^ 2) := by
      funext x
      ring
    rw [he] at hn
    have c1 : Continuous (fun x => (t*t) * f x ^ 2) := by fun_prop
    have c2 : Continuous (fun x => (2*t) * (f x * g x)) := by fun_prop
    have c3 : Continuous (fun x => g x ^ 2) := by fun_prop
    have c12 : Continuous (fun x => (t*t) * f x ^ 2 + (2*t) * (f x * g x)) := by fun_prop
    rw [intervalIntegral.integral_add (c12.intervalIntegrable a b)
        (c3.intervalIntegrable a b),
      intervalIntegral.integral_add (c1.intervalIntegrable a b) (c2.intervalIntegrable a b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hn
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

theorem integral_product_le_budget (f g : ℝ → ℝ) (a b A B : ℝ) (hab : a ≤ b)
    (hf : Continuous f) (hg : Continuous g) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf2 : (∫ x in a..b, f x ^ 2) ≤ A ^ 2)
    (hg2 : (∫ x in a..b, g x ^ 2) ≤ B ^ 2) :
    (∫ x in a..b, f x * g x) ≤ A * B := by
  have hff := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
    (fun x => sq_nonneg (f x))
  have hgg := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
    (fun x => sq_nonneg (g x))
  have hp := mul_le_mul hf2 hg2 hgg (sq_nonneg A)
  have hs := (integral_product_sq_le f g a b hab hf hg).trans hp
  have hab0 := mul_nonneg hA hB
  nlinarith [sq_nonneg ((∫ x in a..b, f x * g x) - A * B)]

/-- True tail times field error is absorbed by the relative electric gap. -/
theorem tail_error_le (f E V : ℝ → ℝ) (a b A : ℝ) (hab : a ≤ b)
    (hf : Continuous f) (hE : Continuous E) (hV : Continuous V)
    (hf2 : (∫ x in a..b, f x ^ 2) ≤ A ^ 2) :
    (∫ x in a..b, f x * (V x - E x)) ≤
      A ^ 2 / 2 + (∫ x in a..b, electricGap (E x) (V x)) := by
  have cg : Continuous (fun x => electricGap (E x) (V x)) := by
    unfold electricGap FiniteEnergy.density Riccati.constitutive
    fun_prop
  have hc : Continuous (fun x => f x ^ 2 / 2) := by fun_prop
  have cf : Continuous (fun x => f x * (V x - E x)) := by fun_prop
  have cp : Continuous (fun x => f x ^ 2 / 2 + electricGap (E x) (V x)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (cf.intervalIntegrable a b) (cp.intervalIntegrable a b)
    (fun x _ => show f x * (V x - E x) ≤ f x ^ 2 / 2 + electricGap (E x) (V x) from by
      nlinarith [sq_nonneg (f x - (V x - E x)), square_error_le_gap (E x) (V x)])
  rw [intervalIntegral.integral_add (hc.intervalIntegrable a b) (cg.intervalIntegrable a b),
    intervalIntegral.integral_div] at hi
  linarith

/-- The projection tail term needs only the tails of the true fields.
The orthogonality equality is kept explicit until a concrete projection is supplied. -/
theorem tail_field_le (f E V PE : ℝ → ℝ) (a b A B : ℝ) (hab : a ≤ b)
    (hf : Continuous f) (hE : Continuous E) (hV : Continuous V) (hPE : Continuous PE)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf2 : (∫ x in a..b, f x ^ 2) ≤ A ^ 2)
    (hE2 : (∫ x in a..b, (E x - PE x) ^ 2) ≤ B ^ 2)
    (horth : (∫ x in a..b, f x * PE x) = 0) :
    (∫ x in a..b, f x * V x) ≤ A ^ 2 / 2 + A * B +
      (∫ x in a..b, electricGap (E x) (V x)) := by
  have he := tail_error_le f E V a b A hab hf hE hV hf2
  have ht := integral_product_le_budget f (fun x => E x - PE x) a b A B hab
    hf (hE.sub hPE) hA hB hf2 hE2
  have c1 : Continuous (fun x => f x * (V x - E x)) := by fun_prop
  have c2 : Continuous (fun x => f x * (E x - PE x)) := by fun_prop
  have c3 : Continuous (fun x => f x * PE x) := by fun_prop
  have c12 : Continuous (fun x => f x * (V x - E x) + f x * (E x - PE x)) := by fun_prop
  have hid : (fun x => f x * V x) =
      (fun x => f x * (V x - E x) + f x * (E x - PE x) + f x * PE x) := by
    funext x
    ring
  rw [hid, intervalIntegral.integral_add (c12.intervalIntegrable a b)
      (c3.intervalIntegrable a b),
    intervalIntegral.integral_add (c1.intervalIntegrable a b) (c2.intervalIntegrable a b), horth]
  linarith

end KerrKoopman.IntegralTail
