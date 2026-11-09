
/-!
# The actual real interval Fourier coefficient operator

The coefficients are Lebesgue interval integrals. Self-adjointness applies to
all continuous real-line inputs. Derivative commutation requires actual C1
input and agreement at the periodic endpoints, and is proved by actual IBP.
-/

namespace KerrKoopman.IntervalFourier

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators Interval
open FourierSupBounds ContinuumCalculus

def period : ℝ := 2 * Real.pi

def mean (f : ℝ → ℝ) : ℝ := (∫ x in 0..period, f x) / period

def cosCoeff (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  2 / period * ∫ x in 0..period, f x * Real.cos ((k : ℝ) * x)

def sinCoeff (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  2 / period * ∫ x in 0..period, f x * Real.sin ((k : ℝ) * x)

/-- Frequencies 1,...,N, with the constant mode represented separately. -/
def projection (N : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  polynomial (mean f) (fun k : Fin N => ((k.val+1 : ℕ) : ℝ))
    (fun k => cosCoeff f (k.val+1)) (fun k => sinCoeff f (k.val+1))

theorem projection_hasDerivAt (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    HasDerivAt (projection N f)
      (firstRate (fun k : Fin N => ((k.val+1 : ℕ) : ℝ))
        (fun k => cosCoeff f (k.val+1)) (fun k => sinCoeff f (k.val+1)) x) x :=
  polynomial_hasDerivAt _ _ _ _ x

theorem projection_continuous (N : ℕ) (f : ℝ → ℝ) : Continuous (projection N f) :=
  continuous_iff_continuousAt.mpr (fun x => (projection_hasDerivAt N f x).continuousAt)

theorem cos_endpoint (k : ℕ) :
    Real.cos ((k : ℝ)*period) = Real.cos ((k : ℝ)*0) := by
  simp [period, Real.cos_nat_mul_two_pi]

theorem sin_endpoint (k : ℕ) :
    Real.sin ((k : ℝ)*period) = Real.sin ((k : ℝ)*0) := by
  simpa only [period, zero_add, mul_zero, Real.sin_zero] using
    Real.sin_add_nat_mul_two_pi 0 k

theorem projection_endpoint (N : ℕ) (f : ℝ → ℝ) : projection N f period = projection N f 0 := by
  simp only [projection, polynomial, cos_endpoint, sin_endpoint]

theorem polynomial_pairing {ι : Type*} [Fintype ι] (c : ℝ) (ω a b : ι → ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x in 0..period, polynomial c ω a b x * g x) =
      c * (∫ x in 0..period, g x) + ∑ k,
        (a k * (∫ x in 0..period, Real.cos (ω k*x)*g x) +
         b k * (∫ x in 0..period, Real.sin (ω k*x)*g x)) := by
  have hc : Continuous (fun x => c*g x) := by fun_prop
  have hk (k : ι) : Continuous (fun x =>
      a k * (Real.cos (ω k*x)*g x) + b k * (Real.sin (ω k*x)*g x)) := by fun_prop
  have hs : Continuous (fun x => ∑ k,
      (a k * (Real.cos (ω k*x)*g x) + b k * (Real.sin (ω k*x)*g x))) := by fun_prop
  have he : (fun x => polynomial c ω a b x*g x) = (fun x => c*g x + ∑ k,
      (a k * (Real.cos (ω k*x)*g x) + b k * (Real.sin (ω k*x)*g x))) := by
    funext x
    simp only [polynomial, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hadd : (∫ x in 0..period, c*g x + ∑ k,
      (a k * (Real.cos (ω k*x)*g x) + b k * (Real.sin (ω k*x)*g x))) =
      (∫ x in 0..period, c*g x) + ∫ x in 0..period, ∑ k,
      (a k * (Real.cos (ω k*x)*g x) + b k * (Real.sin (ω k*x)*g x)) :=
    intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hs.intervalIntegrable _ _)
  rw [he, hadd, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finset_sum (fun k _ => (hk k).intervalIntegrable _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have h1 : Continuous (fun x => a k*(Real.cos (ω k*x)*g x)) := by fun_prop
  have h2 : Continuous (fun x => b k*(Real.sin (ω k*x)*g x)) := by fun_prop
  rw [intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem projection_pairing (N : ℕ) (f g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x in 0..period, projection N f x*g x) =
      period * mean f * mean g + period/2 * ∑ k : Fin N,
        (cosCoeff f (k.val+1)*cosCoeff g (k.val+1) +
         sinCoeff f (k.val+1)*sinCoeff g (k.val+1)) := by
  rw [projection, polynomial_pairing _ _ _ _ g hg]
  have hp : period ≠ 0 := by unfold period; positivity
  unfold mean cosCoeff sinCoeff
  simp_rw [mul_comm (Real.cos _) (g _), mul_comm (Real.sin _) (g _)]
  rw [Finset.mul_sum]
  congr 1
  · field_simp
  · apply Finset.sum_congr rfl
    intro k _
    field_simp

/-- True interval-integral self-adjointness, without periodicity of either input. -/
theorem projection_selfadjoint (N : ℕ) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x in 0..period, projection N f x*g x) = ∫ x in 0..period, f x*projection N g x := by
  have he : (fun x => f x*projection N g x) = (fun x => projection N g x*f x) := by
    funext x
    ring
  rw [he, projection_pairing N f g hg, projection_pairing N g f hf]
  congr 1
  · ring
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem mean_derivative (f df : ℝ → ℝ) (hdf : ∀ x, HasDerivAt f (df x) x)
    (cdf : Continuous df) (hp : f period = f 0) : mean df = 0 := by
  have hi : (∫ x in 0..period, df x) = f period - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hdf x) (cdf.intervalIntegrable _ _)
  rw [mean, hi, hp, sub_self, zero_div]

theorem cosCoeff_derivative (f df : ℝ → ℝ) (k : ℕ)
    (hdf : ∀ x, HasDerivAt f (df x) x) (cdf : Continuous df) (hp : f period = f 0) :
    cosCoeff df k = (k : ℝ)*sinCoeff f k := by
  have hd (x : ℝ) : HasDerivAt (fun y => Real.cos ((k : ℝ)*y))
      (-(k : ℝ)*Real.sin ((k : ℝ)*x)) x := by
    convert ((hasDerivAt_id x).const_mul (k : ℝ)).cos using 1
    simp only [id_eq]
    ring
  have cd : Continuous (fun x => -(k : ℝ)*Real.sin ((k : ℝ)*x)) := by fun_prop
  have hi := periodic_skew_integral f (fun x => Real.cos ((k : ℝ)*x)) df
    (fun x => -(k : ℝ)*Real.sin ((k : ℝ)*x)) 0 period hdf hd cdf cd hp (cos_endpoint k)
  have he : (fun x => f x*(-(k : ℝ)*Real.sin ((k : ℝ)*x))) =
      (fun x => -(k : ℝ)*(f x*Real.sin ((k : ℝ)*x))) := by funext x; ring
  rw [he, intervalIntegral.integral_const_mul] at hi
  have hj : (∫ x in 0..period, df x*Real.cos ((k : ℝ)*x)) =
      (k : ℝ)*(∫ x in 0..period, f x*Real.sin ((k : ℝ)*x)) := by linarith
  unfold cosCoeff sinCoeff
  rw [hj]
  ring

theorem sinCoeff_derivative (f df : ℝ → ℝ) (k : ℕ)
    (hdf : ∀ x, HasDerivAt f (df x) x) (cdf : Continuous df) (hp : f period = f 0) :
    sinCoeff df k = -(k : ℝ)*cosCoeff f k := by
  have hd (x : ℝ) : HasDerivAt (fun y => Real.sin ((k : ℝ)*y))
      ((k : ℝ)*Real.cos ((k : ℝ)*x)) x := by
    convert ((hasDerivAt_id x).const_mul (k : ℝ)).sin using 1
    simp only [id_eq]
    ring
  have cd : Continuous (fun x => (k : ℝ)*Real.cos ((k : ℝ)*x)) := by fun_prop
  have hi := periodic_skew_integral f (fun x => Real.sin ((k : ℝ)*x)) df
    (fun x => (k : ℝ)*Real.cos ((k : ℝ)*x)) 0 period hdf hd cdf cd hp (sin_endpoint k)
  have he : (fun x => f x*((k : ℝ)*Real.cos ((k : ℝ)*x))) =
      (fun x => (k : ℝ)*(f x*Real.cos ((k : ℝ)*x))) := by funext x; ring
  rw [he, intervalIntegral.integral_const_mul] at hi
  have hj : (∫ x in 0..period, df x*Real.sin ((k : ℝ)*x)) =
      -(k : ℝ)*(∫ x in 0..period, f x*Real.cos ((k : ℝ)*x)) := by linarith
  unfold cosCoeff sinCoeff
  rw [hj]
  ring

/-- Commutation is a consequence of IBP on the actual periodic input. -/
theorem projection_derivative_commutes (N : ℕ) (f df : ℝ → ℝ)
    (hdf : ∀ x, HasDerivAt f (df x) x) (cdf : Continuous df) (hp : f period = f 0) :
    projection N df = deriv (projection N f) := by
  unfold projection
  rw [polynomial_deriv]
  funext x
  simp only [polynomial, mean_derivative f df hdf cdf hp, zero_add,
    cosCoeff_derivative f df _ hdf cdf hp, sinCoeff_derivative f df _ hdf cdf hp, firstRate]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end KerrKoopman.IntervalFourier
