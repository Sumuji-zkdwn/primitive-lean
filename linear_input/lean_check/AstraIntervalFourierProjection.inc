
/-! Actual trigonometric orthogonality and idempotence of the interval Fourier operator. -/

namespace KerrKoopman.IntervalFourier

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory FourierSupBounds
open scoped BigOperators Interval

theorem integral_cos_int (k : ℤ) :
    (∫ x in 0..period, Real.cos ((k : ℝ)*x)) = if k=0 then period else 0 := by
  by_cases hk : k=0
  · simp [hk]
  · have hr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hs : Real.sin ((k : ℝ)*period) = 0 := by
      simpa only [period, zero_add, Real.sin_zero] using Real.sin_add_int_mul_two_pi 0 k
    rw [if_neg hk, intervalIntegral.integral_comp_mul_left Real.cos hr, integral_cos]
    simp [hs]

theorem integral_sin_int (k : ℤ) :
    (∫ x in 0..period, Real.sin ((k : ℝ)*x)) = 0 := by
  by_cases hk : k=0
  · simp [hk]
  · have hr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [intervalIntegral.integral_comp_mul_left Real.sin hr, integral_sin]
    simp [period, Real.cos_int_mul_two_pi]

theorem integral_cos_nat (k : ℕ) (hk : 0<k) :
    (∫ x in 0..period, Real.cos ((k : ℝ)*x)) = 0 := by
  simpa only [Int.cast_natCast, if_neg (show (k : ℤ) ≠ 0 by omega)] using integral_cos_int (k : ℤ)

theorem integral_sin_nat (k : ℕ) :
    (∫ x in 0..period, Real.sin ((k : ℝ)*x)) = 0 := by
  simpa only [Int.cast_natCast] using integral_sin_int (k : ℤ)

theorem integral_cos_cos (k l : ℕ) (hk : 0<k) (hl : 0<l) :
    (∫ x in 0..period, Real.cos ((k : ℝ)*x)*Real.cos ((l : ℝ)*x)) =
      if k=l then period/2 else 0 := by
  have hd : Continuous (fun x => Real.cos ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x)) := by fun_prop
  have ha : Continuous (fun x => Real.cos ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x)) := by fun_prop
  have he : (fun x => Real.cos ((k : ℝ)*x)*Real.cos ((l : ℝ)*x)) =
      (fun x => (Real.cos ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x) +
        Real.cos ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x))/2) := by
    funext x
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  have hi : (∫ x in 0..period, Real.cos ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x) +
      Real.cos ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x)) =
      (∫ x in 0..period, Real.cos ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x)) +
      (∫ x in 0..period, Real.cos ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x)) :=
    intervalIntegral.integral_add (hd.intervalIntegrable _ _) (ha.intervalIntegrable _ _)
  rw [he, intervalIntegral.integral_div, hi, integral_cos_int, integral_cos_int,
    if_neg (show (k : ℤ)+(l : ℤ) ≠ 0 by omega), add_zero]
  by_cases h : k=l
  · simp [h]
  · rw [if_neg h, if_neg (show (k : ℤ)-(l : ℤ) ≠ 0 by omega), zero_div]

theorem integral_sin_sin (k l : ℕ) (hk : 0<k) (hl : 0<l) :
    (∫ x in 0..period, Real.sin ((k : ℝ)*x)*Real.sin ((l : ℝ)*x)) =
      if k=l then period/2 else 0 := by
  have hd : Continuous (fun x => Real.cos ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x)) := by fun_prop
  have ha : Continuous (fun x => Real.cos ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x)) := by fun_prop
  have he : (fun x => Real.sin ((k : ℝ)*x)*Real.sin ((l : ℝ)*x)) =
      (fun x => (Real.cos ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x) -
        Real.cos ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x))/2) := by
    funext x
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  have hi : (∫ x in 0..period, Real.cos ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x) -
      Real.cos ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x)) =
      (∫ x in 0..period, Real.cos ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x)) -
      (∫ x in 0..period, Real.cos ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x)) :=
    intervalIntegral.integral_sub (hd.intervalIntegrable _ _) (ha.intervalIntegrable _ _)
  rw [he, intervalIntegral.integral_div, hi, integral_cos_int, integral_cos_int,
    if_neg (show (k : ℤ)+(l : ℤ) ≠ 0 by omega), sub_zero]
  by_cases h : k=l
  · simp [h]
  · rw [if_neg h, if_neg (show (k : ℤ)-(l : ℤ) ≠ 0 by omega), zero_div]

theorem integral_sin_cos (k l : ℕ) :
    (∫ x in 0..period, Real.sin ((k : ℝ)*x)*Real.cos ((l : ℝ)*x)) = 0 := by
  have hd : Continuous (fun x => Real.sin ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x)) := by fun_prop
  have ha : Continuous (fun x => Real.sin ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x)) := by fun_prop
  have he : (fun x => Real.sin ((k : ℝ)*x)*Real.cos ((l : ℝ)*x)) =
      (fun x => (Real.sin ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x) +
        Real.sin ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x))/2) := by
    funext x
    push_cast
    rw [sub_mul, add_mul, Real.sin_sub, Real.sin_add]
    ring
  have hi : (∫ x in 0..period, Real.sin ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x) +
      Real.sin ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x)) =
      (∫ x in 0..period, Real.sin ((((k : ℤ)+(l : ℤ) : ℤ) : ℝ)*x)) +
      (∫ x in 0..period, Real.sin ((((k : ℤ)-(l : ℤ) : ℤ) : ℝ)*x)) :=
    intervalIntegral.integral_add (ha.intervalIntegrable _ _) (hd.intervalIntegrable _ _)
  rw [he, intervalIntegral.integral_div, hi, integral_sin_int, integral_sin_int]
  norm_num

theorem integral_cos_sin (k l : ℕ) :
    (∫ x in 0..period, Real.cos ((k : ℝ)*x)*Real.sin ((l : ℝ)*x)) = 0 := by
  simpa only [mul_comm] using integral_sin_cos l k

theorem mean_polynomial (N : ℕ) (c : ℝ) (a b : Fin N → ℝ) :
    mean (polynomial c (fun k : Fin N => ((k.val+1 : ℕ) : ℝ)) a b) = c := by
  have hi := polynomial_pairing c (fun k : Fin N => ((k.val+1 : ℕ) : ℝ)) a b
    (fun _ => 1) continuous_const
  simp only [mul_one, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  simp_rw [integral_cos_nat _ (Nat.succ_pos _), integral_sin_nat] at hi
  simp only [mul_zero, add_zero, Finset.sum_const_zero] at hi
  unfold mean
  rw [hi]
  have hp : period ≠ 0 := by unfold period; positivity
  field_simp

theorem cosCoeff_polynomial (N : ℕ) (c : ℝ) (a b : Fin N → ℝ) (j : Fin N) :
    cosCoeff (polynomial c (fun k : Fin N => ((k.val+1 : ℕ) : ℝ)) a b) (j.val+1) = a j := by
  have hg : Continuous (fun x => Real.cos (((j.val+1 : ℕ) : ℝ)*x)) := by fun_prop
  have hi := polynomial_pairing c (fun k : Fin N => ((k.val+1 : ℕ) : ℝ)) a b _ hg
  simp_rw [integral_cos_nat _ (Nat.succ_pos _),
    integral_cos_cos _ _ (Nat.succ_pos _) (Nat.succ_pos _), integral_sin_cos] at hi
  simp only [mul_zero, zero_add, add_zero] at hi
  have he (k : Fin N) : (k.val+1=j.val+1) ↔ k=j := by simp [Fin.ext_iff]
  simp_rw [he, mul_ite, mul_zero] at hi
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hi
  unfold cosCoeff
  rw [hi]
  have hp : period ≠ 0 := by unfold period; positivity
  field_simp

theorem sinCoeff_polynomial (N : ℕ) (c : ℝ) (a b : Fin N → ℝ) (j : Fin N) :
    sinCoeff (polynomial c (fun k : Fin N => ((k.val+1 : ℕ) : ℝ)) a b) (j.val+1) = b j := by
  have hg : Continuous (fun x => Real.sin (((j.val+1 : ℕ) : ℝ)*x)) := by fun_prop
  have hi := polynomial_pairing c (fun k : Fin N => ((k.val+1 : ℕ) : ℝ)) a b _ hg
  simp_rw [integral_sin_nat, integral_cos_sin,
    integral_sin_sin _ _ (Nat.succ_pos _) (Nat.succ_pos _)] at hi
  simp only [mul_zero, zero_add] at hi
  have he (k : Fin N) : (k.val+1=j.val+1) ↔ k=j := by simp [Fin.ext_iff]
  simp_rw [he, mul_ite, mul_zero] at hi
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hi
  unfold sinCoeff
  rw [hi]
  have hp : period ≠ 0 := by unfold period; positivity
  field_simp

theorem projection_idempotent (N : ℕ) (f : ℝ → ℝ) :
    projection N (projection N f) = projection N f := by
  unfold projection
  simp only [mean_polynomial, cosCoeff_polynomial, sinCoeff_polynomial]

theorem projection_polynomial (N : ℕ) (c : ℝ) (a b : Fin N → ℝ) :
    projection N (polynomial c (fun k : Fin N => ((k.val+1 : ℕ) : ℝ)) a b) =
      polynomial c (fun k : Fin N => ((k.val+1 : ℕ) : ℝ)) a b := by
  unfold projection
  simp only [mean_polynomial, cosCoeff_polynomial, sinCoeff_polynomial]

/-- The actual interval operator now discharges every bundled projection law. -/
def actualProjection (N : ℕ) : ContinuumGalerkin.IntervalProjection 0 period where
  apply := projection N
  continuous := fun f _ => projection_continuous N f
  selfadjoint := projection_selfadjoint N
  idempotent := fun f _ => projection_idempotent N f

theorem weighted_integral_sub (f g w : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hw : Continuous w) :
    (∫ x in 0..period, (f x-g x)*w x) =
      (∫ x in 0..period, f x*w x) - ∫ x in 0..period, g x*w x := by
  have he : (fun x => (f x-g x)*w x) = (fun x => f x*w x-g x*w x) := by
    funext x
    ring
  rw [he]
  exact intervalIntegral.integral_sub ((hf.mul hw).intervalIntegrable _ _)
    ((hg.mul hw).intervalIntegrable _ _)

theorem mean_sub (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    mean (fun x => f x-g x) = mean f-mean g := by
  unfold mean
  have hi : (∫ x in 0..period, f x-g x) =
      (∫ x in 0..period, f x) - ∫ x in 0..period, g x :=
    intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
  rw [hi, sub_div]

theorem cosCoeff_sub (f g : ℝ → ℝ) (k : ℕ) (hf : Continuous f) (hg : Continuous g) :
    cosCoeff (fun x => f x-g x) k = cosCoeff f k-cosCoeff g k := by
  unfold cosCoeff
  rw [weighted_integral_sub f g _ hf hg (by fun_prop)]
  ring

theorem sinCoeff_sub (f g : ℝ → ℝ) (k : ℕ) (hf : Continuous f) (hg : Continuous g) :
    sinCoeff (fun x => f x-g x) k = sinCoeff f k-sinCoeff g k := by
  unfold sinCoeff
  rw [weighted_integral_sub f g _ hf hg (by fun_prop)]
  ring

theorem projection_sub (N : ℕ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    projection N (fun x => f x-g x) = fun x => projection N f x-projection N g x := by
  funext x
  simp only [projection, polynomial, mean_sub f g hf hg,
    cosCoeff_sub f g _ hf hg, sinCoeff_sub f g _ hf hg,
    sub_mul, sub_add_sub_comm, Finset.sum_sub_distrib]

theorem projection_deriv_continuous (N : ℕ) (f : ℝ → ℝ) :
    Continuous (deriv (projection N f)) := by
  unfold projection
  rw [polynomial_deriv]
  unfold firstRate
  fun_prop

/-- The actual magnetic projection residual has zero projection. -/
theorem projection_residual_zero (N : ℕ) (f df : ℝ → ℝ)
    (hdf : ∀ x, HasDerivAt f (df x) x) (cdf : Continuous df) (hp : f period=f 0) :
    projection N (fun x => df x-deriv (projection N f) x) = fun _ => 0 := by
  have hd (x : ℝ) : HasDerivAt (projection N f) (deriv (projection N f) x) x :=
    (projection_hasDerivAt N f x).differentiableAt.hasDerivAt
  have hc := projection_derivative_commutes N (projection N f) (deriv (projection N f))
    hd (projection_deriv_continuous N f) (projection_endpoint N f)
  rw [projection_idempotent] at hc
  rw [projection_sub N df _ cdf (projection_deriv_continuous N f),
    projection_derivative_commutes N f df hdf cdf hp, hc]
  funext x
  exact sub_self _

end
end KerrKoopman.IntervalFourier
