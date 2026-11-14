/-!
Actual line integrals on parametrized circles.  Coordinates and derivatives
are explicit; the moment is the interval integral of x(t)^2 * y'(t).
This file does not identify the discrete quarter-turn word evaluator with
a globally parametrized piecewise-smooth curve.
-/

noncomputable section

namespace LinearInputCurveWordCircularMoment

open Real MeasureTheory

def circleX (c R t : ℝ) : ℝ := c + R * sin t

def circleY (d R t : ℝ) : ℝ := d - R * cos t

theorem circle_equation (c d R t : ℝ) :
    (circleX c R t - c) ^ 2 + (circleY d R t - d) ^ 2 = R ^ 2 := by
  calc
    _ = R ^ 2 * (sin t ^ 2 + cos t ^ 2) := by dsimp [circleX, circleY]; ring
    _ = _ := by rw [sin_sq_add_cos_sq, mul_one]

theorem circleY_hasDerivAt (d R t : ℝ) :
    HasDerivAt (circleY d R) (R * sin t) t := by
  convert ((hasDerivAt_cos t).const_mul R).const_sub d using 1
  · rfl
  · ring

theorem circleY_deriv (d R t : ℝ) :
    deriv (circleY d R) t = R * sin t :=
  (circleY_hasDerivAt d R t).deriv

/-- The actual integral x^2 dy on an oriented angular interval. -/
def circleMoment (c d R a b : ℝ) : ℝ :=
  ∫ t in a..b, circleX c R t ^ 2 * deriv (circleY d R) t

theorem circleMoment_integrand (c d R a b : ℝ) :
    circleMoment c d R a b = ∫ t in a..b, (c + R * sin t) ^ 2 * (R * sin t) := by
  simp only [circleMoment, circleX, circleY_deriv]

theorem circleMoment_explicit (c d R a b : ℝ) :
    circleMoment c d R a b =
      c ^ 2 * R * (cos a - cos b) +
      (2 * c * R ^ 2) * ((sin a * cos a - sin b * cos b + b - a) / 2) +
      R ^ 3 * (cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3) := by
  rw [circleMoment_integrand]
  have hp : (fun t : ℝ => (c + R * sin t) ^ 2 * (R * sin t)) =
      fun t => c ^ 2 * R * sin t + (2 * c * R ^ 2) * sin t ^ 2 +
        R ^ 3 * sin t ^ 3 := by
    funext t
    ring
  rw [hp]
  have h1 : IntervalIntegrable (fun t : ℝ => c ^ 2 * R * sin t) volume a b :=
    (continuous_const.mul continuous_sin).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => (2 * c * R ^ 2) * sin t ^ 2) volume a b :=
    (continuous_const.mul (continuous_sin.pow 2)).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun t : ℝ => R ^ 3 * sin t ^ 3) volume a b :=
    (continuous_const.mul (continuous_sin.pow 3)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h1.add h2) h3,
    intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_sin, integral_sin_sq, integral_sin_pow_three]

theorem circleMoment_full_turns (c d R a : ℝ) (n : ℕ) :
    circleMoment c d R a (a + (n : ℝ) * (2 * Real.pi)) =
      2 * (n : ℝ) * Real.pi * c * R ^ 2 := by
  rw [circleMoment_explicit, sin_add_nat_mul_two_pi, cos_add_nat_mul_two_pi]
  ring

theorem circleMoment_three_turns (c d R a : ℝ) :
    circleMoment c d R a (a + 6 * Real.pi) = 6 * Real.pi * c * R ^ 2 := by
  have h := circleMoment_full_turns c d R a 3
  norm_num only [Nat.cast_ofNat] at h
  rw [show (3 : ℝ) * (2 * Real.pi) = 6 * Real.pi by ring] at h
  exact h

theorem circleMoment_three_turn_difference (R d₀ d₁ a₀ a₁ : ℝ) :
    circleMoment (-2 * R) d₁ R a₁ (a₁ + 6 * Real.pi) -
      circleMoment 0 d₀ R a₀ (a₀ + 6 * Real.pi) = -12 * Real.pi * R ^ 3 := by
  rw [circleMoment_three_turns, circleMoment_three_turns]
  ring

theorem circleMoment_three_turn_difference_nonzero (R d₀ d₁ a₀ a₁ : ℝ) (hR : R ≠ 0) :
    circleMoment (-2 * R) d₁ R a₁ (a₁ + 6 * Real.pi) -
      circleMoment 0 d₀ R a₀ (a₀ + 6 * Real.pi) ≠ 0 := by
  rw [circleMoment_three_turn_difference]
  exact mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) (pow_ne_zero _ hR)

theorem circleMoment_three_turn_difference_h (h d₀ d₁ a₀ a₁ : ℝ) :
    circleMoment (-2 * (2 * h / (3 * Real.pi))) d₁ (2 * h / (3 * Real.pi)) a₁ (a₁ + 6 * Real.pi) -
      circleMoment 0 d₀ (2 * h / (3 * Real.pi)) a₀ (a₀ + 6 * Real.pi) =
        -32 * h ^ 3 / (9 * Real.pi ^ 2) := by
  rw [circleMoment_three_turn_difference]
  field_simp
  ring


theorem circleMoment_add (c d R a b e : ℝ) :
    circleMoment c d R a b + circleMoment c d R b e = circleMoment c d R a e := by
  simp only [circleMoment_integrand]
  have hc : Continuous (fun t : ℝ => (c + R * sin t) ^ 2 * (R * sin t)) := by
    fun_prop
  exact intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)

theorem circle_returns (c d R a : ℝ) (n : ℕ) :
    (circleX c R (a + (n : ℝ) * (2 * Real.pi)),
      circleY d R (a + (n : ℝ) * (2 * Real.pi))) =
    (circleX c R a, circleY d R a) := by
  simp [circleX, circleY, sin_add_nat_mul_two_pi, cos_add_nat_mul_two_pi]

theorem circle_start_at_origin (R : ℝ) :
    (circleX 0 R 0, circleY R R 0) = (0, 0) := by
  simp [circleX, circleY]

theorem insertion_position (R : ℝ) :
    (circleX 0 (3 * R) (3 * Real.pi / 2), circleY (3 * R) (3 * R) (3 * Real.pi / 2)) =
    (circleX (-2 * R) R (3 * Real.pi / 2), circleY (3 * R) R (3 * Real.pi / 2)) := by
  have h : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  simp only [circleX, circleY, h, sin_add, cos_add, sin_pi, cos_pi,
    sin_pi_div_two, cos_pi_div_two]
  simp
  ring

/-- Moment of an A circle followed by three B turns, each based at the origin.
A has radius 3R and B has radius R.  This is a sum of actual line integrals. -/
def sequentialLoopsMoment (R : ℝ) : ℝ :=
  circleMoment 0 (3 * R) (3 * R) 0 (2 * Real.pi) +
    circleMoment 0 R R 0 (6 * Real.pi)

/-- The same A circle split after three quarters, with three B turns inserted.
The position match is proved by insertion_position and circle_returns.
No equivalence to the separate discrete word evaluator is assumed. -/
def insertedLoopsMoment (R : ℝ) : ℝ :=
  circleMoment 0 (3 * R) (3 * R) 0 (3 * Real.pi / 2) +
    circleMoment (-2 * R) (3 * R) R (3 * Real.pi / 2) (3 * Real.pi / 2 + 6 * Real.pi) +
    circleMoment 0 (3 * R) (3 * R) (3 * Real.pi / 2) (2 * Real.pi)

theorem insertion_moment_difference (R : ℝ) :
    insertedLoopsMoment R - sequentialLoopsMoment R = -12 * Real.pi * R ^ 3 := by
  have hA := circleMoment_add 0 (3 * R) (3 * R) 0 (3 * Real.pi / 2) (2 * Real.pi)
  have hB := circleMoment_three_turn_difference R R (3 * R) 0 (3 * Real.pi / 2)
  simp only [zero_add] at hB
  dsimp [insertedLoopsMoment, sequentialLoopsMoment]
  linarith

theorem insertion_moment_difference_h (h : ℝ) :
    insertedLoopsMoment (2 * h / (3 * Real.pi)) -
      sequentialLoopsMoment (2 * h / (3 * Real.pi)) = -32 * h ^ 3 / (9 * Real.pi ^ 2) := by
  rw [insertion_moment_difference]
  field_simp
  ring

theorem insertion_moments_distinct (h : ℝ) (hh : 0 < h) :
    insertedLoopsMoment (2 * h / (3 * Real.pi)) ≠
      sequentialLoopsMoment (2 * h / (3 * Real.pi)) := by
  apply sub_ne_zero.mp
  rw [insertion_moment_difference_h]
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hh.ne'))
    (mul_ne_zero (by norm_num) (pow_ne_zero _ pi_ne_zero))


theorem circleX_hasDerivAt (c R t : ℝ) :
    HasDerivAt (circleX c R) (R * cos t) t :=
  ((hasDerivAt_sin t).const_mul R).const_add c

theorem circleX_deriv (c R t : ℝ) :
    deriv (circleX c R) t = R * cos t :=
  (circleX_hasDerivAt c R t).deriv

/-- Actual signed area, with both derivatives taken from the explicit coordinates. -/
def circleArea (c d R a b : ℝ) : ℝ :=
  (1 / 2) * ∫ t in a..b,
    circleX c R t * deriv (circleY d R) t -
      circleY d R t * deriv (circleX c R) t

theorem circleArea_integrand (c d R a b : ℝ) :
    circleArea c d R a b =
      (1 / 2) * ∫ t in a..b, c * R * sin t - d * R * cos t + R ^ 2 := by
  unfold circleArea
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [circleX, circleY, circleY_deriv, circleX_deriv]
  calc
    (c + R * sin t) * (R * sin t) - (d - R * cos t) * (R * cos t) =
        c * R * sin t - d * R * cos t + R ^ 2 * (sin t ^ 2 + cos t ^ 2) := by ring
    _ = _ := by rw [sin_sq_add_cos_sq, mul_one]

theorem circleArea_explicit (c d R a b : ℝ) :
    circleArea c d R a b =
      (1 / 2) * (c * R * (cos a - cos b) -
        d * R * (sin b - sin a) + R ^ 2 * (b - a)) := by
  rw [circleArea_integrand]
  have h1 : IntervalIntegrable (fun t : ℝ => c * R * sin t) volume a b :=
    (continuous_const.mul continuous_sin).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => d * R * cos t) volume a b :=
    (continuous_const.mul continuous_cos).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun _t : ℝ => R ^ 2) volume a b :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h1.sub h2) h3,
    intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_sin, integral_cos,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem circleArea_full_turns (c d R a : ℝ) (n : ℕ) :
    circleArea c d R a (a + (n : ℝ) * (2 * Real.pi)) =
      (n : ℝ) * Real.pi * R ^ 2 := by
  rw [circleArea_explicit, sin_add_nat_mul_two_pi, cos_add_nat_mul_two_pi]
  ring

theorem circleArea_three_turns (c d R a : ℝ) :
    circleArea c d R a (a + 6 * Real.pi) = 3 * Real.pi * R ^ 2 := by
  have h := circleArea_full_turns c d R a 3
  norm_num only [Nat.cast_ofNat] at h
  rw [show (3 : ℝ) * (2 * Real.pi) = 6 * Real.pi by ring] at h
  exact h

theorem circleArea_one_turn (c d R : ℝ) :
    circleArea c d R 0 (2 * Real.pi) = Real.pi * R ^ 2 := by
  simpa only [Nat.cast_one, one_mul, zero_add] using circleArea_full_turns c d R 0 1

theorem circleArea_add (c d R a b e : ℝ) :
    circleArea c d R a b + circleArea c d R b e = circleArea c d R a e := by
  rw [circleArea_explicit, circleArea_explicit, circleArea_explicit]
  ring

def sequentialLoopsArea (R : ℝ) : ℝ :=
  circleArea 0 (3 * R) (3 * R) 0 (2 * Real.pi) +
    circleArea 0 R R 0 (6 * Real.pi)

def insertedLoopsArea (R : ℝ) : ℝ :=
  circleArea 0 (3 * R) (3 * R) 0 (3 * Real.pi / 2) +
    circleArea (-2 * R) (3 * R) R (3 * Real.pi / 2) (3 * Real.pi / 2 + 6 * Real.pi) +
    circleArea 0 (3 * R) (3 * R) (3 * Real.pi / 2) (2 * Real.pi)

theorem sequentialLoopsArea_value (R : ℝ) :
    sequentialLoopsArea R = 12 * Real.pi * R ^ 2 := by
  have hB := circleArea_three_turns 0 R R 0
  simp only [zero_add] at hB
  unfold sequentialLoopsArea
  rw [circleArea_one_turn, hB]
  ring

theorem insertedLoopsArea_value (R : ℝ) :
    insertedLoopsArea R = 12 * Real.pi * R ^ 2 := by
  calc
    insertedLoopsArea R =
        (circleArea 0 (3 * R) (3 * R) 0 (3 * Real.pi / 2) +
          circleArea 0 (3 * R) (3 * R) (3 * Real.pi / 2) (2 * Real.pi)) +
          circleArea (-2 * R) (3 * R) R (3 * Real.pi / 2)
            (3 * Real.pi / 2 + 6 * Real.pi) := by
      unfold insertedLoopsArea
      ring
    _ = circleArea 0 (3 * R) (3 * R) 0 (2 * Real.pi) +
          circleArea (-2 * R) (3 * R) R (3 * Real.pi / 2)
            (3 * Real.pi / 2 + 6 * Real.pi) := by rw [circleArea_add]
    _ = _ := by rw [circleArea_one_turn, circleArea_three_turns]; ring

theorem insertion_preserves_area (R : ℝ) :
    insertedLoopsArea R = sequentialLoopsArea R := by
  rw [insertedLoopsArea_value, sequentialLoopsArea_value]

theorem loop_area_h (h : ℝ) :
    insertedLoopsArea (2 * h / (3 * Real.pi)) = 16 * h ^ 2 / (3 * Real.pi) := by
  rw [insertedLoopsArea_value]
  field_simp
  ring

/-- Two explicit joined-circle descriptions have the same actual signed area
but different actual cubic moments for positive length scale. -/
theorem equal_area_distinct_moments (h : ℝ) (hh : 0 < h) :
    insertedLoopsArea (2 * h / (3 * Real.pi)) =
        sequentialLoopsArea (2 * h / (3 * Real.pi)) ∧
      insertedLoopsMoment (2 * h / (3 * Real.pi)) ≠
        sequentialLoopsMoment (2 * h / (3 * Real.pi)) :=
  ⟨insertion_preserves_area _, insertion_moments_distinct h hh⟩

end LinearInputCurveWordCircularMoment
