/-!
Actual circular-arc integrals behind the integer curve-word alphabet.

An arc of length h and total real turning angle a is reconstructed from
theta(s) = (a / h) s by Elastica.xCoord and Elastica.yCoord.  Its cost is
the existing Elastica.energy with quadratic density.  The endpoint and
cost formulae below are consequences of these integrals, not definitions.
Arbitrary concatenations remain the piecewise-smooth auxiliary model;
these results do not assert smooth elastica stationarity at a junction.
-/

noncomputable section
open Real MeasureTheory

namespace LinearInputCurveWordArc

def arcAngle (h a s : ℝ) : ℝ := (a / h) * s

def quadraticDensity (κ : ℝ) : ℝ := κ ^ 2 / 2

def arcState (h a : ℝ) : LinearInputCurveWordAlgebra.State :=
  (⟨Elastica.xCoord (arcAngle h a) 0 h, Elastica.yCoord (arcAngle h a) 0 h⟩,
   arcAngle h a h - arcAngle h a 0,
   Elastica.energy quadraticDensity (arcAngle h a) h)

theorem arcAngle_continuous (h a : ℝ) : Continuous (arcAngle h a) := by
  unfold arcAngle
  fun_prop

theorem arcAngle_initial (h a : ℝ) : arcAngle h a 0 = 0 := by simp [arcAngle]

theorem arcAngle_terminal {h : ℝ} (hh : 0 < h) (a : ℝ) : arcAngle h a h = a := by
  simp [arcAngle, ne_of_gt hh]

theorem arcAngle_derivative (h a s : ℝ) : HasDerivAt (arcAngle h a) (a / h) s := by
  simpa only [arcAngle, mul_one] using (hasDerivAt_id s).const_mul (a / h)

theorem arc_curvature (h a s : ℝ) : Elastica.curvature (arcAngle h a) s = a / h :=
  (arcAngle_derivative h a s).deriv

theorem arc_unit_speed (h a s : ℝ) :
    (deriv (Elastica.xCoord (arcAngle h a) 0) s) ^ 2 +
      (deriv (Elastica.yCoord (arcAngle h a) 0) s) ^ 2 = 1 :=
  Elastica.unit_speed_squared (arcAngle_continuous h a) 0 0 s

theorem arc_x_endpoint {h a : ℝ} (hh : 0 < h) (ha : a ≠ 0) :
    Elastica.xCoord (arcAngle h a) 0 h = h * Real.sin a / a := by
  have hx := Elastica.xCoord_affine 0 (a / h) 0 h (div_ne_zero ha (ne_of_gt hh))
  simpa only [zero_add, arcAngle, div_mul_cancel₀ _ (ne_of_gt hh), Real.sin_zero,
    sub_zero, div_div_eq_mul_div, mul_comm (Real.sin a) h] using hx

theorem arc_y_endpoint {h a : ℝ} (hh : 0 < h) (ha : a ≠ 0) :
    Elastica.yCoord (arcAngle h a) 0 h = h * (1 - Real.cos a) / a := by
  have hy := Elastica.yCoord_affine 0 (a / h) 0 h (div_ne_zero ha (ne_of_gt hh))
  simpa only [zero_add, arcAngle, div_mul_cancel₀ _ (ne_of_gt hh), Real.cos_zero,
    div_div_eq_mul_div, mul_comm (1 - Real.cos a) h] using hy

theorem arc_quadratic_energy {h : ℝ} (hh : 0 < h) (a : ℝ) :
    Elastica.energy quadraticDensity (arcAngle h a) h = a ^ 2 / (2 * h) := by
  have hd : deriv (arcAngle h a) = fun _ => a / h :=
    funext (fun s => (arcAngle_derivative h a s).deriv)
  simp only [Elastica.energy, hd, quadraticDensity, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  field_simp

theorem arc_state_formula {h a : ℝ} (hh : 0 < h) (ha : a ≠ 0) :
    arcState h a =
      (⟨h * Real.sin a / a, h * (1 - Real.cos a) / a⟩, a, a ^ 2 / (2 * h)) := by
  simp [arcState, arc_x_endpoint hh ha, arc_y_endpoint hh ha,
    arcAngle_terminal hh, arcAngle_initial, arc_quadratic_energy hh]

/-- Geometric scaling of the actual integrated nonstraight arc agrees with the
state scaling used in the algebraic theorem chain. -/
theorem arc_state_scale {σ h a : ℝ} (hσ : 0 < σ) (hh : 0 < h) (ha : a ≠ 0) :
    arcState (σ * h) a = LinearInputCurveWordAlgebra.scale σ (arcState h a) := by
  rw [arc_state_formula (mul_pos hσ hh) ha, arc_state_formula hh ha]
  apply LinearInputCurveWordAlgebra.state_ext
  · apply Complex.ext <;>
      simp [LinearInputCurveWordAlgebra.endpoint, LinearInputCurveWordAlgebra.scale,
        Complex.mul_re, Complex.mul_im] <;> ring
  · rfl
  · change a ^ 2 / (2 * (σ * h)) = a ^ 2 / (2 * h) / σ
    ring

def endpointUnit (h : ℝ) : ℝ := 2 * h / (3 * Real.pi)

def costUnit (h : ℝ) : ℝ := Real.pi ^ 2 / (8 * h)

theorem endpointUnit_pos {h : ℝ} (hh : 0 < h) : 0 < endpointUnit h := by
  unfold endpointUnit
  positivity

theorem costUnit_pos {h : ℝ} (hh : 0 < h) : 0 < costUnit h := by
  unfold costUnit
  positivity

theorem sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.sin_add]
  simp

theorem cos_three_pi_div_two : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add]
  simp

theorem arc_A_state {h : ℝ} (hh : 0 < h) :
    arcState h (Real.pi / 2) =
      (⟨3 * endpointUnit h, 3 * endpointUnit h⟩, Real.pi / 2, costUnit h) := by
  rw [arc_state_formula hh (by positivity)]
  simp only [Real.sin_pi_div_two, Real.cos_pi_div_two, sub_zero, mul_one]
  apply Prod.ext
  · apply Complex.ext <;> simp only [endpointUnit] <;> ring
  · apply Prod.ext
    · rfl
    · simp only [costUnit]
      ring

theorem arc_B_state {h : ℝ} (hh : 0 < h) :
    arcState h (3 * Real.pi / 2) =
      (⟨-endpointUnit h, endpointUnit h⟩, 3 * Real.pi / 2, 9 * costUnit h) := by
  rw [arc_state_formula hh (by positivity)]
  simp only [sin_three_pi_div_two, cos_three_pi_div_two, sub_zero, mul_one, mul_neg_one]
  apply Prod.ext
  · apply Complex.ext <;> simp only [endpointUnit] <;> ring
  · apply Prod.ext
    · rfl
    · simp only [costUnit]
      ring

/-- The actual integrated arc for the Boolean alphabet used by CurveWordFinite. -/
def letterState (h : ℝ) (a : Bool) : LinearInputCurveWordAlgebra.State :=
  arcState h (if a then Real.pi / 2 else 3 * Real.pi / 2)

/-- Interpret the lifted discrete endpoint, angle and cost in physical units. -/
def interpretFirstState (h : ℝ) (s : LinearInputCurveWordFinite.State) :
    LinearInputCurveWordAlgebra.State :=
  (⟨endpointUnit h * (s.1.1 : ℝ), endpointUnit h * (s.1.2 : ℝ)⟩,
   (s.2.1 : ℝ) * (Real.pi / 2), costUnit h * (s.2.2.1 : ℝ))

theorem letter_matches_integer_step {h : ℝ} (hh : 0 < h) (a : Bool) :
    letterState h a = interpretFirstState h
      (LinearInputCurveWordFinite.step ((0, 0), 0, 0, 0) a) := by
  cases a
  · change arcState h (3 * Real.pi / 2) = _
    rw [arc_B_state hh]
    simp [interpretFirstState, LinearInputCurveWordFinite.step,
      LinearInputCurveWordFinite.rotate, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  · change arcState h (Real.pi / 2) = _
    rw [arc_A_state hh]
    simp [interpretFirstState, LinearInputCurveWordFinite.step,
      LinearInputCurveWordFinite.rotate, mul_comm]

end LinearInputCurveWordArc
