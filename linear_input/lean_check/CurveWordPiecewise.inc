/-!
A single tangent-angle reconstruction for every finite word of circular arcs.
The angle is continuous at the joins, while its derivative may jump there.
No global C1 curvature or elastica stationarity is asserted.
-/

noncomputable section

namespace LinearInputCurveWordPiecewise

open Real Set MeasureTheory Filter
open scoped Topology Interval
open LinearInputCurveWordAlgebra

def letterAngle (a : Bool) : ℝ := if a then Real.pi / 2 else 3 * Real.pi / 2

def splice (h a : ℝ) (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ h then LinearInputCurveWordArc.arcAngle h a t else a + θ (t - h)

def wordAngle (h : ℝ) : List Bool → ℝ → ℝ
  | [] => fun _ => 0
  | a :: w => splice h (letterAngle a) (wordAngle h w)

def wordLength (h : ℝ) (w : List Bool) : ℝ := (w.length : ℝ) * h

def totalAngle : List Bool → ℝ
  | [] => 0
  | a :: w => letterAngle a + totalAngle w

def curvePoint (θ : ℝ → ℝ) (t : ℝ) : ℂ :=
  ⟨Elastica.xCoord θ 0 t, Elastica.yCoord θ 0 t⟩

def curve (h : ℝ) (w : List Bool) : ℝ → ℂ := curvePoint (wordAngle h w)

theorem wordLength_nonneg {h : ℝ} (hh : 0 < h) (w : List Bool) : 0 ≤ wordLength h w :=
  mul_nonneg (Nat.cast_nonneg _) hh.le

theorem wordLength_cons (h : ℝ) (a : Bool) (w : List Bool) :
    wordLength h (a :: w) = h + wordLength h w := by
  simp [wordLength, Nat.cast_add, add_mul, add_comm]

theorem splice_left (h a : ℝ) (θ : ℝ → ℝ) {t : ℝ} (ht : t ≤ h) :
    splice h a θ t = LinearInputCurveWordArc.arcAngle h a t := by
  simp [splice, ht]

theorem splice_right {h : ℝ} (hh : 0 < h) (a : ℝ) (θ : ℝ → ℝ) (hθ : θ 0 = 0)
    {t : ℝ} (ht : h ≤ t) : splice h a θ t = a + θ (t - h) := by
  by_cases he : t ≤ h
  · have heq : t = h := le_antisymm he ht
    subst t
    simp [splice, LinearInputCurveWordArc.arcAngle_terminal hh, hθ]
  · simp [splice, he]

theorem splice_continuous {h : ℝ} (hh : 0 < h) (a : ℝ) {θ : ℝ → ℝ}
    (hc : Continuous θ) (hθ : θ 0 = 0) : Continuous (splice h a θ) := by
  apply (LinearInputCurveWordArc.arcAngle_continuous h a).if_le
    (continuous_const.add (hc.comp (continuous_id.sub continuous_const)))
    continuous_id continuous_const
  intro t ht
  change t = h at ht
  subst t
  simp [LinearInputCurveWordArc.arcAngle_terminal hh, hθ]

theorem wordAngle_initial {h : ℝ} (hh : 0 < h) (w : List Bool) : wordAngle h w 0 = 0 := by
  cases w with
  | nil => rfl
  | cons a w => simp [wordAngle, splice, hh.le, LinearInputCurveWordArc.arcAngle_initial]

theorem wordAngle_continuous {h : ℝ} (hh : 0 < h) (w : List Bool) :
    Continuous (wordAngle h w) := by
  induction w with
  | nil => exact continuous_const
  | cons a w ih => exact splice_continuous hh (letterAngle a) ih (wordAngle_initial hh w)

theorem wordAngle_terminal {h : ℝ} (hh : 0 < h) (w : List Bool) :
    wordAngle h w (wordLength h w) = totalAngle w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [wordLength_cons]
    change splice h (letterAngle a) (wordAngle h w) (h + wordLength h w) = _
    rw [splice_right hh _ _ (wordAngle_initial hh w) (by linarith [wordLength_nonneg hh w])]
    simp only [add_sub_cancel_left, ih, totalAngle]

theorem curve_unit_speed {h : ℝ} (hh : 0 < h) (w : List Bool) (t : ℝ) :
    (deriv (Elastica.xCoord (wordAngle h w) 0) t) ^ 2 +
      (deriv (Elastica.yCoord (wordAngle h w) 0) t) ^ 2 = 1 :=
  Elastica.unit_speed_squared (wordAngle_continuous hh w) 0 0 t

theorem curve_tangent_continuous {h : ℝ} (hh : 0 < h) (w : List Bool) :
    Continuous (deriv (Elastica.xCoord (wordAngle h w) 0)) ∧
      Continuous (deriv (Elastica.yCoord (wordAngle h w) 0)) := by
  have hc := wordAngle_continuous hh w
  constructor
  · have he := funext (Elastica.deriv_xCoord hc 0)
    rw [he]
    exact Real.continuous_cos.comp hc
  · have he := funext (Elastica.deriv_yCoord hc 0)
    rw [he]
    exact Real.continuous_sin.comp hc

theorem integral_splice {h : ℝ} (hh : 0 < h) (a : ℝ) {θ : ℝ → ℝ}
    (hc : Continuous θ) (hθ : θ 0 = 0) (f : ℝ → ℝ) (hf : Continuous f)
    {t : ℝ} (ht : h ≤ t) :
    (∫ s in 0..t, f (splice h a θ s)) =
      (∫ s in 0..h, f (LinearInputCurveWordArc.arcAngle h a s)) +
      (∫ s in 0..(t - h), f (a + θ s)) := by
  have hcont : Continuous (fun s => f (splice h a θ s)) :=
    hf.comp (splice_continuous hh a hc hθ)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 h) (hcont.intervalIntegrable h t)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hh.le] at hs
    change f (splice h a θ s) = f (LinearInputCurveWordArc.arcAngle h a s)
    rw [splice_left h a θ hs.2]
  · calc
      (∫ s in h..t, f (splice h a θ s)) =
          ∫ s in h..t, f (a + θ (s - h)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        change f (splice h a θ s) = f (a + θ (s - h))
        rw [splice_right hh a θ hθ hs.1]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right (fun s => f (a + θ s)) h]
        simp

theorem splice_x_right {h : ℝ} (hh : 0 < h) (a : ℝ) {θ : ℝ → ℝ}
    (hc : Continuous θ) (hθ : θ 0 = 0) {t : ℝ} (ht : h ≤ t) :
    Elastica.xCoord (splice h a θ) 0 t =
      Elastica.xCoord (LinearInputCurveWordArc.arcAngle h a) 0 h +
      Real.cos a * Elastica.xCoord θ 0 (t - h) -
      Real.sin a * Elastica.yCoord θ 0 (t - h) := by
  have hi := integral_splice hh a hc hθ Real.cos Real.continuous_cos ht
  have hr := Elastica.xCoord_add_angle hc a 0 0 0 (t - h)
  simp only [Elastica.xCoord, Elastica.yCoord, zero_add, sub_zero] at hr ⊢
  rw [hi]
  have he : (fun s => Real.cos (a + θ s)) = (fun s => Real.cos (θ s + a)) := by
    funext s
    rw [add_comm]
  rw [he]
  linarith

theorem splice_y_right {h : ℝ} (hh : 0 < h) (a : ℝ) {θ : ℝ → ℝ}
    (hc : Continuous θ) (hθ : θ 0 = 0) {t : ℝ} (ht : h ≤ t) :
    Elastica.yCoord (splice h a θ) 0 t =
      Elastica.yCoord (LinearInputCurveWordArc.arcAngle h a) 0 h +
      Real.sin a * Elastica.xCoord θ 0 (t - h) +
      Real.cos a * Elastica.yCoord θ 0 (t - h) := by
  have hi := integral_splice hh a hc hθ Real.sin Real.continuous_sin ht
  have hr := Elastica.yCoord_add_angle hc a 0 0 0 (t - h)
  simp only [Elastica.xCoord, Elastica.yCoord, zero_add, sub_zero] at hr ⊢
  rw [hi]
  have he : (fun s => Real.sin (a + θ s)) = (fun s => Real.sin (θ s + a)) := by
    funext s
    rw [add_comm]
  rw [he]
  linarith

theorem splice_point_right {h : ℝ} (hh : 0 < h) (a : ℝ) {θ : ℝ → ℝ}
    (hc : Continuous θ) (hθ : θ 0 = 0) {t : ℝ} (ht : h ≤ t) :
    curvePoint (splice h a θ) t =
      curvePoint (LinearInputCurveWordArc.arcAngle h a) h + rotation a * curvePoint θ (t - h) := by
  apply Complex.ext
  · simp only [curvePoint, Complex.add_re, Complex.mul_re, rotation,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [splice_x_right hh a hc hθ ht]
    ring
  · simp only [curvePoint, Complex.add_im, Complex.mul_im, rotation,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [splice_y_right hh a hc hθ ht]
    ring

theorem curve_endpoint_cons {h : ℝ} (hh : 0 < h) (a : Bool) (w : List Bool) :
    curve h (a :: w) (wordLength h (a :: w)) =
      endpoint (LinearInputCurveWordArc.letterState h a) +
        rotation (letterAngle a) * curve h w (wordLength h w) := by
  rw [wordLength_cons]
  change curvePoint (splice h (letterAngle a) (wordAngle h w)) (h + wordLength h w) = _
  rw [splice_point_right hh _ (wordAngle_continuous hh w) (wordAngle_initial hh w)
    (by linarith [wordLength_nonneg hh w])]
  simp only [add_sub_cancel_left]
  rfl

theorem fold_join (h : ℝ) (w : List Bool) (s : State) :
    w.foldl (fun t a => join t (LinearInputCurveWordArc.letterState h a)) s =
      join s (LinearInputCurveWordRealization.wordState h w) := by
  induction w generalizing s with
  | nil => exact (join_empty s).symm
  | cons a w ih =>
    change w.foldl (fun t a => join t (LinearInputCurveWordArc.letterState h a))
        (join s (LinearInputCurveWordArc.letterState h a)) =
      join s (w.foldl (fun t a => join t (LinearInputCurveWordArc.letterState h a))
        (join emptyState (LinearInputCurveWordArc.letterState h a)))
    rw [empty_join, ih, ih, join_assoc]

theorem wordState_cons (h : ℝ) (a : Bool) (w : List Bool) :
    LinearInputCurveWordRealization.wordState h (a :: w) =
      join (LinearInputCurveWordArc.letterState h a)
        (LinearInputCurveWordRealization.wordState h w) := by
  rw [LinearInputCurveWordRealization.wordState, List.foldl_cons, empty_join, fold_join]

theorem curve_endpoint_wordState {h : ℝ} (hh : 0 < h) (w : List Bool) :
    curve h w (wordLength h w) = endpoint (LinearInputCurveWordRealization.wordState h w) := by
  induction w with
  | nil =>
    simp [curve, curvePoint, wordAngle, wordLength,
      LinearInputCurveWordRealization.wordState, emptyState, endpoint]
    rfl
  | cons a w ih =>
    rw [curve_endpoint_cons hh, ih, wordState_cons, join_endpoint]
    simp [LinearInputCurveWordArc.letterState, LinearInputCurveWordArc.arcState,
      letterAngle, angle, LinearInputCurveWordArc.arcAngle_initial,
      LinearInputCurveWordArc.arcAngle_terminal hh]

theorem splice_deriv_left (h a : ℝ) (θ : ℝ → ℝ) {t : ℝ} (ht : t < h) :
    deriv (splice h a θ) t = a / h := by
  have he : splice h a θ =ᶠ[𝓝 t] LinearInputCurveWordArc.arcAngle h a := by
    filter_upwards [eventually_lt_nhds ht] with s hs
    exact splice_left h a θ hs.le
  rw [he.deriv_eq]
  exact (LinearInputCurveWordArc.arcAngle_derivative h a t).deriv

theorem splice_deriv_right (h a : ℝ) (θ : ℝ → ℝ) {t : ℝ} (ht : h < t) :
    deriv (splice h a θ) t = deriv θ (t - h) := by
  have he : splice h a θ =ᶠ[𝓝 t] (fun s => a + θ (s - h)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    simp [splice, not_le_of_gt hs]
  rw [he.deriv_eq, deriv_const_add, deriv_comp_sub_const]

theorem splice_energy_left_ae {h : ℝ} (hh : 0 < h) (a : ℝ) (θ ε : ℝ → ℝ) :
    (fun s => ε (deriv (splice h a θ) s)) =ᵐ[volume.restrict (Ι 0 h)]
      (fun _ => ε (a / h)) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (volume.ae_ne h)] with s hs hne
  rw [uIoc_of_le hh.le] at hs
  rw [splice_deriv_left h a θ (lt_of_le_of_ne hs.2 hne)]

theorem splice_energy_right_ae (h a : ℝ) (θ ε : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (fun s => ε (deriv (splice h a θ) s)) =ᵐ[volume.restrict (Ι h (h + L))]
      (fun s => ε (deriv θ (s - h))) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le (by linarith : h ≤ h + L)] at hs
  rw [splice_deriv_right h a θ hs.1]

theorem splice_energy_integrable {h : ℝ} (hh : 0 < h) (a : ℝ) (θ ε : ℝ → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hi : IntervalIntegrable (fun s => ε (deriv θ s)) volume 0 L) :
    IntervalIntegrable (fun s => ε (deriv (splice h a θ) s)) volume 0 (h + L) := by
  have hl : IntervalIntegrable (fun s => ε (deriv (splice h a θ) s)) volume 0 h :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ε (a / h)) volume 0 h).congr_ae
      (splice_energy_left_ae hh a θ ε).symm
  have hr0 : IntervalIntegrable (fun s => ε (deriv θ (s - h))) volume h (h + L) := by
    simpa only [zero_add, add_comm L h] using hi.comp_sub_right h
  have hr := hr0.congr_ae (splice_energy_right_ae h a θ ε hL).symm
  exact hl.trans hr

theorem splice_energy {h : ℝ} (hh : 0 < h) (a : ℝ) (θ ε : ℝ → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hi : IntervalIntegrable (fun s => ε (deriv θ s)) volume 0 L) :
    Elastica.energy ε (splice h a θ) (h + L) = h * ε (a / h) + Elastica.energy ε θ L := by
  have hl : IntervalIntegrable (fun s => ε (deriv (splice h a θ) s)) volume 0 h :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ε (a / h)) volume 0 h).congr_ae
      (splice_energy_left_ae hh a θ ε).symm
  have hr0 : IntervalIntegrable (fun s => ε (deriv θ (s - h))) volume h (h + L) := by
    simpa only [zero_add, add_comm L h] using hi.comp_sub_right h
  have hr := hr0.congr_ae (splice_energy_right_ae h a θ ε hL).symm
  unfold Elastica.energy
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr,
    intervalIntegral.integral_congr_ae_restrict (splice_energy_left_ae hh a θ ε),
    intervalIntegral.integral_congr_ae_restrict (splice_energy_right_ae h a θ ε hL)]
  rw [intervalIntegral.integral_comp_sub_right (fun s => ε (deriv θ s)) h]
  simp [smul_eq_mul]

theorem word_energy_integrable {h : ℝ} (hh : 0 < h) (w : List Bool) (ε : ℝ → ℝ) :
    IntervalIntegrable (fun s => ε (deriv (wordAngle h w) s)) volume 0 (wordLength h w) := by
  induction w with
  | nil => simp [wordLength]
  | cons a w ih =>
    rw [wordLength_cons]
    exact splice_energy_integrable hh (letterAngle a) (wordAngle h w) ε
      (wordLength_nonneg hh w) ih

theorem word_energy_cons {h : ℝ} (hh : 0 < h) (a : Bool) (w : List Bool) (ε : ℝ → ℝ) :
    Elastica.energy ε (wordAngle h (a :: w)) (wordLength h (a :: w)) =
      h * ε (letterAngle a / h) + Elastica.energy ε (wordAngle h w) (wordLength h w) := by
  rw [wordLength_cons]
  exact splice_energy hh (letterAngle a) (wordAngle h w) ε (wordLength_nonneg hh w)
    (word_energy_integrable hh w ε)

theorem curve_cost_wordState {h : ℝ} (hh : 0 < h) (w : List Bool) :
    Elastica.energy LinearInputCurveWordArc.quadraticDensity (wordAngle h w) (wordLength h w) =
      cost (LinearInputCurveWordRealization.wordState h w) := by
  induction w with
  | nil => simp [Elastica.energy, wordLength, LinearInputCurveWordRealization.wordState,
      emptyState, cost]
  | cons a w ih =>
    rw [word_energy_cons hh, ih, wordState_cons, join_cost]
    congr 1
    change h * LinearInputCurveWordArc.quadraticDensity (letterAngle a / h) =
      Elastica.energy LinearInputCurveWordArc.quadraticDensity
        (LinearInputCurveWordArc.arcAngle h (letterAngle a)) h
    rw [LinearInputCurveWordArc.arc_quadratic_energy hh]
    unfold LinearInputCurveWordArc.quadraticDensity
    field_simp

theorem curve_angle_wordState {h : ℝ} (hh : 0 < h) (w : List Bool) :
    wordAngle h w (wordLength h w) - wordAngle h w 0 =
      angle (LinearInputCurveWordRealization.wordState h w) := by
  rw [wordAngle_terminal hh, wordAngle_initial hh, sub_zero]
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [totalAngle, wordState_cons, join_angle, ih]
    congr 1
    change letterAngle a = LinearInputCurveWordArc.arcAngle h (letterAngle a) h -
      LinearInputCurveWordArc.arcAngle h (letterAngle a) 0
    rw [LinearInputCurveWordArc.arcAngle_terminal hh, LinearInputCurveWordArc.arcAngle_initial,
      sub_zero]

theorem curvePoint_continuous {θ : ℝ → ℝ} (hc : Continuous θ) : Continuous (curvePoint θ) := by
  have hx := (show Differentiable ℝ (Elastica.xCoord θ 0) from
    fun s => (Elastica.hasDerivAt_xCoord hc 0 s).differentiableAt).continuous
  have hy := (show Differentiable ℝ (Elastica.yCoord θ 0) from
    fun s => (Elastica.hasDerivAt_yCoord hc 0 s).differentiableAt).continuous
  have he : curvePoint θ = fun t => (Elastica.xCoord θ 0 t : ℂ) +
      (Elastica.yCoord θ 0 t : ℂ) * Complex.I := by
    funext t
    apply Complex.ext <;> simp [curvePoint]
  rw [he]
  exact (Complex.continuous_ofReal.comp hx).add
    ((Complex.continuous_ofReal.comp hy).mul continuous_const)

theorem curvePoint_splice_left (h a : ℝ) (θ : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 h) :
    curvePoint (splice h a θ) t = curvePoint (LinearInputCurveWordArc.arcAngle h a) t := by
  apply Complex.ext
  · change Elastica.xCoord (splice h a θ) 0 t = _
    change Elastica.xCoord (splice h a θ) 0 t =
      Elastica.xCoord (LinearInputCurveWordArc.arcAngle h a) 0 t
    simp only [Elastica.xCoord, zero_add]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change Real.cos (splice h a θ s) = _
    rw [splice_left h a θ (hs.2.trans ht.2)]
  · change Elastica.yCoord (splice h a θ) 0 t = _
    change Elastica.yCoord (splice h a θ) 0 t =
      Elastica.yCoord (LinearInputCurveWordArc.arcAngle h a) 0 t
    simp only [Elastica.yCoord, zero_add]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change Real.sin (splice h a θ s) = _
    rw [splice_left h a θ (hs.2.trans ht.2)]

theorem curvePoint_rotation {θ : ℝ → ℝ} (hc : Continuous θ) (a t : ℝ) :
    curvePoint (fun s => a + θ s) t = rotation a * curvePoint θ t := by
  have hx := Elastica.xCoord_add_angle hc a 0 0 0 t
  have hy := Elastica.yCoord_add_angle hc a 0 0 0 t
  have he : (fun s => a + θ s) = (fun s => θ s + a) := by funext s; ring
  rw [he]
  apply Complex.ext
  · simp only [curvePoint, rotation, Complex.mul_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simpa only [sub_zero] using hx
  · simp only [curvePoint, rotation, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp only [sub_zero] at hy
    linarith

def areaIntegrand (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  cross (curvePoint θ t) (rotation (θ t))

def signedArea (θ : ℝ → ℝ) (L : ℝ) : ℝ := (1 / 2) * ∫ t in 0..L, areaIntegrand θ t

theorem areaIntegrand_eq (θ : ℝ → ℝ) (t : ℝ) :
    areaIntegrand θ t = Elastica.xCoord θ 0 t * Real.sin (θ t) -
      Elastica.yCoord θ 0 t * Real.cos (θ t) := by
  simp [areaIntegrand, cross, curvePoint, rotation]

theorem areaIntegrand_continuous {θ : ℝ → ℝ} (hc : Continuous θ) :
    Continuous (areaIntegrand θ) := by
  have hp := curvePoint_continuous hc
  have he : areaIntegrand θ = fun t => (curvePoint θ t).re * Real.sin (θ t) -
      (curvePoint θ t).im * Real.cos (θ t) := by
    funext t
    exact areaIntegrand_eq θ t
  rw [he]
  exact ((Complex.continuous_re.comp hp).mul (Real.continuous_sin.comp hc)).sub
    ((Complex.continuous_im.comp hp).mul (Real.continuous_cos.comp hc))

theorem integral_cross_tangent (z : ℂ) {θ : ℝ → ℝ} (hc : Continuous θ) (L : ℝ) :
    (∫ t in 0..L, cross z (rotation (θ t))) = cross z (curvePoint θ L) := by
  simp only [cross, rotation, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hs : IntervalIntegrable (fun t => z.re * Real.sin (θ t)) volume 0 L :=
    (continuous_const.mul (Real.continuous_sin.comp hc)).intervalIntegrable 0 L
  have hcos : IntervalIntegrable (fun t => z.im * Real.cos (θ t)) volume 0 L :=
    (continuous_const.mul (Real.continuous_cos.comp hc)).intervalIntegrable 0 L
  rw [intervalIntegral.integral_sub hs hcos,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp [curvePoint, Elastica.xCoord, Elastica.yCoord]

theorem splice_areaIntegrand_right {h : ℝ} (hh : 0 < h) (a : ℝ) {θ : ℝ → ℝ}
    (hc : Continuous θ) (hθ : θ 0 = 0) {t : ℝ} (ht : h ≤ t) :
    areaIntegrand (splice h a θ) t =
      cross (curvePoint (LinearInputCurveWordArc.arcAngle h a) h)
        (rotation (a + θ (t - h))) + areaIntegrand θ (t - h) := by
  unfold areaIntegrand
  rw [splice_point_right hh a hc hθ ht, splice_right hh a θ hθ ht,
    rotation_add, cross_add_left, cross_rotation]

theorem signedArea_splice {h : ℝ} (hh : 0 < h) (a : ℝ) {θ : ℝ → ℝ}
    (hc : Continuous θ) (hθ : θ 0 = 0) {L : ℝ} (hL : 0 ≤ L) :
    signedArea (splice h a θ) (h + L) =
      signedArea (LinearInputCurveWordArc.arcAngle h a) h + signedArea θ L +
        cross (curvePoint (LinearInputCurveWordArc.arcAngle h a) h)
          (rotation a * curvePoint θ L) / 2 := by
  have hs := areaIntegrand_continuous (splice_continuous hh a hc hθ)
  have hfirst : (∫ t in 0..h, areaIntegrand (splice h a θ) t) =
      ∫ t in 0..h, areaIntegrand (LinearInputCurveWordArc.arcAngle h a) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hh.le] at ht
    unfold areaIntegrand
    rw [curvePoint_splice_left h a θ ht, splice_left h a θ ht.2]
  have htail : (∫ t in h..(h + L), areaIntegrand (splice h a θ) t) =
      cross (curvePoint (LinearInputCurveWordArc.arcAngle h a) h)
          (rotation a * curvePoint θ L) + ∫ t in 0..L, areaIntegrand θ t := by
    calc
      _ = ∫ t in h..(h + L),
          cross (curvePoint (LinearInputCurveWordArc.arcAngle h a) h)
            (rotation (a + θ (t - h))) + areaIntegrand θ (t - h) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : h ≤ h + L)] at ht
        exact splice_areaIntegrand_right hh a hc hθ ht.1
      _ = ∫ t in 0..L,
          cross (curvePoint (LinearInputCurveWordArc.arcAngle h a) h)
            (rotation (a + θ t)) + areaIntegrand θ t := by
        rw [intervalIntegral.integral_comp_sub_right
          (fun t => cross (curvePoint (LinearInputCurveWordArc.arcAngle h a) h)
            (rotation (a + θ t)) + areaIntegrand θ t) h]
        simp
      _ = _ := by
        have hcrot : Continuous (fun t => cross (curvePoint (LinearInputCurveWordArc.arcAngle h a) h)
            (rotation (a + θ t))) := by
          simp only [cross, rotation, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          fun_prop
        have hca : Continuous (fun t => a + θ t) := continuous_const.add hc
        rw [intervalIntegral.integral_add (hcrot.intervalIntegrable 0 L)
          ((areaIntegrand_continuous hc).intervalIntegrable 0 L),
          integral_cross_tangent _ hca, curvePoint_rotation hc]
  unfold signedArea
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hs.intervalIntegrable 0 h) (hs.intervalIntegrable h (h + L)), hfirst, htail]
  ring

def areaLetterState (h : ℝ) (a : Bool) : AreaState :=
  (LinearInputCurveWordArc.letterState h a,
    signedArea (LinearInputCurveWordArc.arcAngle h (letterAngle a)) h)

def areaWordState (h : ℝ) : List Bool → AreaState
  | [] => (emptyState, 0)
  | a :: w => joinArea (areaLetterState h a) (areaWordState h w)

theorem areaWordState_first (h : ℝ) (w : List Bool) :
    (areaWordState h w).1 = LinearInputCurveWordRealization.wordState h w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [areaWordState, joinArea, areaLetterState, ih, wordState_cons]

set_option backward.isDefEq.respectTransparency false in
theorem curve_area_wordState {h : ℝ} (hh : 0 < h) (w : List Bool) :
    signedArea (wordAngle h w) (wordLength h w) = (areaWordState h w).2 := by
  induction w with
  | nil => simp [signedArea, wordLength, areaWordState]
  | cons a w ih =>
    rw [wordLength_cons]
    change signedArea (splice h (letterAngle a) (wordAngle h w)) (h + wordLength h w) = _
    rw [signedArea_splice hh _ (wordAngle_continuous hh w) (wordAngle_initial hh w)
      (wordLength_nonneg hh w), ih]
    simp only [areaWordState, joinArea, areaLetterState, areaCocycle, areaWordState_first]
    apply congrArg (fun z : ℝ =>
      signedArea (LinearInputCurveWordArc.arcAngle h (letterAngle a)) h +
        (areaWordState h w).2 + z)
    rw [← curve_endpoint_wordState hh]
    have ha : angle (LinearInputCurveWordArc.letterState h a) = letterAngle a := by
      change LinearInputCurveWordArc.arcAngle h (letterAngle a) h -
        LinearInputCurveWordArc.arcAngle h (letterAngle a) 0 = _
      rw [LinearInputCurveWordArc.arcAngle_terminal hh,
        LinearInputCurveWordArc.arcAngle_initial, sub_zero]
    rw [ha]
    rfl

def reconstructedState (h : ℝ) (w : List Bool) : State :=
  (curve h w (wordLength h w),
   wordAngle h w (wordLength h w) - wordAngle h w 0,
   Elastica.energy LinearInputCurveWordArc.quadraticDensity (wordAngle h w) (wordLength h w))

theorem reconstructedState_eq_wordState {h : ℝ} (hh : 0 < h) (w : List Bool) :
    reconstructedState h w = LinearInputCurveWordRealization.wordState h w := by
  apply state_ext
  · exact curve_endpoint_wordState hh w
  · exact curve_angle_wordState hh w
  · exact curve_cost_wordState hh w

theorem reconstructedState_eq_integer_decode {h : ℝ} (hh : 0 < h) (w : List Bool) :
    reconstructedState h w =
      LinearInputCurveWordRealization.decode h (LinearInputCurveWordFinite.state w) := by
  rw [reconstructedState_eq_wordState hh, LinearInputCurveWordRealization.wordState_eq_decode hh]

theorem reconstructedAreaState_eq {h : ℝ} (hh : 0 < h) (w : List Bool) :
    (reconstructedState h w, signedArea (wordAngle h w) (wordLength h w)) = areaWordState h w := by
  apply Prod.ext
  · rw [areaWordState_first, reconstructedState_eq_wordState hh]
  · exact curve_area_wordState hh w

/-- Intrinsic signed areas of the separate pieces, before translation. -/
def intrinsicArea (h : ℝ) : List Bool → ℝ
  | [] => 0
  | a :: w => (areaLetterState h a).2 + intrinsicArea h w

/-- Decode the integer cross term with the actual intrinsic arc-area sum. -/
def decodeArea (h : ℝ) (s : LinearInputCurveWordFinite.State) (intrinsic : ℝ) : AreaState :=
  (LinearInputCurveWordRealization.decode h s,
   intrinsic + LinearInputCurveWordArc.endpointUnit h ^ 2 / 2 * (s.2.2.2 : ℝ))

theorem lattice_area_step {h : ℝ} (hh : 0 < h)
    (s : LinearInputCurveWordFinite.State) (a : Bool) :
    areaCocycle (LinearInputCurveWordRealization.decode h s)
        (LinearInputCurveWordArc.letterState h a) =
      LinearInputCurveWordArc.endpointUnit h ^ 2 / 2 *
        (((LinearInputCurveWordFinite.step s a).2.2.2 : ℝ) - (s.2.2.2 : ℝ)) := by
  rw [areaCocycle, LinearInputCurveWordRealization.decode_endpoint,
    LinearInputCurveWordRealization.decode_angle,
    LinearInputCurveWordRealization.letter_endpoint hh,
    ← LinearInputCurveWordRealization.rotation_matches_lattice]
  simp only [cross, LinearInputCurveWordRealization.point,
    LinearInputCurveWordFinite.step, Int.cast_sub, Int.cast_add, Int.cast_mul]
  ring

theorem decodeArea_step {h : ℝ} (hh : 0 < h)
    (s : LinearInputCurveWordFinite.State) (intrinsic : ℝ) (a : Bool) :
    joinArea (decodeArea h s intrinsic) (areaLetterState h a) =
      decodeArea h (LinearInputCurveWordFinite.step s a)
        (intrinsic + (areaLetterState h a).2) := by
  apply Prod.ext
  · exact (LinearInputCurveWordRealization.decode_step hh s a).symm
  · change intrinsic + LinearInputCurveWordArc.endpointUnit h ^ 2 / 2 * (s.2.2.2 : ℝ) +
        (areaLetterState h a).2 +
        areaCocycle (LinearInputCurveWordRealization.decode h s)
          (LinearInputCurveWordArc.letterState h a) = _
    rw [lattice_area_step hh]
    dsimp [decodeArea]
    ring

theorem empty_joinArea (s : AreaState) : joinArea (emptyState, 0) s = s := by
  apply Prod.ext
  · exact empty_join s.1
  · simp [joinArea, areaCocycle, emptyState, endpoint, cross]

theorem joinArea_empty (s : AreaState) : joinArea s (emptyState, 0) = s := by
  apply Prod.ext
  · exact join_empty s.1
  · simp [joinArea, areaCocycle, emptyState, endpoint, cross]

theorem area_fold_join (h : ℝ) (w : List Bool) (s : AreaState) :
    w.foldl (fun z a => joinArea z (areaLetterState h a)) s =
      joinArea s (areaWordState h w) := by
  induction w generalizing s with
  | nil => exact (joinArea_empty s).symm
  | cons a w ih =>
    rw [List.foldl_cons, ih]
    exact joinArea_assoc s (areaLetterState h a) (areaWordState h w)

theorem decodeArea_fold {h : ℝ} (hh : 0 < h) (w : List Bool)
    (s : LinearInputCurveWordFinite.State) (intrinsic : ℝ) :
    w.foldl (fun z a => joinArea z (areaLetterState h a)) (decodeArea h s intrinsic) =
      decodeArea h (w.foldl LinearInputCurveWordFinite.step s)
        (intrinsic + intrinsicArea h w) := by
  induction w generalizing s intrinsic with
  | nil => simp [intrinsicArea]
  | cons a w ih =>
    rw [List.foldl_cons, decodeArea_step hh, ih]
    simp only [List.foldl_cons, intrinsicArea, add_assoc]

theorem areaWordState_eq_integer_decode {h : ℝ} (hh : 0 < h) (w : List Bool) :
    areaWordState h w = decodeArea h (LinearInputCurveWordFinite.state w) (intrinsicArea h w) := by
  have he : decodeArea h ((0, 0), 0, 0, 0) 0 = (emptyState, 0) := by
    simp [decodeArea, LinearInputCurveWordRealization.decode_empty]
  have hf := decodeArea_fold hh w ((0, 0), 0, 0, 0) 0
  rw [he, area_fold_join, empty_joinArea] at hf
  simpa only [zero_add, LinearInputCurveWordFinite.state] using hf

theorem curve_area_integer_formula {h : ℝ} (hh : 0 < h) (w : List Bool) :
    signedArea (wordAngle h w) (wordLength h w) =
      intrinsicArea h w + LinearInputCurveWordArc.endpointUnit h ^ 2 / 2 *
        (LinearInputCurveWordFinite.crossArea w : ℝ) := by
  rw [curve_area_wordState hh, areaWordState_eq_integer_decode hh]
  rfl

theorem reconstructedAreaState_eq_integer_decode {h : ℝ} (hh : 0 < h) (w : List Bool) :
    (reconstructedState h w, signedArea (wordAngle h w) (wordLength h w)) =
      decodeArea h (LinearInputCurveWordFinite.state w) (intrinsicArea h w) := by
  rw [reconstructedAreaState_eq hh, areaWordState_eq_integer_decode hh]

def sixWordLeft : List Bool := [true, true, false, false, false, true]

def sixWordRight : List Bool := [false, true, true, true, false, false]

theorem six_word_intrinsicArea (h : ℝ) :
    intrinsicArea h sixWordLeft = intrinsicArea h sixWordRight := by
  simp only [sixWordLeft, sixWordRight, intrinsicArea]
  ring

theorem six_word_same_state {h : ℝ} (hh : 0 < h) :
    reconstructedState h sixWordLeft = reconstructedState h sixWordRight := by
  rw [reconstructedState_eq_integer_decode hh, reconstructedState_eq_integer_decode hh]
  have hs : LinearInputCurveWordFinite.firstState sixWordLeft =
      LinearInputCurveWordFinite.firstState sixWordRight := by decide
  apply state_ext
  · have hp := congrArg Prod.fst hs
    exact congrArg (LinearInputCurveWordRealization.point h) hp
  · have ha := congrArg (fun s => s.2.1) hs
    exact congrArg (fun n : ℕ => (n : ℝ) * (Real.pi / 2)) ha
  · have hc := congrArg (fun s => s.2.2) hs
    exact congrArg (fun n : ℕ => LinearInputCurveWordArc.costUnit h * (n : ℝ)) hc

theorem six_word_actual_area_difference {h : ℝ} (hh : 0 < h) :
    signedArea (wordAngle h sixWordRight) (wordLength h sixWordRight) -
      signedArea (wordAngle h sixWordLeft) (wordLength h sixWordLeft) =
      32 * h ^ 2 / (9 * Real.pi ^ 2) := by
  rw [curve_area_integer_formula hh, curve_area_integer_formula hh, six_word_intrinsicArea]
  have hL : LinearInputCurveWordFinite.crossArea sixWordLeft = 8 := by decide
  have hR : LinearInputCurveWordFinite.crossArea sixWordRight = 24 := by decide
  rw [hL, hR]
  norm_num only [Int.cast_ofNat]
  unfold LinearInputCurveWordArc.endpointUnit
  field_simp
  ring

theorem six_word_actual_areas_distinct {h : ℝ} (hh : 0 < h) :
    signedArea (wordAngle h sixWordRight) (wordLength h sixWordRight) ≠
      signedArea (wordAngle h sixWordLeft) (wordLength h sixWordLeft) := by
  apply sub_ne_zero.mp
  rw [six_word_actual_area_difference hh]
  positivity

end LinearInputCurveWordPiecewise
