/-!
Curve-level identification of the eight-letter collision words.
The parameters below are physical arc length; the circular models use angle.
-/

noncomputable section

namespace LinearInputCurveWordCircleWords

open Real Set MeasureTheory
open LinearInputCurveWordPiecewise

def sequentialWord : List Bool := [true, true, true, true, false, false, false, false]

def insertedWord : List Bool := [true, true, true, false, false, false, false, true]

def curvatureA (h : ℝ) : ℝ := (Real.pi / 2) / h

def curvatureB (h : ℝ) : ℝ := (3 * Real.pi / 2) / h

theorem sequential_angle_first {h t : ℝ} (hh : 0 < h) (ht : t ≤ 4 * h) :
    wordAngle h sequentialWord t = curvatureA h * t := by
  dsimp [sequentialWord, wordAngle, splice, letterAngle, LinearInputCurveWordArc.arcAngle,
    curvatureA]
  split_ifs <;> solve | (exfalso; linarith) | field_simp | (field_simp; ring)

theorem sequential_angle_second {h t : ℝ} (hh : 0 < h)
    (ht0 : 4 * h ≤ t) (ht1 : t ≤ 8 * h) :
    wordAngle h sequentialWord t = 2 * Real.pi + curvatureB h * (t - 4 * h) := by
  dsimp [sequentialWord, wordAngle, splice, letterAngle, LinearInputCurveWordArc.arcAngle,
    curvatureB]
  split_ifs <;> solve | (exfalso; linarith) | field_simp | (field_simp; ring) | (field_simp; linarith)

theorem inserted_angle_first {h t : ℝ} (hh : 0 < h) (ht : t ≤ 3 * h) :
    wordAngle h insertedWord t = curvatureA h * t := by
  dsimp [insertedWord, wordAngle, splice, letterAngle, LinearInputCurveWordArc.arcAngle,
    curvatureA]
  split_ifs <;> solve | (exfalso; linarith) | field_simp | (field_simp; ring)

theorem inserted_angle_middle {h t : ℝ} (hh : 0 < h)
    (ht0 : 3 * h ≤ t) (ht1 : t ≤ 7 * h) :
    wordAngle h insertedWord t = 3 * Real.pi / 2 + curvatureB h * (t - 3 * h) := by
  dsimp [insertedWord, wordAngle, splice, letterAngle, LinearInputCurveWordArc.arcAngle,
    curvatureB]
  split_ifs <;> solve | (exfalso; linarith) | field_simp | (field_simp; ring) | (field_simp; linarith)

theorem inserted_angle_last {h t : ℝ} (hh : 0 < h)
    (ht0 : 7 * h ≤ t) (ht1 : t ≤ 8 * h) :
    wordAngle h insertedWord t = 15 * Real.pi / 2 + curvatureA h * (t - 7 * h) := by
  dsimp [insertedWord, wordAngle, splice, letterAngle, LinearInputCurveWordArc.arcAngle,
    curvatureA]
  split_ifs <;> solve | (exfalso; linarith) | field_simp | (field_simp; ring) | (field_simp; linarith)

def circlePoint (c d R a : ℝ) : ℂ :=
  ⟨LinearInputCurveWordCircularMoment.circleX c R a,
    LinearInputCurveWordCircularMoment.circleY d R a⟩

theorem point_on_circle_segment {θ : ℝ → ℝ} (hc : Continuous θ)
    (s t a κ c d R : ℝ) (hst : s ≤ t) (hR : R * κ = 1)
    (hstart : curvePoint θ s = circlePoint c d R a)
    (hθ : ∀ u ∈ Icc s t, θ u = a + κ * (u - s)) :
    curvePoint θ t = circlePoint c d R (a + κ * (t - s)) := by
  have hphase (u : ℝ) : HasDerivAt (fun v => a + κ * (v - s)) κ u := by
    simpa only [mul_one] using (((hasDerivAt_id u).sub_const s).const_mul κ).const_add a
  have hxder (u : ℝ) (hu : u ∈ uIcc s t) :
      HasDerivAt (fun v => LinearInputCurveWordCircularMoment.circleX c R (a + κ * (v - s)))
        (Real.cos (θ u)) u := by
    have hd := (LinearInputCurveWordCircularMoment.circleX_hasDerivAt c R
      (a + κ * (u - s))).comp u (hphase u)
    have hm : (R * Real.cos (a + κ * (u - s))) * κ = Real.cos (θ u) := by
      rw [uIcc_of_le hst] at hu
      rw [hθ u hu]
      calc
        _ = (R * κ) * Real.cos (a + κ * (u - s)) := by ring
        _ = _ := by rw [hR, one_mul]
    rw [hm] at hd
    exact hd
  have hyder (u : ℝ) (hu : u ∈ uIcc s t) :
      HasDerivAt (fun v => LinearInputCurveWordCircularMoment.circleY d R (a + κ * (v - s)))
        (Real.sin (θ u)) u := by
    have hd := (LinearInputCurveWordCircularMoment.circleY_hasDerivAt d R
      (a + κ * (u - s))).comp u (hphase u)
    have hm : (R * Real.sin (a + κ * (u - s))) * κ = Real.sin (θ u) := by
      rw [uIcc_of_le hst] at hu
      rw [hθ u hu]
      calc
        _ = (R * κ) * Real.sin (a + κ * (u - s)) := by ring
        _ = _ := by rw [hR, one_mul]
    rw [hm] at hd
    exact hd
  have hx := intervalIntegral.integral_eq_sub_of_hasDerivAt hxder
    ((Real.continuous_cos.comp hc).intervalIntegrable s t)
  have hy := intervalIntegral.integral_eq_sub_of_hasDerivAt hyder
    ((Real.continuous_sin.comp hc).intervalIntegrable s t)
  have hx0 := congrArg Complex.re hstart
  have hy0 := congrArg Complex.im hstart
  have hxi := Elastica.xCoord_sub_eq_integral hc 0 s t
  have hyi := Elastica.yCoord_sub_eq_integral hc 0 s t
  simp only [sub_self, mul_zero, add_zero] at hx hy
  apply Complex.ext
  · change Elastica.xCoord θ 0 t = _
    change Elastica.xCoord θ 0 s = _ at hx0
    dsimp only [circlePoint] at hx0 ⊢
    linarith
  · change Elastica.yCoord θ 0 t = _
    change Elastica.yCoord θ 0 s = _ at hy0
    dsimp only [circlePoint] at hy0 ⊢
    linarith

def radiusB (h : ℝ) : ℝ := LinearInputCurveWordArc.endpointUnit h

theorem radiusA_curvatureA {h : ℝ} (hh : 0 < h) : 3 * radiusB h * curvatureA h = 1 := by
  unfold radiusB LinearInputCurveWordArc.endpointUnit curvatureA
  field_simp [ne_of_gt hh, Real.pi_ne_zero]

theorem radiusB_curvatureB {h : ℝ} (hh : 0 < h) : radiusB h * curvatureB h = 1 := by
  unfold radiusB LinearInputCurveWordArc.endpointUnit curvatureB
  field_simp [ne_of_gt hh, Real.pi_ne_zero]

theorem circlePoint_zero (R : ℝ) : circlePoint 0 R R 0 = 0 := by
  apply Complex.ext <;> simp [circlePoint, LinearInputCurveWordCircularMoment.circleX,
    LinearInputCurveWordCircularMoment.circleY]

theorem sequential_curve_first {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc 0 (4 * h)) :
    curve h sequentialWord t = circlePoint 0 (3 * radiusB h) (3 * radiusB h) (curvatureA h * t) := by
  have hs : curvePoint (wordAngle h sequentialWord) 0 = circlePoint 0 (3 * radiusB h) (3 * radiusB h) 0 := by
    rw [circlePoint_zero]
    apply Complex.ext <;> simp [curvePoint]
  have hp := point_on_circle_segment (wordAngle_continuous hh sequentialWord)
    0 t 0 (curvatureA h) 0 (3 * radiusB h) (3 * radiusB h) ht.1 (radiusA_curvatureA hh) hs
    (fun u hu => by simpa using sequential_angle_first hh (hu.2.trans ht.2))
  simpa [curve] using hp

theorem inserted_curve_first {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc 0 (3 * h)) :
    curve h insertedWord t = circlePoint 0 (3 * radiusB h) (3 * radiusB h) (curvatureA h * t) := by
  have hs : curvePoint (wordAngle h insertedWord) 0 = circlePoint 0 (3 * radiusB h) (3 * radiusB h) 0 := by
    rw [circlePoint_zero]
    apply Complex.ext <;> simp [curvePoint]
  have hp := point_on_circle_segment (wordAngle_continuous hh insertedWord)
    0 t 0 (curvatureA h) 0 (3 * radiusB h) (3 * radiusB h) ht.1 (radiusA_curvatureA hh) hs
    (fun u hu => by simpa using inserted_angle_first hh (hu.2.trans ht.2))
  simpa [curve] using hp

theorem circlePoint_full_turns (c d R a : ℝ) (n : ℕ) :
    circlePoint c d R (a + (n : ℝ) * (2 * Real.pi)) = circlePoint c d R a := by
  apply Complex.ext <;>
    simp [circlePoint, LinearInputCurveWordCircularMoment.circleX,
      LinearInputCurveWordCircularMoment.circleY, Real.sin_add_nat_mul_two_pi,
      Real.cos_add_nat_mul_two_pi]

theorem sequential_join {h : ℝ} (hh : 0 < h) : curve h sequentialWord (4 * h) = 0 := by
  rw [sequential_curve_first hh ⟨by positivity, le_rfl⟩]
  have ha : curvatureA h * (4 * h) = 2 * Real.pi := by
    unfold curvatureA
    field_simp
    norm_num
  rw [ha]
  apply Complex.ext <;> simp [circlePoint, LinearInputCurveWordCircularMoment.circleX,
    LinearInputCurveWordCircularMoment.circleY]

theorem sequential_curve_second {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc (4 * h) (8 * h)) :
    curve h sequentialWord t = circlePoint 0 (radiusB h) (radiusB h) (curvatureB h * (t - 4 * h)) := by
  have hs : curvePoint (wordAngle h sequentialWord) (4 * h) =
      circlePoint 0 (radiusB h) (radiusB h) (2 * Real.pi) := by
    change curve h sequentialWord (4 * h) = _
    rw [sequential_join hh]
    apply Complex.ext <;> simp [circlePoint, LinearInputCurveWordCircularMoment.circleX,
      LinearInputCurveWordCircularMoment.circleY]
  have hp := point_on_circle_segment (wordAngle_continuous hh sequentialWord)
    (4 * h) t (2 * Real.pi) (curvatureB h) 0 (radiusB h) (radiusB h)
    ht.1 (radiusB_curvatureB hh) hs
    (fun u hu => sequential_angle_second hh hu.1 (hu.2.trans ht.2))
  change curve h sequentialWord t = _ at hp
  rw [hp]
  simpa only [Nat.cast_one, one_mul, add_comm] using
    circlePoint_full_turns 0 (radiusB h) (radiusB h) (curvatureB h * (t - 4 * h)) 1

theorem circlePoint_insertion (R : ℝ) :
    circlePoint 0 (3 * R) (3 * R) (3 * Real.pi / 2) =
      circlePoint (-2 * R) (3 * R) R (3 * Real.pi / 2) := by
  have hi := LinearInputCurveWordCircularMoment.insertion_position R
  apply Complex.ext
  · exact congrArg Prod.fst hi
  · exact congrArg Prod.snd hi

theorem inserted_join_first {h : ℝ} (hh : 0 < h) :
    curve h insertedWord (3 * h) =
      circlePoint (-2 * radiusB h) (3 * radiusB h) (radiusB h) (3 * Real.pi / 2) := by
  rw [inserted_curve_first hh ⟨by positivity, le_rfl⟩]
  have ha : curvatureA h * (3 * h) = 3 * Real.pi / 2 := by
    unfold curvatureA
    field_simp
  rw [ha, circlePoint_insertion]

theorem inserted_curve_middle {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc (3 * h) (7 * h)) :
    curve h insertedWord t = circlePoint (-2 * radiusB h) (3 * radiusB h) (radiusB h)
      (3 * Real.pi / 2 + curvatureB h * (t - 3 * h)) := by
  exact point_on_circle_segment (wordAngle_continuous hh insertedWord)
    (3 * h) t (3 * Real.pi / 2) (curvatureB h) (-2 * radiusB h) (3 * radiusB h) (radiusB h)
    ht.1 (radiusB_curvatureB hh) (inserted_join_first hh)
    (fun u hu => inserted_angle_middle hh hu.1 (hu.2.trans ht.2))

theorem inserted_join_second {h : ℝ} (hh : 0 < h) :
    curve h insertedWord (7 * h) =
      circlePoint 0 (3 * radiusB h) (3 * radiusB h) (15 * Real.pi / 2) := by
  rw [inserted_curve_middle hh ⟨by linarith, le_rfl⟩]
  have ha : curvatureB h * (7 * h - 3 * h) = 6 * Real.pi := by
    unfold curvatureB
    field_simp
    ring
  rw [ha]
  have hB := circlePoint_full_turns (-2 * radiusB h) (3 * radiusB h) (radiusB h) (3 * Real.pi / 2) 3
  have hA := circlePoint_full_turns 0 (3 * radiusB h) (3 * radiusB h) (3 * Real.pi / 2) 3
  norm_num only [Nat.cast_ofNat] at hB hA
  rw [show (3 : ℝ) * (2 * Real.pi) = 6 * Real.pi by ring] at hB hA
  rw [hB, ← circlePoint_insertion, show 15 * Real.pi / 2 = 3 * Real.pi / 2 + 6 * Real.pi by ring, hA]

theorem inserted_curve_last {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc (7 * h) (8 * h)) :
    curve h insertedWord t = circlePoint 0 (3 * radiusB h) (3 * radiusB h)
      (3 * Real.pi / 2 + curvatureA h * (t - 7 * h)) := by
  have hp := point_on_circle_segment (wordAngle_continuous hh insertedWord)
    (7 * h) t (15 * Real.pi / 2) (curvatureA h) 0 (3 * radiusB h) (3 * radiusB h)
    ht.1 (radiusA_curvatureA hh) (inserted_join_second hh)
    (fun u hu => inserted_angle_last hh hu.1 (hu.2.trans ht.2))
  change curve h insertedWord t = _ at hp
  rw [hp]
  have hperiod := circlePoint_full_turns 0 (3 * radiusB h) (3 * radiusB h)
    (3 * Real.pi / 2 + curvatureA h * (t - 7 * h)) 3
  norm_num only [Nat.cast_ofNat] at hperiod
  convert hperiod using 1
  congr 1
  ring

def curveMoment (θ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ u in s..t, Elastica.xCoord θ 0 u ^ 2 * deriv (Elastica.yCoord θ 0) u

theorem curveMoment_integrand {θ : ℝ → ℝ} (hc : Continuous θ) (s t : ℝ) :
    curveMoment θ s t = ∫ u in s..t, Elastica.xCoord θ 0 u ^ 2 * Real.sin (θ u) := by
  simp only [curveMoment, Elastica.deriv_yCoord hc]

theorem curveMoment_add {θ : ℝ → ℝ} (hc : Continuous θ) (s t v : ℝ) :
    curveMoment θ s t + curveMoment θ t v = curveMoment θ s v := by
  simp only [curveMoment_integrand hc]
  have hx : Continuous (Elastica.xCoord θ 0) :=
    (show Differentiable ℝ (Elastica.xCoord θ 0) from
      fun u => (Elastica.hasDerivAt_xCoord hc 0 u).differentiableAt).continuous
  have hi : Continuous (fun u => Elastica.xCoord θ 0 u ^ 2 * Real.sin (θ u)) :=
    (hx.pow 2).mul (Real.continuous_sin.comp hc)
  exact intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable s t) (hi.intervalIntegrable t v)

theorem circleMoment_arclength (s t a κ c d R : ℝ) (hR : R * κ = 1) :
    (∫ u in s..t, LinearInputCurveWordCircularMoment.circleX c R (a + κ * (u - s)) ^ 2 *
      Real.sin (a + κ * (u - s))) =
    LinearInputCurveWordCircularMoment.circleMoment c d R a (a + κ * (t - s)) := by
  have hd (u : ℝ) : HasDerivAt (fun v => a + κ * (v - s)) κ u := by
    simpa only [mul_one] using (((hasDerivAt_id u).sub_const s).const_mul κ).const_add a
  have hg : Continuous (fun u => LinearInputCurveWordCircularMoment.circleX c R u ^ 2 *
      (R * Real.sin u)) := by
    unfold LinearInputCurveWordCircularMoment.circleX
    fun_prop
  have hv := intervalIntegral.integral_comp_mul_deriv
    (a := s) (b := t) (g := fun u => LinearInputCurveWordCircularMoment.circleX c R u ^ 2 *
      (R * Real.sin u)) (fun u _ => hd u) continuous_const.continuousOn hg
  simp only [Function.comp_apply, sub_self, mul_zero, add_zero] at hv
  change _ = ∫ u in a..a + κ * (t - s), (c + R * Real.sin u) ^ 2 * (R * Real.sin u) at hv
  rw [← LinearInputCurveWordCircularMoment.circleMoment_integrand] at hv
  rw [← hv]
  apply intervalIntegral.integral_congr
  intro u _
  change _ = (LinearInputCurveWordCircularMoment.circleX c R (a + κ * (u - s)) ^ 2 *
    (R * Real.sin (a + κ * (u - s)))) * κ
  calc
    _ = LinearInputCurveWordCircularMoment.circleX c R (a + κ * (u - s)) ^ 2 *
        ((R * κ) * Real.sin (a + κ * (u - s))) := by rw [hR, one_mul]
    _ = _ := by ring

theorem curveMoment_circle_segment {θ : ℝ → ℝ} (hc : Continuous θ)
    (s t a κ c d R : ℝ) (hst : s ≤ t) (hR : R * κ = 1)
    (hp : ∀ u ∈ Icc s t, curvePoint θ u = circlePoint c d R (a + κ * (u - s)))
    (hsin : ∀ u ∈ Icc s t, Real.sin (θ u) = Real.sin (a + κ * (u - s))) :
    curveMoment θ s t = LinearInputCurveWordCircularMoment.circleMoment c d R a
      (a + κ * (t - s)) := by
  rw [curveMoment_integrand hc, ← circleMoment_arclength s t a κ c d R hR]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hst] at hu
  have hx := congrArg Complex.re (hp u hu)
  change Elastica.xCoord θ 0 u = _ at hx
  change Elastica.xCoord θ 0 u ^ 2 * Real.sin (θ u) = _
  rw [hx, hsin u hu]
  rfl

def curveArea (θ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (1 / 2) * ∫ u in s..t, areaIntegrand θ u

theorem curveArea_add {θ : ℝ → ℝ} (hc : Continuous θ) (s t v : ℝ) :
    curveArea θ s t + curveArea θ t v = curveArea θ s v := by
  unfold curveArea
  rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals
    ((areaIntegrand_continuous hc).intervalIntegrable s t)
    ((areaIntegrand_continuous hc).intervalIntegrable t v)]

theorem circleArea_arclength (s t a κ c d R : ℝ) (hR : R * κ = 1) :
    (1 / 2) * (∫ u in s..t,
      LinearInputCurveWordCircularMoment.circleX c R (a + κ * (u - s)) *
          Real.sin (a + κ * (u - s)) -
        LinearInputCurveWordCircularMoment.circleY d R (a + κ * (u - s)) *
          Real.cos (a + κ * (u - s))) =
    LinearInputCurveWordCircularMoment.circleArea c d R a (a + κ * (t - s)) := by
  have hd (u : ℝ) : HasDerivAt (fun v => a + κ * (v - s)) κ u := by
    simpa only [mul_one] using (((hasDerivAt_id u).sub_const s).const_mul κ).const_add a
  have hg : Continuous (fun u =>
      LinearInputCurveWordCircularMoment.circleX c R u * (R * Real.sin u) -
        LinearInputCurveWordCircularMoment.circleY d R u * (R * Real.cos u)) := by
    unfold LinearInputCurveWordCircularMoment.circleX LinearInputCurveWordCircularMoment.circleY
    fun_prop
  have hv := intervalIntegral.integral_comp_mul_deriv (a := s) (b := t)
    (g := fun u => LinearInputCurveWordCircularMoment.circleX c R u * (R * Real.sin u) -
      LinearInputCurveWordCircularMoment.circleY d R u * (R * Real.cos u))
    (fun u _ => hd u) continuous_const.continuousOn hg
  simp only [Function.comp_apply, sub_self, mul_zero, add_zero] at hv
  unfold LinearInputCurveWordCircularMoment.circleArea
  simp only [LinearInputCurveWordCircularMoment.circleX_deriv,
    LinearInputCurveWordCircularMoment.circleY_deriv]
  rw [← hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  change _ = (_ * (R * Real.sin (a + κ * (u - s))) -
    _ * (R * Real.cos (a + κ * (u - s)))) * κ
  calc
    _ = LinearInputCurveWordCircularMoment.circleX c R (a + κ * (u - s)) *
          ((R * κ) * Real.sin (a + κ * (u - s))) -
        LinearInputCurveWordCircularMoment.circleY d R (a + κ * (u - s)) *
          ((R * κ) * Real.cos (a + κ * (u - s))) := by rw [hR, one_mul, one_mul]
    _ = _ := by ring

theorem curveArea_circle_segment {θ : ℝ → ℝ}
    (s t a κ c d R : ℝ) (hst : s ≤ t) (hR : R * κ = 1)
    (hp : ∀ u ∈ Icc s t, curvePoint θ u = circlePoint c d R (a + κ * (u - s)))
    (hsin : ∀ u ∈ Icc s t, Real.sin (θ u) = Real.sin (a + κ * (u - s)))
    (hcos : ∀ u ∈ Icc s t, Real.cos (θ u) = Real.cos (a + κ * (u - s))) :
    curveArea θ s t = LinearInputCurveWordCircularMoment.circleArea c d R a
      (a + κ * (t - s)) := by
  rw [curveArea, ← circleArea_arclength s t a κ c d R hR]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hst] at hu
  have hx := congrArg Complex.re (hp u hu)
  have hy := congrArg Complex.im (hp u hu)
  change Elastica.xCoord θ 0 u = _ at hx
  change Elastica.yCoord θ 0 u = _ at hy
  rw [areaIntegrand_eq, hx, hy, hsin u hu, hcos u hu]
  rfl

theorem curve_integrals_circle_segment {θ : ℝ → ℝ} (hc : Continuous θ)
    (s t a κ c d R : ℝ) (hst : s ≤ t) (hR : R * κ = 1)
    (hp : ∀ u ∈ Icc s t, curvePoint θ u = circlePoint c d R (a + κ * (u - s)))
    (hsin : ∀ u ∈ Icc s t, Real.sin (θ u) = Real.sin (a + κ * (u - s)))
    (hcos : ∀ u ∈ Icc s t, Real.cos (θ u) = Real.cos (a + κ * (u - s))) :
    curveMoment θ s t = LinearInputCurveWordCircularMoment.circleMoment c d R a
        (a + κ * (t - s)) ∧
      curveArea θ s t = LinearInputCurveWordCircularMoment.circleArea c d R a
        (a + κ * (t - s)) :=
  ⟨curveMoment_circle_segment hc s t a κ c d R hst hR hp hsin,
    curveArea_circle_segment s t a κ c d R hst hR hp hsin hcos⟩

open LinearInputCurveWordCircularMoment

theorem sequential_integrals_first {h : ℝ} (hh : 0 < h) :
    curveMoment (wordAngle h sequentialWord) 0 (4 * h) =
        circleMoment 0 (3 * radiusB h) (3 * radiusB h) 0 (2 * Real.pi) ∧
      curveArea (wordAngle h sequentialWord) 0 (4 * h) =
        circleArea 0 (3 * radiusB h) (3 * radiusB h) 0 (2 * Real.pi) := by
  have hs := curve_integrals_circle_segment (wordAngle_continuous hh sequentialWord)
    0 (4 * h) 0 (curvatureA h) 0 (3 * radiusB h) (3 * radiusB h) (by positivity)
    (radiusA_curvatureA hh)
    (by intro u hu; simpa only [zero_add, sub_zero] using sequential_curve_first hh hu)
    (by intro u hu; rw [sequential_angle_first hh hu.2]; simp only [zero_add, sub_zero])
    (by intro u hu; rw [sequential_angle_first hh hu.2]; simp only [zero_add, sub_zero])
  have ha : curvatureA h * (4 * h) = 2 * Real.pi := by
    unfold curvatureA
    field_simp
    norm_num
  simpa only [zero_add, sub_zero, ha] using hs

theorem sequential_integrals_second {h : ℝ} (hh : 0 < h) :
    curveMoment (wordAngle h sequentialWord) (4 * h) (8 * h) =
        circleMoment 0 (radiusB h) (radiusB h) 0 (6 * Real.pi) ∧
      curveArea (wordAngle h sequentialWord) (4 * h) (8 * h) =
        circleArea 0 (radiusB h) (radiusB h) 0 (6 * Real.pi) := by
  have hs := curve_integrals_circle_segment (wordAngle_continuous hh sequentialWord)
    (4 * h) (8 * h) 0 (curvatureB h) 0 (radiusB h) (radiusB h) (by linarith)
    (radiusB_curvatureB hh)
    (by intro u hu; simpa only [zero_add] using sequential_curve_second hh hu)
    (by intro u hu; rw [sequential_angle_second hh hu.1 hu.2];
        simp only [zero_add, Real.sin_add, Real.sin_two_pi, Real.cos_two_pi, zero_mul, one_mul])
    (by intro u hu; rw [sequential_angle_second hh hu.1 hu.2];
        simp only [zero_add, Real.cos_add, Real.sin_two_pi, Real.cos_two_pi, zero_mul, one_mul, sub_zero])
  have ha : curvatureB h * (8 * h - 4 * h) = 6 * Real.pi := by
    unfold curvatureB
    field_simp
    ring
  simpa only [zero_add, ha] using hs

theorem inserted_integrals_first {h : ℝ} (hh : 0 < h) :
    curveMoment (wordAngle h insertedWord) 0 (3 * h) =
        circleMoment 0 (3 * radiusB h) (3 * radiusB h) 0 (3 * Real.pi / 2) ∧
      curveArea (wordAngle h insertedWord) 0 (3 * h) =
        circleArea 0 (3 * radiusB h) (3 * radiusB h) 0 (3 * Real.pi / 2) := by
  have hs := curve_integrals_circle_segment (wordAngle_continuous hh insertedWord)
    0 (3 * h) 0 (curvatureA h) 0 (3 * radiusB h) (3 * radiusB h) (by positivity)
    (radiusA_curvatureA hh)
    (by intro u hu; simpa only [zero_add, sub_zero] using inserted_curve_first hh hu)
    (by intro u hu; rw [inserted_angle_first hh hu.2]; simp only [zero_add, sub_zero])
    (by intro u hu; rw [inserted_angle_first hh hu.2]; simp only [zero_add, sub_zero])
  have ha : curvatureA h * (3 * h) = 3 * Real.pi / 2 := by
    unfold curvatureA
    field_simp
  simpa only [zero_add, sub_zero, ha] using hs

theorem inserted_integrals_middle {h : ℝ} (hh : 0 < h) :
    curveMoment (wordAngle h insertedWord) (3 * h) (7 * h) =
        circleMoment (-2 * radiusB h) (3 * radiusB h) (radiusB h)
          (3 * Real.pi / 2) (3 * Real.pi / 2 + 6 * Real.pi) ∧
      curveArea (wordAngle h insertedWord) (3 * h) (7 * h) =
        circleArea (-2 * radiusB h) (3 * radiusB h) (radiusB h)
          (3 * Real.pi / 2) (3 * Real.pi / 2 + 6 * Real.pi) := by
  have hs := curve_integrals_circle_segment (wordAngle_continuous hh insertedWord)
    (3 * h) (7 * h) (3 * Real.pi / 2) (curvatureB h)
    (-2 * radiusB h) (3 * radiusB h) (radiusB h) (by linarith)
    (radiusB_curvatureB hh) (fun u hu => inserted_curve_middle hh hu)
    (by intro u hu; rw [inserted_angle_middle hh hu.1 hu.2])
    (by intro u hu; rw [inserted_angle_middle hh hu.1 hu.2])
  have ha : curvatureB h * (7 * h - 3 * h) = 6 * Real.pi := by
    unfold curvatureB
    field_simp
    ring
  simpa only [ha] using hs

theorem inserted_integrals_last {h : ℝ} (hh : 0 < h) :
    curveMoment (wordAngle h insertedWord) (7 * h) (8 * h) =
        circleMoment 0 (3 * radiusB h) (3 * radiusB h) (3 * Real.pi / 2) (2 * Real.pi) ∧
      curveArea (wordAngle h insertedWord) (7 * h) (8 * h) =
        circleArea 0 (3 * radiusB h) (3 * radiusB h) (3 * Real.pi / 2) (2 * Real.pi) := by
  have hphase (u : ℝ) :
      15 * Real.pi / 2 + curvatureA h * (u - 7 * h) =
        (3 * Real.pi / 2 + curvatureA h * (u - 7 * h)) + (3 : ℕ) * (2 * Real.pi) := by
    norm_num
    ring
  have hs := curve_integrals_circle_segment (wordAngle_continuous hh insertedWord)
    (7 * h) (8 * h) (3 * Real.pi / 2) (curvatureA h)
    0 (3 * radiusB h) (3 * radiusB h) (by linarith)
    (radiusA_curvatureA hh) (fun u hu => inserted_curve_last hh hu)
    (by intro u hu; rw [inserted_angle_last hh hu.1 hu.2, hphase, Real.sin_add_nat_mul_two_pi])
    (by intro u hu; rw [inserted_angle_last hh hu.1 hu.2, hphase, Real.cos_add_nat_mul_two_pi])
  have ha : 3 * Real.pi / 2 + curvatureA h * (8 * h - 7 * h) = 2 * Real.pi := by
    unfold curvatureA
    field_simp
    ring
  simpa only [ha] using hs

def wordMoment (h : ℝ) (w : List Bool) : ℝ :=
  curveMoment (wordAngle h w) 0 (wordLength h w)

theorem sequentialWord_length (h : ℝ) : wordLength h sequentialWord = 8 * h := by
  norm_num [wordLength, sequentialWord]

theorem insertedWord_length (h : ℝ) : wordLength h insertedWord = 8 * h := by
  norm_num [wordLength, insertedWord]

/-- The first word is one traversal of the large circle followed by three
traversals of the small circle. Both equalities concern the reconstructed curve. -/
theorem sequential_integrals {h : ℝ} (hh : 0 < h) :
    wordMoment h sequentialWord = sequentialLoopsMoment (radiusB h) ∧
      signedArea (wordAngle h sequentialWord) (wordLength h sequentialWord) =
        sequentialLoopsArea (radiusB h) := by
  constructor
  · rw [wordMoment, sequentialWord_length,
      ← curveMoment_add (wordAngle_continuous hh sequentialWord) 0 (4 * h) (8 * h),
      (sequential_integrals_first hh).1, (sequential_integrals_second hh).1]
    rfl
  · change curveArea (wordAngle h sequentialWord) 0 (wordLength h sequentialWord) = _
    rw [sequentialWord_length,
      ← curveArea_add (wordAngle_continuous hh sequentialWord) 0 (4 * h) (8 * h),
      (sequential_integrals_first hh).2, (sequential_integrals_second hh).2]
    rfl

/-- The second word inserts three small-circle traversals at the three-quarter
point of the large circle, then completes the large circle. -/
theorem inserted_integrals {h : ℝ} (hh : 0 < h) :
    wordMoment h insertedWord = insertedLoopsMoment (radiusB h) ∧
      signedArea (wordAngle h insertedWord) (wordLength h insertedWord) =
        insertedLoopsArea (radiusB h) := by
  constructor
  · rw [wordMoment, insertedWord_length,
      ← curveMoment_add (wordAngle_continuous hh insertedWord) 0 (7 * h) (8 * h),
      ← curveMoment_add (wordAngle_continuous hh insertedWord) 0 (3 * h) (7 * h),
      (inserted_integrals_first hh).1, (inserted_integrals_middle hh).1,
      (inserted_integrals_last hh).1]
    rfl
  · change curveArea (wordAngle h insertedWord) 0 (wordLength h insertedWord) = _
    rw [insertedWord_length,
      ← curveArea_add (wordAngle_continuous hh insertedWord) 0 (7 * h) (8 * h),
      ← curveArea_add (wordAngle_continuous hh insertedWord) 0 (3 * h) (7 * h),
      (inserted_integrals_first hh).2, (inserted_integrals_middle hh).2,
      (inserted_integrals_last hh).2]
    rfl

theorem actual_word_moment_difference {h : ℝ} (hh : 0 < h) :
    wordMoment h insertedWord - wordMoment h sequentialWord =
      -32 * h ^ 3 / (9 * Real.pi ^ 2) := by
  rw [(inserted_integrals hh).1, (sequential_integrals hh).1]
  exact insertion_moment_difference_h h

theorem actual_words_equal_area {h : ℝ} (hh : 0 < h) :
    signedArea (wordAngle h insertedWord) (wordLength h insertedWord) =
      signedArea (wordAngle h sequentialWord) (wordLength h sequentialWord) := by
  rw [(inserted_integrals hh).2, (sequential_integrals hh).2]
  exact insertion_preserves_area _

theorem actual_word_area_value {h : ℝ} (hh : 0 < h) :
    signedArea (wordAngle h insertedWord) (wordLength h insertedWord) =
      16 * h ^ 2 / (3 * Real.pi) := by
  rw [(inserted_integrals hh).2]
  exact loop_area_h h

theorem actual_words_distinct_moments {h : ℝ} (hh : 0 < h) :
    wordMoment h insertedWord ≠ wordMoment h sequentialWord := by
  rw [(inserted_integrals hh).1, (sequential_integrals hh).1]
  exact insertion_moments_distinct h hh

theorem actual_words_same_state {h : ℝ} (hh : 0 < h) :
    reconstructedState h insertedWord = reconstructedState h sequentialWord := by
  rw [reconstructedState_eq_integer_decode hh, reconstructedState_eq_integer_decode hh]
  have hw : LinearInputCurveWordFinite.state insertedWord =
      LinearInputCurveWordFinite.state sequentialWord := by decide
  rw [hw]

theorem sequential_state_value {h : ℝ} (hh : 0 < h) :
    reconstructedState h sequentialWord = (0, 8 * Real.pi, 5 * Real.pi ^ 2 / h) := by
  rw [reconstructedState_eq_integer_decode hh]
  have hw : LinearInputCurveWordFinite.state sequentialWord = ((0, 0), 16, 40, 32) := by decide
  rw [hw]
  apply LinearInputCurveWordAlgebra.state_ext
  · simp [LinearInputCurveWordRealization.decode, LinearInputCurveWordArc.interpretFirstState,
      LinearInputCurveWordAlgebra.endpoint]
    rfl
  · change (16 : ℝ) * (Real.pi / 2) = 8 * Real.pi
    ring
  · change (Real.pi ^ 2 / (8 * h)) * 40 = 5 * Real.pi ^ 2 / h
    ring

theorem inserted_state_value {h : ℝ} (hh : 0 < h) :
    reconstructedState h insertedWord = (0, 8 * Real.pi, 5 * Real.pi ^ 2 / h) := by
  rw [actual_words_same_state hh, sequential_state_value hh]

/-- The finite area collision is an actual pair of unit-speed curves with
continuous tangent, identical state and signed area, but distinct cubic moment. -/
theorem actual_curve_collision {h : ℝ} (hh : 0 < h) :
    reconstructedState h insertedWord = reconstructedState h sequentialWord ∧
      signedArea (wordAngle h insertedWord) (wordLength h insertedWord) =
        signedArea (wordAngle h sequentialWord) (wordLength h sequentialWord) ∧
      wordMoment h insertedWord ≠ wordMoment h sequentialWord :=
  ⟨actual_words_same_state hh, actual_words_equal_area hh, actual_words_distinct_moments hh⟩

end LinearInputCurveWordCircleWords
