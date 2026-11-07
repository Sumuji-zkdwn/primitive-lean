import PADFourLayerThreeProbe

/-!
# Fourth-probe follow-up: exact rational discrimination, no global claim

Additive sidecar to PR #103 on top of PR #101. Existing proof files are unchanged.
All formal statements concern rational polynomial responses, not real-power
calibration, measurement noise, or actual PAD/eKE experiments.
-/

namespace PADFourLayerFourProbe

open PADFourLayer PADFourLayerThreeProbe

/-- Positive remainder for the fixed PR #103 witness pair. -/
def remainder (t : ℚ) : ℚ :=
  41616*t^8 + 86700*t^7 + 119935*t^6 + 128090*t^5 +
  138186*t^4 + 147450*t^3 + 84370*t^2 + 12980*t + 1298

theorem remainder_positive (t : ℚ) (ht : 0 ≤ t) : 0 < remainder t := by
  unfold remainder
  positivity

/-- Exact polynomial identity comparing s_A=t^3 and s_B=t^4.
Only the specific tripleP, tripleQ from PR #103 are asserted. -/
theorem exact_gap_factor (t : ℚ) :
    response (t^3) tripleP - response (t^4) tripleQ =
      -((t-1)*(2*t-1)*(3*t-1)*(4*t-1)*remainder t) / 3042500 := by
  dsimp [response, tripleP, tripleQ, remainder]
  ring

/-- At t=4/5, nominal u=t^3=64/125; other calibration uses t^4=256/625. -/
theorem fourth_exact_gap :
    response (64/125) tripleP - response (256/625) tripleQ =
      13370535881703/371398925781250 := by
  norm_num [response, tripleP, tripleQ]

theorem fourth_exact_gap_positive :
    0 < response (64/125) tripleP - response (256/625) tripleQ := by
  rw [fourth_exact_gap]
  norm_num

theorem fourth_separates_fixed_pair :
    response (64/125) tripleP ≠ response (256/625) tripleQ := by
  intro h
  have z : response (64/125) tripleP - response (256/625) tripleQ = 0 :=
    sub_eq_zero.mpr h
  rw [fourth_exact_gap] at z
  norm_num at z

/-- Every positive rational fourth cube-root coordinate other than the
existing three probes (and t=1) separates this fixed pair.
NOT a universal four-probe injectivity theorem. -/
theorem fixed_pair_separated_off_roots
    (t : ℚ) (ht : 0 < t) (ht1 : t < 1)
    (h4 : t ≠ 1/4) (h3 : t ≠ 1/3) (h2 : t ≠ 1/2) :
    response (t^3) tripleP ≠ response (t^4) tripleQ := by
  have hOne : t - 1 ≠ 0 := by linarith
  have hTwo : 2*t - 1 ≠ 0 := by
    intro h
    apply h2
    linarith
  have hThree : 3*t - 1 ≠ 0 := by
    intro h
    apply h3
    linarith
  have hFour : 4*t - 1 ≠ 0 := by
    intro h
    apply h4
    linarith
  have hR : remainder t ≠ 0 := ne_of_gt (remainder_positive t (le_of_lt ht))
  have hProd : (t-1)*(2*t-1)*(3*t-1)*(4*t-1)*remainder t ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hOne hTwo)
      hThree) hFour) hR
  have hDiff : -((t-1)*(2*t-1)*(3*t-1)*(4*t-1)*remainder t) /
      (3042500 : ℚ) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hProd) (by norm_num)
  intro h
  have hz : response (t^3) tripleP - response (t^4) tripleQ = 0 :=
    sub_eq_zero.mpr h
  rw [exact_gap_factor] at hz
  exact hDiff hz

/-- u=1 is uninformative: the two distinct profiles have equal mass. -/
theorem fourth_unit_probe_ambiguous :
    response 1 tripleP = response 1 tripleQ := by
  norm_num [response, tripleP, tripleQ]

end PADFourLayerFourProbe
