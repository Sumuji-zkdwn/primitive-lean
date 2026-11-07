import PADFourLayerFourthMean

/-!
# Exact fixed-calibration noise margin from two interior probes

The result is an exact minimax separation at alpha ratio 4/3, known mass 1
and known mean 3/2. No real/experimental PAD noise law is claimed.
The original PR #101, #103, #106, and #109 sources are unchanged.
-/
namespace PADFourLayerUniformMargin
open PADFourLayer

/-- Every profile with mass 1 and mean 3/2 has this parametrization
in coordinates a=p2, b=p3. -/
def param (a b : ℚ) : Profile :=
  ⟨-(1/2)+a+2*b, (3/2)-2*a-3*b, a, b⟩

def crossGap (t a b c d : ℚ) : ℚ :=
  response (t^3) (param a b) - response (t^4) (param c d)

/-- The two probe coordinates are t=1/2 and t=9/10; nominal u=t^3. -/
def lam : ℚ := 1812744140625/2126873677106
def mu : ℚ := 314129536481/2126873677106
def margin : ℚ := 2823749272953/68059957667392
def coefP1 : ℚ := 859005471493/34029978833696
def coefP3 : ℚ := 1702471931945/272239830669568
def coefQ2 : ℚ := 987235535475/34029978833696

theorem param_mass (a b : ℚ) : mass (param a b) = 1 := by
  unfold mass param
  ring

theorem param_mean (a b : ℚ) : mean (param a b) = 3/2 := by
  unfold mean param
  ring

theorem positive_weights_and_margin :
    0 < lam ∧ 0 < mu ∧ lam+mu=1 ∧
    0 < margin ∧ 0 < coefP1 ∧ 0 < coefP3 ∧ 0 < coefQ2 := by
  norm_num [lam, mu, margin, coefP1, coefP3, coefQ2]

/-- Exact LP dual identity. The right-hand surplus is nonnegative whenever
p1 = 3/2-2a-3b >=0, p3=b>=0, q2=c>=0. -/
theorem weighted_gap_identity (a b c d : ℚ) :
    lam*crossGap (9/10) a b c d - mu*crossGap (1/2) a b c d =
      margin + coefP1*((3/2)-2*a-3*b) + coefP3*b + coefQ2*c := by
  norm_num [lam, mu, margin, coefP1, coefP3, coefQ2,
    crossGap, response, param]
  ring

/-- Uniform minimax lower bound. For any nonnegative-profile parameters
with the same exact mass and mean, one of two nominal internal readouts
has a signed response discrepancy of at least margin ~= 0.0414891. -/
theorem two_probe_uniform_separation (a b c d : ℚ)
    (hp1 : 0 ≤ (3/2 : ℚ)-2*a-3*b) (hp3 : 0 ≤ b)
    (hq2 : 0 ≤ c) :
    margin ≤ crossGap (9/10) a b c d ∨
      crossGap (1/2) a b c d ≤ -margin := by
  have hweight := positive_weights_and_margin
  obtain ⟨hl, hm, hsum, hd, hc1, hc3, hcq⟩ := hweight
  have hid := weighted_gap_identity a b c d
  have hprod1 : 0 ≤ coefP1*((3/2 : ℚ)-2*a-3*b) :=
    mul_nonneg (le_of_lt hc1) hp1
  have hprod3 : 0 ≤ coefP3*b := mul_nonneg (le_of_lt hc3) hp3
  have hprodq : 0 ≤ coefQ2*c := mul_nonneg (le_of_lt hcq) hq2
  have hlower : margin ≤
      lam*crossGap (9/10) a b c d - mu*crossGap (1/2) a b c d := by
    linarith
  by_contra h
  push Not at h
  have hx : 0 < lam*(margin-crossGap (9/10) a b c d) :=
    mul_pos hl (sub_pos.mpr h.1)
  have hy : 0 < mu*(margin+crossGap (1/2) a b c d) :=
    mul_pos hm (by linarith [h.2])
  nlinarith

/-- The lower bound is attained on the closed nonnegative simplex. -/
def sharpP : Profile := param (3/4) 0
def sharpQ : Profile := param 0 (416199750000/1063436838553)

theorem sharp_profiles_nonnegative :
    0 ≤ sharpP.p0 ∧ 0 ≤ sharpP.p1 ∧
    0 ≤ sharpP.p2 ∧ 0 ≤ sharpP.p3 ∧
    0 ≤ sharpQ.p0 ∧ 0 ≤ sharpQ.p1 ∧
    0 ≤ sharpQ.p2 ∧ 0 ≤ sharpQ.p3 := by
  norm_num [sharpP, sharpQ, param]

theorem sharp_two_responses :
    crossGap (1/2) (3/4) 0 0 (416199750000/1063436838553) = -margin ∧
    crossGap (9/10) (3/4) 0 0 (416199750000/1063436838553) = margin := by
  norm_num [crossGap, response, param, margin]

end PADFourLayerUniformMargin
