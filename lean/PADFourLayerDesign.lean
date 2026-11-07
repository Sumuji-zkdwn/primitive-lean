import Mathlib

/-!
# Four-layer PAD design: exact D-optimality certificate

This additive theorem file does not change `PADFourLayer.lean`.
It concerns only an abstract cubic observation matrix, not calibrated PAD data.
-/

namespace PADFourLayerDesign

/-- The determinant of the four-layer observation matrix when t ≤ s. -/
def detEnvelope (t s : ℚ) : ℚ :=
  (s - t) * (1 - t)^2 * (1 - s)^2

/-- Exact algebraic gap between the fixed-first-probe envelope
    and its maximum at s=(1+2e)/3. -/
theorem fixedFirstGap (e s : ℚ) :
    (4:ℚ)*(1-e)^3/27 - (s-e)*(1-s)^2 =
      (1+2*e-3*s)^2*(4-e-3*s)/27 := by
  ring

/-- A global upper bound for the determinant when both probes lie in [e,1]. -/
theorem detEnvelope_upper (e t s : ℚ)
    (he : 0 ≤ e) (het : e ≤ t) (hts : t ≤ s) (hs : s ≤ 1) :
    detEnvelope t s ≤ 4*(1-e)^5/27 := by
  have ht_le : t ≤ 1 := le_trans hts hs
  have he_le : e ≤ 1 := le_trans (le_trans het hts) hs
  have hdiff : 0 ≤ s-t := sub_nonneg.mpr hts
  have htdiff : 0 ≤ t-e := sub_nonneg.mpr het
  have htop : 0 ≤ 2-t-e := by linarith
  have hfactor : 0 ≤ (t-e)*(2-t-e) := mul_nonneg htdiff htop
  have hsquare : (1-t)^2 ≤ (1-e)^2 := by nlinarith
  have hfirst : (s-t)*(1-t)^2 ≤ (s-e)*(1-e)^2 := by
    calc
      (s-t)*(1-t)^2 ≤ (s-t)*(1-e)^2 :=
        mul_le_mul_of_nonneg_left hsquare hdiff
      _ ≤ (s-e)*(1-e)^2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg (1-e))
  have hgapNonneg : 0 ≤ (1+2*e-3*s)^2*(4-e-3*s) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hfixed : (s-e)*(1-s)^2 ≤ 4*(1-e)^3/27 := by
    have hidentity := fixedFirstGap e s
    nlinarith [hgapNonneg, hidentity]
  calc
    detEnvelope t s ≤ (s-e)*(1-e)^2*(1-s)^2 := by
      unfold detEnvelope
      exact mul_le_mul_of_nonneg_right hfirst (sq_nonneg (1-s))
    _ = (1-e)^2*((s-e)*(1-s)^2) := by ring
    _ ≤ (1-e)^2*(4*(1-e)^3/27) :=
        mul_le_mul_of_nonneg_left hfixed (sq_nonneg (1-e))
    _ = 4*(1-e)^5/27 := by ring

/-- The bound is attained at the first permitted point and the
    second point one-third of the way from e to 1. -/
theorem detEnvelope_at_optimal (e : ℚ) :
    detEnvelope e ((1+2*e)/3) = 4*(1-e)^5/27 := by
  unfold detEnvelope
  ring

theorem unitInterval_upper (t s : ℚ)
    (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ 1) :
    detEnvelope t s ≤ 4/27 := by
  have h := detEnvelope_upper 0 t s (by norm_num) ht hts hs
  norm_num at h ⊢
  exact h

theorem unitInterval_at_optimal :
    detEnvelope 0 (1/3) = 4/27 := by
  norm_num [detEnvelope]

end PADFourLayerDesign
