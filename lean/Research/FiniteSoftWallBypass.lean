import Mathlib.Tactic

/-!
# Soft finite-energy walls do not isolate the S³ winding sectors

These 15 small certificates support the *independent* exact SymPy calculation
for the five-vertex model on ∂Δ⁴. They do not formalize degree, geometric
interpolation, a connected configuration space, the full five-site energy, or
a physical Einstein field. The coordinate/barycentric identities are merely
the rational witnesses used by the Python oracle.
-/

namespace FiniteSoftWallBypass

/-- The selected radical r=sqrt(21/26) is less than nine tenths. -/
theorem radical_lt_nine_tenths (r : ℝ)
    (hr : r ^ 2 = (21 : ℝ) / 26) (hn : 0 ≤ r) :
    r < (9 : ℝ) / 10 := by
  have hs : r ^ 2 < ((9 : ℝ) / 10) ^ 2 := by
    rw [hr]
    norm_num
  nlinarith

/-- The coordinate separating the staged route from its targeted zero. -/
theorem route_margin_gt_tenth (r : ℝ)
    (hr : r ^ 2 = (21 : ℝ) / 26) (hn : 0 ≤ r) :
    (1 : ℝ) / 10 < 1 - r := by
  have hb := radical_lt_nine_tenths r hr hn
  linarith

/-- Exact positive squared margin for the bypass route. -/
theorem route_margin_sq_gt_hundredth (r : ℝ)
    (hr : r ^ 2 = (21 : ℝ) / 26) (hn : 0 ≤ r) :
    (1 : ℝ) / 100 < (1 - r) ^ 2 := by
  have hb := route_margin_gt_tenth r hr hn
  nlinarith

/-- The smooth rational wall penalty is below 50 with margin d>1/100. -/
theorem soft_penalty_lt_fifty (d : ℝ) (hd : (1 : ℝ) / 100 < d) :
    (1 : ℝ) / ((1 : ℝ) / 100 + d) < 50 := by
  have hpos : (0 : ℝ) < (1 : ℝ) / 100 + d := by linarith
  apply (div_lt_iff₀ hpos).2
  nlinarith

/-- At all configurations the selected rational potential is at most 100. -/
theorem soft_penalty_le_hundred (d : ℝ) (hd : 0 ≤ d) :
    (1 : ℝ) / ((1 : ℝ) / 100 + d) ≤ 100 := by
  have hpos : (0 : ℝ) < (1 : ℝ) / 100 + d := by linarith
  apply (div_le_iff₀ hpos).2
  nlinarith

/-- K5 energy E₂≤20 and a route margin d>1/100 imply E<70. -/
theorem bypass_energy_lt_seventy (e d : ℝ)
    (he : e ≤ 20) (hd : (1 : ℝ) / 100 < d) :
    e + (1 : ℝ) / ((1 : ℝ) / 100 + d) < 70 := by
  have hp := soft_penalty_lt_fifty d hd
  linarith

/-- The direct path passes through a zero: V=100 exactly. -/
theorem direct_wall_energy_ge_hundred (e : ℝ) (he : 0 ≤ e) :
    100 ≤ e + (1 : ℝ) / ((1 : ℝ) / 100 + 0) := by
  norm_num
  linarith

/-- The bypass upper bound is strictly smaller than the direct wall value. -/
theorem bypass_below_direct (b w : ℝ)
    (hb : b < 70) (hw : 100 ≤ w) : b < w := by
  linarith

/-- Initial “soft-zero” vector norm square, coordinatewise expansion. -/
theorem initial_soft_norm_identity (r : ℝ) :
    r ^ 2 + 3 * (1 - r) ^ 2 = 3 - 6 * r + 4 * r ^ 2 := by
  ring

/-- Every real radical choice gives an initial separation ≥3/4. -/
theorem initial_soft_norm_lower (r : ℝ) :
    (3 : ℝ) / 4 ≤ 3 - 6 * r + 4 * r ^ 2 := by
  nlinarith [sq_nonneg (r - (3 : ℝ) / 4)]

/-- Positive barycentric weights (2,1,1,2)/6 on the bypass wall. -/
theorem bypass_wall_weights_sum :
    (2 : ℝ) / 6 + 1 / 6 + 1 / 6 + 2 / 6 = 1 := by
  norm_num

/-- First two coordinates of the unnormalized bypass facet zero. -/
theorem bypass_wall_coordinate_01 :
    (2 : ℝ) * (1 / 2) + 2 * (-1 / 2) = 0 := by
  norm_num

/-- Last two coordinates of the unnormalized bypass facet zero. -/
theorem bypass_wall_coordinate_23 :
    (1 : ℝ) + 2 * (-1 / 2) = 0 := by
  norm_num

/-- First coordinate of the direct path's face zero at t=1/6. -/
theorem direct_wall_coordinate_0 :
    (3 : ℝ) * (1 / 6) + 2 * (-1 / 4) = 0 := by
  norm_num

/-- Remaining coordinates of the direct path's face zero at t=1/6. -/
theorem direct_wall_coordinate_123 :
    (5 : ℝ) / 6 + 2 * (-5 / 12) = 0 := by
  norm_num

end FiniteSoftWallBypass
