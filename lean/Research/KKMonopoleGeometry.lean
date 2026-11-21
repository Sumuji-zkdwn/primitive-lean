import Mathlib.Tactic

/-!
# Kaluza-Klein monopole: algebraic identities of the vacuum 5D ansatz

The Gibbons-Hawking spatial metric has H(r)=1+k/r and connection
A=k*cos(theta)dphi, with extra circle coordinate psi.
Lean proves radial flux/gauge-patch arithmetic only. Full 5D
Ricci-flatness is checked independently by tools/check_kk_monopole.py.
-/
namespace KKMonopoleGeometry

def harmonicH (k r : ℚ) : ℚ := 1 + k / r
def radialDerivative (k r : ℚ) : ℚ := -k / r ^ 2
def sphericalFlux (k r : ℚ) : ℚ := r ^ 2 * radialDerivative k r

theorem constant_flux (k r : ℚ) (hr : r ≠ 0) :
    sphericalFlux k r = -k := by
  dsimp [sphericalFlux, radialDerivative]
  field_simp [hr]

theorem H_positive (k r : ℚ) (hk : 0 ≤ k) (hr : 0 < r) :
    0 < harmonicH k r := by
  unfold harmonicH
  have hd : 0 ≤ k / r := div_nonneg hk (le_of_lt hr)
  linarith

/-- θφ-component of dA, with sigma denoting sin(theta). -/
def connectionCurvature (k sigma : ℚ) : ℚ := -k * sigma

theorem field_flux_match (k r sigma : ℚ) (hr : r ≠ 0) :
    connectionCurvature k sigma = sphericalFlux k r * sigma := by
  rw [constant_flux k r hr]
  rfl

def northPatch (k c : ℚ) : ℚ := k * (c - 1)
def southPatch (k c : ℚ) : ℚ := k * (c + 1)

theorem patch_difference (k c : ℚ) :
    southPatch k c - northPatch k c = 2 * k := by
  unfold southPatch northPatch
  ring

/-- One azimuthal loop changes psi by a full 4pi*k fibre period. -/
theorem fibre_period_winding (k : ℚ) :
    (2 * k) * 2 = 4 * k := by ring

/-- For chi=psi/(2k) with period 2pi, the normalized flux is -1. -/
theorem normalized_first_chern : (-2 : ℚ) / 2 = -1 := by norm_num

theorem nontrivial_flux (k : ℚ) (hk : k ≠ 0) :
    connectionCurvature k 1 ≠ 0 := by
  simpa [connectionCurvature] using neg_ne_zero.mpr hk

theorem reverse_orientation (k sigma : ℚ) :
    connectionCurvature (-k) sigma = -connectionCurvature k sigma := by
  unfold connectionCurvature
  ring

end KKMonopoleGeometry
