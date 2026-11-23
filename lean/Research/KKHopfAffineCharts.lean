import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# The two affine Hopf/CP1 charts and overlap transition
On C2\{0}, use the chart z1!=0 with w_N=z2/z1 and the chart
z2!=0 with w_S=z1/z2. They cover C2\{0}, and on overlap
w_N*w_S=1. These are the algebraic chart gluing identities.
They do not themselves establish smooth-manifold quotient S3/U1=S2,
transition winding, or a principal circle bundle structure in Mathlib.
-/
namespace KKHopfAffineCharts

def north (z1 z2 : ℂ) : ℂ := z2/z1
def south (z1 z2 : ℂ) : ℂ := z1/z2

theorem overlap_inverse (z1 z2 : ℂ) (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) :
    north z1 z2 * south z1 z2 = 1 := by
  unfold north south
  field_simp [h1,h2]

theorem north_reconstruct (z1 z2 : ℂ) (h1 : z1 ≠ 0) :
    z1 * north z1 z2 = z2 := by
  unfold north
  field_simp [h1]

theorem south_reconstruct (z1 z2 : ℂ) (h2 : z2 ≠ 0) :
    z2 * south z1 z2 = z1 := by
  unfold south
  field_simp [h2]

theorem north_invariant_under_scaling (z1 z2 lam : ℂ)
    (hz : z1 ≠ 0) (hl : lam ≠ 0) :
    north (lam*z1) (lam*z2) = north z1 z2 := by
  unfold north
  field_simp [hz,hl]
  ring

theorem south_invariant_under_scaling (z1 z2 lam : ℂ)
    (hz : z2 ≠ 0) (hl : lam ≠ 0) :
    south (lam*z1) (lam*z2) = south z1 z2 := by
  unfold south
  field_simp [hz,hl]
  ring

end KKHopfAffineCharts
