import Mathlib.Tactic

/-!
# North/South Dirac fibre-chart transition for the single Taub--NUT centre

On the overlapping spherical charts, the local 1-form potentials are
 A_N=k(cos(theta)-1)dphi, A_S=k(cos(theta)+1)dphi.
The fibre coordinates must obey psi_S = psi_N - 2k phi so that
 dpsi_S+A_S = dpsi_N+A_N. The transition changes psi by exactly
 4*pi*k upon one complete azimuthal rotation, hence the prescribed
 fibre period is necessary for the Hopf S3 bundle.

The statements are coordinate algebra; smooth chart gluing remains
an external manifold/theorem obligation.
-/
namespace KKNutPatching

def northA (k c : ℝ) : ℝ := k*(c-1)
def southA (k c : ℝ) : ℝ := k*(c+1)
def southFibre (k psi phi : ℝ) : ℝ := psi - 2*k*phi

/-- The Dirac North/South magnetic gauge potentials differ by 2k dphi. -/
theorem potential_difference (k c : ℝ) :
    southA k c - northA k c = 2*k := by
  unfold southA northA
  ring

/-- The coordinate shift exactly preserves the 5D fibre one-form. -/
theorem fibre_form_overlap (k c dpsi dphi : ℝ) :
    (dpsi - 2*k*dphi) + southA k c*dphi =
      dpsi + northA k c*dphi := by
  unfold southA northA
  ring

/-- Azimuth phi~phi+2*pi shifts the local fibre coordinate by
one full period 4*pi*k, hence the transition is single-valued on
the correctly normalized circle. -/
theorem period_matching (k psi phi : ℝ) :
    southFibre k psi (phi + 2*Real.pi) =
      southFibre k psi phi - 4*Real.pi*k := by
  unfold southFibre
  ring

end KKNutPatching