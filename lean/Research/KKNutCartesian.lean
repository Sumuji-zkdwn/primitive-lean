import Mathlib.Tactic

/-!
# Taub--NUT centre: smooth Cartesian rational coefficient certificates

Let k>0, c>=0, rho^2 = |X|², alpha=c/(4*k²), q=1+alpha*rho².
Under the Hopf map with fibre angle chi=psi/k of period 4*pi,

g_TN = q delta - [alpha*(2+alpha*rho²)/q] omega⊗omega,

where omega=X0*dX1-X1*dX0+X2*dX3-X3*dX2 on R4. This is a
smooth Cartesian expression across X=0 for alpha>=0. Lean here
certifies the *scalar rational identities and positivity condition*
needed for the rank-one metric. It does NOT prove the Hopf manifold
atlas or that all metric components are C^infinity on R4.
-/

namespace KKNutCartesian


def q (alpha s : ℝ) : ℝ := 1+alpha*s

noncomputable def beta (alpha s : ℝ) : ℝ := -(alpha*(2+alpha*s))/q alpha s

/-- Rank-one metric eigenvalue along omega (where omega·omega=s).
The other three eigenvalues are q. -/
theorem fibre_eigenvalue (alpha s : ℝ) (hq : q alpha s ≠ 0) :
    q alpha s + beta alpha s * s = (q alpha s)⁻¹ := by
  dsimp [beta, q] at *
  field_simp [hq]
  ring

/-- Determinant from the rank-one matrix determinant lemma:
q^3 * (q+beta*s)=q². -/
theorem determinant_certificate (alpha s : ℝ) (hq : q alpha s ≠ 0) :
    (q alpha s)^3*(q alpha s + beta alpha s*s) = (q alpha s)^2 := by
  rw [fibre_eigenvalue alpha s hq]
  field_simp

/-- In the centre X=0, the metric is exactly Euclidean. -/
theorem centre_coefficients (alpha : ℝ) :
    q alpha 0 = 1 ∧ beta alpha 0 = -2*alpha := by
  simp [q,beta]
  ring

/-- The centre extending coefficient beta has no pole at rho=0. -/
theorem beta_centre_regular (alpha s : ℝ) (hq : q alpha s ≠ 0) :
    beta alpha s = -2*alpha + alpha^2*s*(1/q alpha s) := by
  dsimp [beta, q] at *
  field_simp [hq]
  ring

/-- For alpha>=0 and s>=0, both rank-one eigenvalues are positive. -/
theorem eigenvalues_positive (alpha s : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    0 < q alpha s ∧ 0 < (q alpha s)⁻¹ := by
  have hprod : 0 ≤ alpha*s := mul_nonneg ha hs
  have hq : 0 < q alpha s := by
    dsimp [q]
    linarith
  exact ⟨hq, inv_pos.mpr hq⟩

/-- Algebraic lower bound for a quadratic form with the norm
constraint omega(v)^2 <= s*|v|^2 (Cauchy-Schwarz). -/
theorem quadratic_lower_bound
    (alpha s v t : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hcs : t^2 ≤ s*v) :
    v / (q alpha s) ≤ q alpha s*v + beta alpha s*t^2 := by
  have hq : 0 < q alpha s := (eigenvalues_positive alpha s ha hs).1
  have hneg : beta alpha s ≤ 0 := by
    unfold beta
    have h2 : 0 ≤ 2+alpha*s := by
      have := mul_nonneg ha hs
      linarith
    have hnum : 0 ≤ alpha*(2+alpha*s) := mul_nonneg ha h2
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum) (le_of_lt hq)
  have hmul : beta alpha s * (s*v) ≤ beta alpha s * (t^2) :=
    mul_le_mul_of_nonpos_left hcs hneg
  have heq : q alpha s*v + beta alpha s*(s*v) = v/(q alpha s) := by
    have heigen := fibre_eigenvalue alpha s (ne_of_gt hq)
    calc
      q alpha s*v + beta alpha s*(s*v) = (q alpha s+beta alpha s*s)*v := by ring
      _ = (q alpha s)⁻¹*v := by rw [heigen]
      _ = v/(q alpha s) := by ring
  linarith

end KKNutCartesian
