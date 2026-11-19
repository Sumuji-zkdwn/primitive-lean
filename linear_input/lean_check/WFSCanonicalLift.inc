/-!
A WFS coordinate on intensity alone changes the apparent linear structure.
Its cotangent lift changes the conjugate momentum as well.

For p=2: z=(r^2-1)/2 and xi=u/r, with r>0.
For p=0: z=log r and xi=r*u, with r>0.

The identities below are the algebraic/differential one-form preservation
under these explicit positive-intensity hypotheses. They do not say that a
Fenchel conjugate with a *fixed* transformed xi is unchanged, because xi
depends on the primal coordinate at fixed original u.
-/

noncomputable section

namespace LinearInputWFSCanonical

open LinearInputEWFSDual

/-- Cotangent lift of the p=2 WFS gauge on a positive intensity. -/
def lift2 (r : Positive) (u : ℝ) : ℝ × ℝ :=
  (wfs2 r.val, u / r.val)

/-- Direct WFS gauge relation, valid on the whole real line algebraically. -/
theorem wfs2_coordinate_identity (r : ℝ) :
    2 * wfs2 r + 1 = r ^ 2 := by
  dsimp [wfs2]
  ring

/-- Original polynomial E coupling ur in the new coordinate/momentum pair. -/
theorem wfs2_physical_coupling (r : Positive) (u : ℝ) :
    u * r.val = (u / r.val) * (2 * wfs2 r.val + 1) := by
  have hr : r.val ≠ 0 := ne_of_gt r.property
  rw [wfs2_coordinate_identity]
  field_simp [hr]

/-- WFS G_2 has differential dz = r dr. -/
theorem wfs2_derivative (r : ℝ) :
    deriv wfs2 r = r := by
  have hd : HasDerivAt wfs2 r r := by
    convert (((hasDerivAt_id r).pow 2).sub_const 1).div_const 2 using 1
    · rfl
    · simp
  exact hd.deriv

/-- The *complete* lift satisfies xi dz = u dr (in differential coefficients). -/
theorem wfs2_oneform (r : Positive) (u : ℝ) :
    (lift2 r u).2 * deriv wfs2 r.val = u := by
  rw [wfs2_derivative]
  dsimp [lift2]
  have hr : r.val ≠ 0 := ne_of_gt r.property
  field_simp [hr]

/-- The determinant of the cotangent lift's triangular Jacobian is 1.
Here ∂z/∂r=r and ∂xi/∂u=1/r; the off-diagonal term is killed by ∂z/∂u=0. -/
theorem wfs2_lift_jacobian_algebraic (r : Positive) (u : ℝ) :
    r.val * (1 / r.val) - (0 : ℝ) * (-(u / r.val ^ 2)) = 1 := by
  have hr : r.val ≠ 0 := ne_of_gt r.property
  field_simp [hr]; ring

/-- For Fechner p=0, dz = dr/r, and momentum must become xi=r*u. -/
def logMomentum (r : Positive) (u : ℝ) : ℝ := r.val * u

theorem log_oneform_coefficient (r : Positive) (u : ℝ) :
    logMomentum r u * (1 / r.val) = u := by
  have hr : r.val ≠ 0 := ne_of_gt r.property
  dsimp [logMomentum]
  field_simp [hr]

/-- A naive dual term xi*z cannot replace the original ur coupling. -/
theorem naive_wfs_pairing_not_physical :
    (1 : ℝ) * 1 ≠ (1 / 1 : ℝ) * wfs2 1 := by
  norm_num [wfs2]

/-- The p=2 WFS gauge is genuinely nonlinear, unlike the affine p=1 gauge. -/
theorem wfs2_not_affine :
    ¬ ∃ a b : ℝ, ∀ r : ℝ, wfs2 r = a * r + b := by
  rintro ⟨a, b, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [wfs2] at h0 h1 h2
  linarith

end LinearInputWFSCanonical
