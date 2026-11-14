import Elastica.Geometry
import Elastica.Equations

/-!
The pressure angle equation on an actually reconstructed arclength curve
implies the forced curvature equation. Both its first integral and its second
derivative are proved, rather than supplied as independent jet assumptions.
-/

noncomputable section
namespace LinearInputPressureCurvature

open Real Set Filter Elastica LinearInputDesign LinearInputGradient
open scoped Topology

/-- The force components are `(lam - p Y, mu + p X)`. Their tangent projection
has a quadratic-curvature first integral, derived from the angle equation. -/
theorem pressure_firstIntegral_hasDerivAt
    {θ : ℝ → ℝ} {k p lam μ s : ℝ}
    (hθ : ContDiff ℝ 3 θ)
    (hAngle : HasDerivAt (fun t => k * deriv θ t)
      (p * (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) -
        lam * sin (θ s) + μ * cos (θ s)) s) :
    HasDerivAt (fun t => k * (deriv θ t) ^ 2 / 2 -
      (lam - p * yCoord θ 0 t) * cos (θ t) -
      (μ + p * xCoord θ 0 t) * sin (θ t)) 0 s := by
  have ht := (hθ.differentiable (by norm_num) s).hasDerivAt
  have hκ := ((hθ.deriv' (n := 2)).differentiable (by norm_num) s).hasDerivAt
  have hX := hasDerivAt_xCoord hθ.continuous 0 s
  have hY := hasDerivAt_yCoord hθ.continuous 0 s
  have hmoment := (hκ.const_mul k).unique hAngle
  convert (((hκ.pow 2).const_mul k).div_const 2).sub
    (((hasDerivAt_const s lam).sub (hY.const_mul p)).mul ht.cos) |>.sub
      (((hasDerivAt_const s μ).add (hX.const_mul p)).mul ht.sin) using 1
  norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat, Pi.sub_apply, Pi.add_apply]
  nlinarith [congrArg (fun q : ℝ => q * deriv θ s) hmoment]

/-- The pressure contribution to the differentiated moment equation is exactly
`p`, using unit arclength speed. The other term is the tangential force. -/
theorem pressure_angleForce_hasDerivAt
    {θ : ℝ → ℝ} {p lam μ s : ℝ} (hθ : ContDiff ℝ 3 θ) :
    HasDerivAt (fun t =>
      p * (xCoord θ 0 t * cos (θ t) + yCoord θ 0 t * sin (θ t)) -
        lam * sin (θ t) + μ * cos (θ t))
      (p - ((lam - p * yCoord θ 0 s) * cos (θ s) +
        (μ + p * xCoord θ 0 s) * sin (θ s)) * deriv θ s) s := by
  have ht := (hθ.differentiable (by norm_num) s).hasDerivAt
  have hX := hasDerivAt_xCoord hθ.continuous 0 s
  have hY := hasDerivAt_yCoord hθ.continuous 0 s
  convert ((((hX.mul ht.cos).add (hY.mul ht.sin)).const_mul p).sub
    (ht.sin.const_mul lam)).add (ht.cos.const_mul μ) using 1
  nlinarith [congrArg (fun q : ℝ => p * q) (sin_sq_add_cos_sq (θ s))]

/-- The same constant in the force first integral yields the forced curvature
equation. The second derivative is obtained from the actual angle equation. -/
theorem pressure_angle_firstIntegral_curvature
    {θ : ℝ → ℝ} {ℓ k p lam μ : ℝ} (hθ : ContDiff ℝ 3 θ)
    (hAngle : ∀ s ∈ Ioo 0 ℓ, HasDerivAt (fun t => k * deriv θ t)
      (p * (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) -
        lam * sin (θ s) + μ * cos (θ s)) s) :
    ∃ σ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      (k * (deriv θ s) ^ 2 / 2 -
        (lam - p * yCoord θ 0 s) * cos (θ s) -
        (μ + p * xCoord θ 0 s) * sin (θ s) = σ) ∧
      (k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
        σ * deriv θ s = p) := by
  have hfirst : ∃ σ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      k * (deriv θ s) ^ 2 / 2 -
        (lam - p * yCoord θ 0 s) * cos (θ s) -
        (μ + p * xCoord θ 0 s) * sin (θ s) = σ := by
    apply isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo 0 ℓ).isPreconnected
    · intro s hs
      exact (pressure_firstIntegral_hasDerivAt hθ (hAngle s hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      exact (pressure_firstIntegral_hasDerivAt hθ (hAngle s hs)).deriv
  obtain ⟨σ, hσ⟩ := hfirst
  refine ⟨σ, fun s hs => ⟨hσ s hs, ?_⟩⟩
  have hκ : ContDiff ℝ 2 (deriv θ) := hθ.deriv' (n := 2)
  have heq : deriv (fun t => k * deriv θ t) =ᶠ[𝓝 s]
      (fun t => p * (xCoord θ 0 t * cos (θ t) + yCoord θ 0 t * sin (θ t)) -
        lam * sin (θ t) + μ * cos (θ t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact (hAngle t ht).deriv
  have hsecond := ((pressure_angleForce_hasDerivAt (p := p) (lam := lam)
    (μ := μ) (s := s) hθ).congr_of_eventuallyEq heq).deriv
  have hfun : deriv (fun t => k * deriv θ t) =
      (fun t => k * deriv (deriv θ) t) := by
    funext t
    exact ((hκ.differentiable (by norm_num) t).hasDerivAt.const_mul k).deriv
  rw [hfun, ((hκ.differentiable_deriv_two s).hasDerivAt.const_mul k).deriv] at hsecond
  nlinarith [congrArg (fun q : ℝ => q * deriv θ s) (hσ s hs)]

/-- Projection to the curvature equation, with pressure as its explicit forcing. -/
theorem pressure_angle_curvature
    {θ : ℝ → ℝ} {ℓ k p lam μ : ℝ} (hθ : ContDiff ℝ 3 θ)
    (hAngle : ∀ s ∈ Ioo 0 ℓ, HasDerivAt (fun t => k * deriv θ t)
      (p * (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) -
        lam * sin (θ s) + μ * cos (θ s)) s) :
    ∃ σ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
        σ * deriv θ s = p := by
  obtain ⟨σ, hσ⟩ := pressure_angle_firstIntegral_curvature hθ hAngle
  exact ⟨σ, fun s hs => (hσ s hs).2⟩

/-- Pressure determines the phase input `u = p / k`, which may be nonzero. These are actual
coordinate derivatives and a constant energy along arclength. -/
theorem pressure_angle_phase_energy
    {θ : ℝ → ℝ} {ℓ k p lam μ : ℝ} (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hAngle : ∀ s ∈ Ioo 0 ℓ, HasDerivAt (fun t => k * deriv θ t)
      (p * (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) -
        lam * sin (θ s) + μ * cos (θ s)) s) :
    ∃ σ c : ℝ, ∀ s ∈ Ioo 0 ℓ,
      E (1 / 2) (-σ / k) (p / k) (deriv θ s)
        (deriv (deriv θ) s + sqrt 2 * deriv θ s) = c ∧
      HasDerivAt (deriv θ)
        (gy (deriv θ s) (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s ∧
      HasDerivAt (fun t => deriv (deriv θ) t + sqrt 2 * deriv θ t)
        (-gx (1 / 2) (-σ / k) (p / k) (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s := by
  obtain ⟨σ, heq⟩ := pressure_angle_curvature hθ hAngle
  have hκ : ContDiff ℝ 2 (deriv θ) := hθ.deriv' (n := 2)
  have hforced : ∀ s ∈ Ioo 0 ℓ,
      k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
        σ * deriv θ s = k * (p / k) := by
    intro s hs
    rw [heq s hs]
    field_simp
  obtain ⟨c, hc⟩ := LinearInputCurvatureBridge.forced_energy_constant (ne_of_gt hk) hκ hforced
  refine ⟨σ, c, fun s hs => ⟨hc s hs, ?_⟩⟩
  exact LinearInputCurvatureBridge.forced_phase_hasDerivAt (ne_of_gt hk) hκ (hforced s hs)

/-- Equality of actual first derivatives suffices; C3 regularity supplies the
HasDerivAt form used by the preceding pressure-to-phase theorem. -/
theorem pressure_angle_eq_phase_energy
    {θ : ℝ → ℝ} {ℓ k p lam μ : ℝ} (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hAngle : ∀ s ∈ Ioo 0 ℓ, deriv (fun t => k * deriv θ t) s =
      p * (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) -
        lam * sin (θ s) + μ * cos (θ s)) :
    ∃ σ c : ℝ, ∀ s ∈ Ioo 0 ℓ,
      E (1 / 2) (-σ / k) (p / k) (deriv θ s)
        (deriv (deriv θ) s + sqrt 2 * deriv θ s) = c ∧
      HasDerivAt (deriv θ)
        (gy (deriv θ s) (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s ∧
      HasDerivAt (fun t => deriv (deriv θ) t + sqrt 2 * deriv θ t)
        (-gx (1 / 2) (-σ / k) (p / k) (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s := by
  apply pressure_angle_phase_energy hk hθ
  intro s hs
  have hd := ((hθ.deriv' (n := 2)).differentiable (by norm_num) s).hasDerivAt.const_mul k
  exact hd.congr_deriv (hd.deriv.symm.trans (hAngle s hs))

end LinearInputPressureCurvature
