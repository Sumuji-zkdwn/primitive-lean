import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-! Classical first integral and curvature equation. Derivative hypotheses below
are local jets of actual functions, rather than formal independent symbols. -/

noncomputable section
open Real Set Filter
open scoped Topology
namespace Elastica

/-- Differentiating the usual first integral using the angle equation. -/
theorem firstIntegral_hasDerivAt
    {θ κ M ε : ℝ → ℝ} {lam μ s κ' : ℝ}
    (hθ : HasDerivAt θ (κ s) s) (hκ : HasDerivAt κ κ' s)
    (hε : HasDerivAt ε (M s) (κ s))
    (hM : HasDerivAt M (-lam * sin (θ s) + μ * cos (θ s)) s) :
    HasDerivAt
      (fun t => κ t * M t - ε (κ t) - lam * cos (θ t) - μ * sin (θ t)) 0 s := by
  convert (((hκ.mul hM).sub (hε.comp s hκ)).sub
    (hθ.cos.const_mul lam)).sub (hθ.sin.const_mul μ) using 1
  ring

/-- On an open connected interval the first integral is constant. -/
theorem firstIntegral_constant
    {θ κ M ε : ℝ → ℝ} {lam μ a b : ℝ}
    (hθ : ∀ s ∈ Ioo a b, HasDerivAt θ (κ s) s)
    (hκ : ∀ s ∈ Ioo a b, DifferentiableAt ℝ κ s)
    (hε : ∀ s ∈ Ioo a b, HasDerivAt ε (M s) (κ s))
    (hM : ∀ s ∈ Ioo a b, HasDerivAt M (-lam * sin (θ s) + μ * cos (θ s)) s) :
    ∃ σ : ℝ, ∀ s ∈ Ioo a b,
      κ s * M s - ε (κ s) - lam * cos (θ s) - μ * sin (θ s) = σ := by
  apply isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
  · intro s hs
    exact (firstIntegral_hasDerivAt (hθ s hs) (hκ s hs).hasDerivAt
      (hε s hs) (hM s hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    exact (firstIntegral_hasDerivAt (hθ s hs) (hκ s hs).hasDerivAt
      (hε s hs) (hM s hs)).deriv

/-- Differentiating the right-hand side of the angle equation. -/
theorem angleForce_hasDerivAt {θ κ : ℝ → ℝ} {lam μ s : ℝ}
    (hθ : HasDerivAt θ (κ s) s) :
    HasDerivAt (fun t => -lam * sin (θ t) + μ * cos (θ t))
      (-(lam * cos (θ s) + μ * sin (θ s)) * κ s) s := by
  convert (hθ.sin.const_mul (-lam)).add (hθ.cos.const_mul μ) using 1
  ring

/-- Algebraic elimination of the two force components; no division by ε'' occurs. -/
theorem curvature_equation_of_firstIntegral
    {κ M E M'' lam μ θ σ : ℝ}
    (hsecond : M'' = -(lam * cos θ + μ * sin θ) * κ)
    (hfirst : κ * M - E - lam * cos θ - μ * sin θ = σ) :
    M'' + κ ^ 2 * M - κ * E - σ * κ = 0 := by
  rw [hsecond]
  nlinarith [congrArg (fun x : ℝ => x * κ) hfirst]

/-- The general curvature equation with the actual density derivative substituted. -/
theorem curvature_equation
    {θ κ ε : ℝ → ℝ} {lam μ σ s : ℝ}
    (hsecond : deriv (deriv (fun t => deriv ε (κ t))) s =
      -(lam * cos (θ s) + μ * sin (θ s)) * κ s)
    (hfirst : κ s * deriv ε (κ s) - ε (κ s) - lam * cos (θ s) -
      μ * sin (θ s) = σ) :
    deriv (deriv (fun t => deriv ε (κ t))) s +
      κ s ^ 2 * deriv ε (κ s) - κ s * ε (κ s) - σ * κ s = 0 :=
  curvature_equation_of_firstIntegral hsecond hfirst

/-- The second derivative is derived from the angle equation on an open interval.
It is not an extra hypothesis about an independent second-order symbol. -/
theorem second_derivative_of_angle_equation
    {θ κ M : ℝ → ℝ} {lam μ a b s : ℝ} (hs : s ∈ Ioo a b)
    (hθ : HasDerivAt θ (κ s) s)
    (hM : ∀ t ∈ Ioo a b, HasDerivAt M (-lam * sin (θ t) + μ * cos (θ t)) t) :
    deriv (deriv M) s = -(lam * cos (θ s) + μ * sin (θ s)) * κ s := by
  have heq : deriv M =ᶠ[𝓝 s] (fun t => -lam * sin (θ t) + μ * cos (θ t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact (hM t ht).deriv
  exact ((angleForce_hasDerivAt hθ).congr_of_eventuallyEq heq).deriv

/-- From the angle equation to both the first integral and the actual curvature
equation, on the same connected interval. The density derivative is genuine. -/
theorem firstIntegral_and_curvature_of_angle
    {θ κ ε : ℝ → ℝ} {lam μ a b : ℝ}
    (hθ : ∀ s ∈ Ioo a b, HasDerivAt θ (κ s) s)
    (hκ : ∀ s ∈ Ioo a b, DifferentiableAt ℝ κ s)
    (hε : ∀ s ∈ Ioo a b, DifferentiableAt ℝ ε (κ s))
    (hAngle : ∀ s ∈ Ioo a b,
      HasDerivAt (fun t => deriv ε (κ t)) (-lam * sin (θ s) + μ * cos (θ s)) s) :
    ∃ σ : ℝ, ∀ s ∈ Ioo a b,
      (κ s * deriv ε (κ s) - ε (κ s) - lam * cos (θ s) - μ * sin (θ s) = σ) ∧
      (deriv (deriv (fun t => deriv ε (κ t))) s +
        κ s ^ 2 * deriv ε (κ s) - κ s * ε (κ s) - σ * κ s = 0) := by
  obtain ⟨σ, hσ⟩ := firstIntegral_constant hθ hκ (fun s hs => (hε s hs).hasDerivAt) hAngle
  refine ⟨σ, fun s hs => ⟨hσ s hs, ?_⟩⟩
  exact curvature_equation (second_derivative_of_angle_equation hs (hθ s hs) hAngle) (hσ s hs)

/-- C³ angles and densities supply the differentiability hypotheses needed above. -/
theorem smooth_angle_firstIntegral_and_curvature
    {θ ε : ℝ → ℝ} {lam μ a b : ℝ}
    (hθ : ContDiff ℝ 3 θ) (hε : ContDiff ℝ 3 ε)
    (hAngle : ∀ s ∈ Ioo a b,
      deriv (fun t => deriv ε (deriv θ t)) s = -lam * sin (θ s) + μ * cos (θ s)) :
    ∃ σ : ℝ, ∀ s ∈ Ioo a b,
      (deriv θ s * deriv ε (deriv θ s) - ε (deriv θ s) -
        lam * cos (θ s) - μ * sin (θ s) = σ) ∧
      (deriv (deriv (fun t => deriv ε (deriv θ t))) s +
        (deriv θ s) ^ 2 * deriv ε (deriv θ s) -
        deriv θ s * ε (deriv θ s) - σ * deriv θ s = 0) := by
  have hθd : Differentiable ℝ θ := hθ.differentiable (by norm_num)
  have hκ : ContDiff ℝ 2 (deriv θ) := hθ.deriv' (n := 2)
  have hε' : ContDiff ℝ 2 (deriv ε) := hε.deriv' (n := 2)
  have hM : Differentiable ℝ (fun t => deriv ε (deriv θ t)) :=
    (hε'.comp hκ).differentiable (by norm_num)
  apply firstIntegral_and_curvature_of_angle (fun s _ => (hθd s).hasDerivAt)
    (fun s _ => hκ.differentiable (by norm_num) s)
    (fun s _ => hε.differentiable (by norm_num) (deriv θ s))
  intro s hs
  exact (hM s).hasDerivAt.congr_deriv (hAngle s hs)

/-- Derivative of the quadratic density, with stiffness k retained. -/
theorem quadratic_density_hasDerivAt (k q : ℝ) :
    HasDerivAt (fun x : ℝ => k * x ^ 2 / 2) (k * q) q := by
  convert (((hasDerivAt_id q).pow 2).const_mul k).div_const 2 using 1
  simp only [id_eq]
  ring

/-- The actual second derivative of ε'(κ) for a quadratic density. -/
theorem quadratic_moment_second_derivative
    {κ : ℝ → ℝ} (k : ℝ) (hκ : ContDiff ℝ 2 κ) (s : ℝ) :
    deriv (deriv (fun t => deriv (fun q : ℝ => k * q ^ 2 / 2) (κ t))) s =
      k * deriv (deriv κ) s := by
  have hfun : (fun t => deriv (fun q : ℝ => k * q ^ 2 / 2) (κ t)) = (fun t => k * κ t) := by
    funext t
    exact (quadratic_density_hasDerivAt k (κ t)).deriv
  rw [hfun]
  have hd : deriv (fun t => k * κ t) = (fun t => k * deriv κ t) := by
    funext t
    exact ((hκ.differentiable (by norm_num) t).hasDerivAt.const_mul k).deriv
  rw [hd]
  exact ((hκ.differentiable_deriv_two s).hasDerivAt.const_mul k).deriv

/-- A quadratic instance of the actual functional equation is the classical
elastica equation, rather than only a polynomial substitution. -/
theorem quadratic_curvature_equation
    {κ : ℝ → ℝ} {k σ s : ℝ} (hκ : ContDiff ℝ 2 κ)
    (h : deriv (deriv (fun t => deriv (fun q : ℝ => k * q ^ 2 / 2) (κ t))) s +
      κ s ^ 2 * deriv (fun q : ℝ => k * q ^ 2 / 2) (κ s) -
      κ s * (k * (κ s) ^ 2 / 2) - σ * κ s = 0) :
    k * deriv (deriv κ) s + k * (κ s) ^ 3 / 2 - σ * κ s = 0 := by
  rw [quadratic_moment_second_derivative k hκ s,
    (quadratic_density_hasDerivAt k (κ s)).deriv] at h
  nlinarith [h]

/-- Substitution of ε(κ)=kκ²/2 recovers the classical polynomial expression. -/
theorem quadratic_curvature_expression (k κ κ'' σ : ℝ) :
    k * κ'' + κ ^ 2 * (k * κ) - κ * (k * κ ^ 2 / 2) - σ * κ =
      k * κ'' + k * κ ^ 3 / 2 - σ * κ := by ring

/-- An affine change of density changes σ by -b and leaves the equation unchanged. -/
theorem affine_density_curvature_expression (κ M E M'' σ a b : ℝ) :
    M'' + κ ^ 2 * (M + a) - κ * (E + a * κ + b) - (σ - b) * κ =
      M'' + κ ^ 2 * M - κ * E - σ * κ := by ring

end Elastica
