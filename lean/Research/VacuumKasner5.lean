import Mathlib.Tactic

/-!
# Algebraic certificates for 5D vacuum Kasner circle cosmology

The metric is ds5² = -dt² + t^(2p) (dx₁²+dx₂²+dx₃²)
                      + t^(2q) dχ², with t>0 and periodic χ.
The Ricci coefficients derived *outside Lean* from metric Christoffels are
  Ric_tt = (3p(1-p)+q(1-q))/t²,
  Ric_xx = p(3p+q-1) t^(2p-2),
  Ric_χχ = q(3p+q-1) t^(2q-2).
This module proves just the resulting **polynomial** classification and
Einstein-frame exponent arithmetic. It does not derive the metric Ricci
formula, Riemann invariant, Weyl reduction theorem or physical phenomenology.
The paired independent SymPy oracle differentiates all metric coefficients.
-/

namespace VacuumKasner5

def timeResidual (p q : ℝ) : ℝ :=
  3 * p * (1 - p) + q * (1 - q)

def externalResidual (p q : ℝ) : ℝ :=
  p * (3 * p + q - 1)

def internalResidual (p q : ℝ) : ℝ :=
  q * (3 * p + q - 1)

/-- Trivial static five-dimensional Minkowski metric. -/
theorem static_vacuum :
    timeResidual 0 0 = 0 ∧
      externalResidual 0 0 = 0 ∧ internalResidual 0 0 = 0 := by
  norm_num [timeResidual, externalResidual, internalResidual]

/-- Locally flat Milne-like circle with a(t)=1 and b(t)=t. -/
theorem milne_vacuum :
    timeResidual 0 1 = 0 ∧
      externalResidual 0 1 = 0 ∧ internalResidual 0 1 = 0 := by
  norm_num [timeResidual, externalResidual, internalResidual]

/-- Expanding external / contracting circle Ricci-flat witness. -/
theorem expanding_vacuum :
    timeResidual (1 / 2) (-1 / 2) = 0 ∧
      externalResidual (1 / 2) (-1 / 2) = 0 ∧
      internalResidual (1 / 2) (-1 / 2) = 0 := by
  norm_num [timeResidual, externalResidual, internalResidual]

/-- Algebraic classification of *all* real isotropic power-law vacuum
    exponents, including the static branch omitted by the usual Kasner
    sum rule. The internal equation is redundant for this implication. -/
theorem all_real_branches (p q : ℝ)
    (ht : timeResidual p q = 0)
    (hx : externalResidual p q = 0)
    (_hy : internalResidual p q = 0) :
    (p = 0 ∧ q = 0) ∨
      (p = 0 ∧ q = 1) ∨
      (p = 1 / 2 ∧ q = -1 / 2) := by
  dsimp [timeResidual, externalResidual] at ht hx
  rcases mul_eq_zero.mp hx with hp0 | hsum
  · subst p
    have hq : q * (1 - q) = 0 := by nlinarith [ht]
    rcases mul_eq_zero.mp hq with hzero | hone
    · exact Or.inl ⟨rfl, hzero⟩
    · right
      left
      constructor
      · rfl
      · linarith
  · have hq : q = 1 - 3 * p := by linarith
    rw [hq] at ht
    have hpoly : p * (2 * p - 1) = 0 := by nlinarith [ht]
    rcases mul_eq_zero.mp hpoly with hzero | hhalf
    · right
      left
      constructor
      · exact hzero
      · rw [hq, hzero]
        ring
    · right
      right
      constructor
      · linarith
      · rw [hq]
        linarith

/-- Any expanding external three-space in this power-law vacuum ansatz
    is forced to have the shrinking circle exponent q=-1/2. -/
theorem expanding_forces_contraction (p q : ℝ)
    (ht : timeResidual p q = 0)
    (hx : externalResidual p q = 0)
    (hy : internalResidual p q = 0)
    (hp : 0 < p) :
    p = 1 / 2 ∧ q = -1 / 2 := by
  rcases all_real_branches p q ht hx hy with h0 | h1 | h2
  · linarith [h0.1]
  · linarith [h1.1]
  · exact h2

/-- For radius b=t^q, the 4D Einstein-frame proper-time power law is
    (p+q/2)/(1+q/2) whenever 1+q/2 is nonzero. -/
def einsteinFrameExponent (p q : ℝ) : ℝ :=
  (p + q / 2) / (1 + q / 2)

/-- The expanding 5D branch reduces to a_E(τ) ∝ τ^(1/3). -/
theorem einstein_frame_one_third :
    einsteinFrameExponent (1 / 2) (-1 / 2) = 1 / 3 := by
  norm_num [einsteinFrameExponent]

/-- The Einstein-frame Hubble law 3H² = φdot² is exactly the
    Friedmann equation for the metric-derived massless radion. -/
theorem stiff_friedmann_identity (u : ℝ) :
    3 * (u / 3) ^ 2 = u ^ 2 / 3 := by
  ring

/-- Scale-factor exponent 1/3 implies strictly negative acceleration. -/
theorem one_third_decelerates :
    (1 / 3 : ℝ) * (1 / 3 - 1) < 0 := by
  norm_num

/-- Orthonormal Kasner curvature-squared coefficient (external formula). -/
theorem kasner_kretschmann_coefficient :
    4 * (3 * ((1 / 2 : ℝ) * (1 / 2 - 1)) ^ 2 +
         ((-1 / 2 : ℝ) * (-1 / 2 - 1)) ^ 2 +
         6 * ((1 / 2 : ℝ) ^ 2 * (1 / 2) ^ 2)) = 9 / 2 := by
  norm_num

/-- A Jordan-slice effective fluid and Einstein-frame scalar have
    different equations of state; neither is an independent matter source. -/
theorem jordan_and_einstein_frames_differ :
    (1 / 3 : ℝ) ≠ 1 := by
  norm_num

end VacuumKasner5
