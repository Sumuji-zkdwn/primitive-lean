import Research.SmoothCurvaturePairSymmetry
import Mathlib.Tactic

/-!
# Metric-compatible contraction of the covariant curvature derivative

This algebraic module proves the exact remaining *trace commutation
calculation* over R for a finite orthonormal frame whose connection
coefficients are skew. It is a standalone frame identity, not a new
smooth Levi-Civita theorem.

Given a curvature field R_abcd, a **linear** directional derivative
on scalar fields, and skew frame coefficients Gamma_eij, construct
covariant derivative D_e R_abcd with corrections in all four slots.

Then prove, without postulating the outcome,
  sum_i (nabla_e R)_{i b i d} = (nabla_e Ric)_{bd}.
The cancellation of the two contracted frame corrections is proved
using skew symmetry and a double-sum reindexing.

Hence an identically zero Ricci field has zero covariant Ricci
derivative. This discharges a nontrivial *algebraic* ingredient left
by draft PR #191.

The extra analytic bridge (to the actual metric's curvature and its
derivative in local orthonormal frames) remains explicit. In
particular the directional-derivative linear map is not claimed to
be automatically constructed from Mathlib's mvfderiv, which is a
junk-valued operator on non-differentiable functions.
-/

namespace RicciTraceCovariance

/-- A connection coefficient matrix \Gamma_{e,i,j} skew in its frame indices. -/
def SkewFrame {n : ℕ} (Gamma : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, Gamma i j = -Gamma j i

/-- Finite skew coefficients cancel against a symmetric pairing. -/
theorem skew_double_sum_swap {n : ℕ}
    (omega : Fin n → Fin n → ℝ)
    (T : Fin n → Fin n → ℝ)
    (homega : SkewFrame omega) :
    (∑ i : Fin n, ∑ j : Fin n, omega i j * T j i) =
      -(∑ i : Fin n, ∑ j : Fin n, omega i j * T i j) := by
  calc
    (∑ i : Fin n, ∑ j : Fin n, omega i j * T j i)
        = ∑ i : Fin n, ∑ j : Fin n, omega j i * T i j := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, (-omega i j) * T i j := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [homega j i]
    _ = -(∑ i : Fin n, ∑ j : Fin n, omega i j * T i j) := by
          simp only [neg_mul, Finset.sum_neg_distrib]

theorem skew_symmetric_contraction_zero {n : ℕ}
    (omega : Fin n → Fin n → ℝ)
    (T : Fin n → Fin n → ℝ)
    (homega : SkewFrame omega) :
    (∑ i : Fin n, ∑ j : Fin n,
      omega i j * (T j i + T i j)) = 0 := by
  have h := skew_double_sum_swap omega T homega
  simp only [mul_add, Finset.sum_add_distrib]
  linarith

/-- A general real-valued moving-frame curvature model.
The scalar derivative is a linear map on the chosen space of scalar
fields. It models ordinary directional differentiation on smooth
fields, rather than assuming the Ricci trace derivative result.
For a concrete manifold a compatible smooth instance is still needed. -/
structure FrameJet (P : Type*) (n : ℕ) where
  R : P → Fin n → Fin n → Fin n → Fin n → ℝ
  ordinaryDeriv : Fin n → (P → ℝ) →ₗ[ℝ] (P → ℝ)
  Gamma : P → Fin n → Fin n → Fin n → ℝ
  gammaSkew : ∀ (p : P) (e i j : Fin n),
    Gamma p e i j = -Gamma p e j i

variable {P : Type*} {n : ℕ}

/-- Trace of the (0,4) Riemann curvature in an orthonormal frame. -/
def ricci (J : FrameJet P n) (p : P) (b d : Fin n) : ℝ :=
  ∑ i : Fin n, J.R p i b i d

/-- Ordinary directional partial derivative of a frame component. -/
def ordinaryR (J : FrameJet P n)
    (p : P) (e a b c d : Fin n) : ℝ :=
  J.ordinaryDeriv e (fun q => J.R q a b c d) p

/-- The tensorial (0,4) covariant curvature derivative in a moving frame.
Each of four input slots contributes its connection correction. -/
def covR (J : FrameJet P n)
    (p : P) (e a b c d : Fin n) : ℝ :=
  ordinaryR J p e a b c d
    - (∑ j : Fin n, J.Gamma p e a j * J.R p j b c d)
    - (∑ j : Fin n, J.Gamma p e b j * J.R p a j c d)
    - (∑ j : Fin n, J.Gamma p e c j * J.R p a b j d)
    - (∑ j : Fin n, J.Gamma p e d j * J.R p a b c j)

/-- The covariant derivative of the Ricci (0,2) tensor, computed
*independently* from the ordinary derivative of the Ricci field. -/
def covRicci (J : FrameJet P n)
    (p : P) (e b d : Fin n) : ℝ :=
  J.ordinaryDeriv e (fun q => ricci J q b d) p
    - (∑ j : Fin n, J.Gamma p e b j * ricci J p j d)
    - (∑ j : Fin n, J.Gamma p e d j * ricci J p b j)

/-- The Ricci trace's directional derivative is the trace of
ordinary curvature component derivatives, by finite-sum linearity. -/
theorem derivative_ricci_trace (J : FrameJet P n)
    (p : P) (e b d : Fin n) :
    J.ordinaryDeriv e (fun q => ricci J q b d) p =
      ∑ i : Fin n, ordinaryR J p e i b i d := by
  have hfun : (fun q : P => ricci J q b d) =
      ∑ i : Fin n, (fun q : P => J.R q i b i d) := by
    funext q
    simp only [ricci, Finset.sum_apply]
  rw [hfun, map_sum]
  simp only [Finset.sum_apply, ordinaryR]

/-- Every correction of the *contracted* first and third frame slots
cancels because the metric-compatible Gamma is skew. -/
theorem contracted_gamma_cancels (J : FrameJet P n)
    (p : P) (e b d : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n,
      J.Gamma p e i j * J.R p j b i d) +
    (∑ i : Fin n, ∑ j : Fin n,
      J.Gamma p e i j * J.R p i b j d) = 0 := by
  have h := skew_symmetric_contraction_zero
    (fun i j => J.Gamma p e i j)
    (fun i j => J.R p i b j d)
    (J.gammaSkew p e)
  simpa only [mul_add, Finset.sum_add_distrib] using h

/-- This is the essential finite-index tensor theorem:
  trace_g(∇_e Rm) = ∇_e(trace_g Rm).
It does NOT assume ∇Ric=0, Bianchi, or any Yang--Mills condition. -/
theorem trace_commutes_with_covariant_derivative (J : FrameJet P n)
    (p : P) (e b d : Fin n) :
    (∑ i : Fin n, covR J p e i b i d) = covRicci J p e b d := by
  have hCross := contracted_gamma_cancels J p e b d
  have hB :
      (∑ i : Fin n, ∑ j : Fin n,
         J.Gamma p e b j * J.R p i j i d) =
        ∑ j : Fin n, J.Gamma p e b j * ricci J p j d := by
    rw [Finset.sum_comm]
    simp only [ricci, Finset.mul_sum]
  have hD :
      (∑ i : Fin n, ∑ j : Fin n,
         J.Gamma p e d j * J.R p i b i j) =
        ∑ j : Fin n, J.Gamma p e d j * ricci J p b j := by
    rw [Finset.sum_comm]
    simp only [ricci, Finset.mul_sum]
  have hOrd := derivative_ricci_trace J p e b d
  unfold covR covRicci
  simp only [Finset.sum_sub_distrib]
  rw [hB, hD, hOrd]
  linarith

/-- If the global Ricci field is zero, its *covariant*
derivative is zero. No independent parallel-Ricci postulate. -/
theorem ricci_flat_derivative_zero (J : FrameJet P n)
    (hFlat : ∀ p b d, ricci J p b d = 0) :
    ∀ p e b d, covRicci J p e b d = 0 := by
  intro p e b d
  unfold covRicci
  have hf : (fun q : P => ricci J q b d) = 0 := by
    funext q
    exact hFlat q b d
  rw [hf, map_zero]
  simp only [Pi.zero_apply]
  simp [hFlat]

/-- The missing assumption "Ricci derivative vanishes" in PR #191
follows from genuine Ricci-flatness once metric-compatible
frame derivative formulas are available. -/
theorem ricci_flat_curvature_trace_zero (J : FrameJet P n)
    (hFlat : ∀ p b d, ricci J p b d = 0) :
    ∀ p e b d,
      (∑ i : Fin n, covR J p e i b i d) = 0 := by
  intro p e b d
  rw [trace_commutes_with_covariant_derivative]
  exact ricci_flat_derivative_zero J hFlat p e b d

/-- Combine with the *same real tensor* Bianchi contraction and
pair-exchange from PR #191. This is still an algebraic frame model;
a smooth-manifold geometric instance is a separate bridge. -/
theorem ricci_flat_frame_yang_mills
    (J : FrameJet P n)
    (hFlat : ∀ p b d, ricci J p b d = 0)
    (hB : ∀ p,
      SmoothCurvatureRealFrame.SecondBianchi (covR J p))
    (hSk : ∀ p,
      SmoothCurvatureRealFrame.SkewLast (covR J p))
    (hEx : ∀ p,
      SmoothCurvatureRealFrame.PairExchange (covR J p)) :
    ∀ p a b d,
      SmoothCurvatureRealFrame.YangMillsDivergence (covR J p) a b d = 0 := by
  intro p a b d
  rw [SmoothCurvatureRealFrame.yang_mills_eq_ricci_derivatives_real
    (covR J p) (hB p) (hSk p) (hEx p)]
  have hz : ∀ e b d,
      SmoothCurvatureRealFrame.RicciDerivative (covR J p) e b d = 0 := by
    intro e b d
    unfold SmoothCurvatureRealFrame.RicciDerivative
    exact ricci_flat_curvature_trace_zero J hFlat p e b d
  rw [hz a d b, hz b d a]
  ring

end RicciTraceCovariance
