import Mathlib.Tactic

/-!
# Second Bianchi => Ricci-flat Levi-Civita curvature satisfies Yang--Mills

D e a b c d models (nabla_e R)_(a b c d) in a pseudo-orthonormal
frame, with signature(i) = +/-1. The second Bianchi identity, curvature
symmetries, metric-compatible contraction, and linearity of the
covariant derivative on Ricci fields are explicitly stated assumptions.
No axiom, sorry, or assumption of the final Yang--Mills equation appears.

This module proves the full tensor contraction but does not construct
the smooth Levi-Civita Riemann tensor from a mathlib connection.
-/

namespace RicciFlatBianchiYangMills

abbrev CurvatureDerivative (n : ℕ) :=
  Fin n → Fin n → Fin n → Fin n → Fin n → ℚ

/-- Differential Bianchi with fixed skew-endomorphism pair (a,b). -/
def SecondBianchi {n : ℕ} (D : CurvatureDerivative n) : Prop :=
  ∀ e a b c d, D e a b c d + D c a b d e + D d a b e c = 0

def SkewLastPair {n : ℕ} (D : CurvatureDerivative n) : Prop :=
  ∀ e a b c d, D e a b c d = -D e a b d c

def ExchangePairs {n : ℕ} (D : CurvatureDerivative n) : Prop :=
  ∀ e a b c d, D e a b c d = D e c d a b

/-- Derivative of the trace defining Ricci. -/
def RicciDerivative {n : ℕ}
    (signature : Fin n → ℚ) (D : CurvatureDerivative n)
    (e b d : Fin n) : ℚ :=
  ∑ a : Fin n, signature a * D e a b a d

/-- First pair curvature divergence. -/
def FirstPairDivergence {n : ℕ}
    (signature : Fin n → ℚ) (D : CurvatureDerivative n)
    (b c d : Fin n) : ℚ :=
  ∑ a : Fin n, signature a * D a a b c d

/-- Gauge curvature 2-form divergence, contracting a BASE index. -/
def YangMillsDivergence {n : ℕ}
    (signature : Fin n → ℚ) (D : CurvatureDerivative n)
    (a b d : Fin n) : ℚ :=
  ∑ c : Fin n, signature c * D c a b c d

/-- Genuine contraction of the uncontracted second Bianchi identity. -/
theorem contracted_second_bianchi {n : ℕ}
    (signature : Fin n → ℚ) (D : CurvatureDerivative n)
    (hB : SecondBianchi D) (hSk : SkewLastPair D)
    (b c d : Fin n) :
    FirstPairDivergence signature D b c d =
      RicciDerivative signature D c b d -
        RicciDerivative signature D d b c := by
  change (∑ a : Fin n, signature a * D a a b c d) =
    (∑ a : Fin n, signature a * D c a b a d) -
      (∑ a : Fin n, signature a * D d a b a c)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hb := hB a a b c d
  have hs := hSk c a b d a
  rw [hs] at hb
  have hi : D a a b c d = D c a b a d - D d a b a c := by
    linarith
  rw [hi]
  ring

/-- Pair exchange moves the contraction onto the genuine gauge-field
    base indices, rather than the endomorphism indices. -/
theorem yang_mills_divergence_eq_ricci_derivatives {n : ℕ}
    (signature : Fin n → ℚ) (D : CurvatureDerivative n)
    (hB : SecondBianchi D) (hSk : SkewLastPair D)
    (hEx : ExchangePairs D) (a b d : Fin n) :
    YangMillsDivergence signature D a b d =
      RicciDerivative signature D a d b -
        RicciDerivative signature D b d a := by
  have hEq : YangMillsDivergence signature D a b d =
      FirstPairDivergence signature D d a b := by
    unfold YangMillsDivergence FirstPairDivergence
    apply Finset.sum_congr rfl
    intro i hi
    rw [hEx i a b i d]
  rw [hEq]
  exact contracted_second_bianchi signature D hB hSk d a b

/-- A covariantly constant Ricci tensor makes the spin curvature YM. -/
theorem parallel_ricci_implies_yang_mills {n : ℕ}
    (signature : Fin n → ℚ) (D : CurvatureDerivative n)
    (hB : SecondBianchi D) (hSk : SkewLastPair D)
    (hEx : ExchangePairs D)
    (hParallel : ∀ e b d, RicciDerivative signature D e b d = 0) :
    ∀ a b d, YangMillsDivergence signature D a b d = 0 := by
  intro a b d
  rw [yang_mills_divergence_eq_ricci_derivatives
      signature D hB hSk hEx a b d]
  rw [hParallel a d b, hParallel b d a]
  ring

abbrev CurvatureField (P : Type*) (n : ℕ) :=
  P → Fin n → Fin n → Fin n → Fin n → ℚ

abbrev RicciField (P : Type*) (n : ℕ) :=
  P → Fin n → Fin n → ℚ

abbrev CovRicciField (P : Type*) (n : ℕ) :=
  P → Fin n → Fin n → Fin n → ℚ

/-- The pseudo-orthonormal metric contraction of the Riemann tensor. -/
def Ricci {P : Type*} {n : ℕ}
    (signature : Fin n → ℚ) (R : CurvatureField P n) :
    RicciField P n :=
  fun p b d => ∑ a : Fin n, signature a * R p a b a d

/-- Sufficient geometric interface for a smooth Levi-Civita connection.

    Metric compatibility: derivative of Ricci agrees with the
    contraction of the covariant derivative of curvature.
    The covariant derivative of a Ricci FIELD is linear (so d0=0).

    This is an abstract *conditional* geometry record. Constructing an
    instance from a concrete manifold connection is a separate problem. -/
structure BianchiConnectionData (P : Type*) (n : ℕ) where
  signature : Fin n → ℚ
  sign_unit : ∀ i, signature i * signature i = 1
  curvature : CurvatureField P n
  covCurvature : P → CurvatureDerivative n
  covRicci : RicciField P n →ₗ[ℚ] CovRicciField P n
  bianchi : ∀ p, SecondBianchi (covCurvature p)
  skew : ∀ p, SkewLastPair (covCurvature p)
  pairExchange : ∀ p, ExchangePairs (covCurvature p)
  contraction : ∀ p e b d,
    covRicci (Ricci signature curvature) p e b d =
      RicciDerivative signature (covCurvature p) e b d

def IsRicciFlat {P : Type*} {n : ℕ}
    (G : BianchiConnectionData P n) : Prop :=
  ∀ p b d, Ricci G.signature G.curvature p b d = 0

/-- Full implication, no assumption of Yang--Mills:
    global Ricci flatness + second Bianchi + Levi-Civita symmetries
    and metric compatibility imply source-free curvature Yang--Mills. -/
theorem ricci_flat_implies_yang_mills {P : Type*} {n : ℕ}
    (G : BianchiConnectionData P n) (hFlat : IsRicciFlat G) :
    ∀ p a b d, YangMillsDivergence G.signature (G.covCurvature p) a b d = 0 := by
  have hRic : Ricci G.signature G.curvature = 0 := by
    funext p b d
    exact hFlat p b d
  have hD : G.covRicci (Ricci G.signature G.curvature) = 0 := by
    rw [hRic]
    exact map_zero G.covRicci
  have hParallel (p : P) (e b d : Fin n) :
      RicciDerivative G.signature (G.covCurvature p) e b d = 0 := by
    rw [← G.contraction p e b d]
    rw [hD]
    rfl
  intro p a b d
  exact parallel_ricci_implies_yang_mills
    G.signature (G.covCurvature p) (G.bianchi p)
    (G.skew p) (G.pairExchange p) (hParallel p) a b d

/-!
Sanity check: no differential Bianchi, no automatic divergence
vanishing. This fake tensor is not a Levi-Civita curvature tensor.
-/
def counterexampleDerivative : CurvatureDerivative 3 :=
  fun e a b c d =>
    if e = 0 ∧ a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 2 then 1
    else if e = 0 ∧ a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 1 then -1
    else 0

theorem counterexample_skew : SkewLastPair counterexampleDerivative := by
  decide

theorem counterexample_ricci_derivative_zero :
    ∀ e b d, RicciDerivative (fun _ => 1) counterexampleDerivative e b d = 0 := by
  decide

theorem counterexample_nonzero_first_divergence :
    FirstPairDivergence (fun _ => 1) counterexampleDerivative 1 1 2 = 1 := by
  decide

theorem counterexample_not_bianchi :
    ¬ SecondBianchi counterexampleDerivative := by
  decide

end RicciFlatBianchiYangMills
