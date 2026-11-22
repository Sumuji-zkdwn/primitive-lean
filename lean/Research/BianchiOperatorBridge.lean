import Research.RicciFlatBianchiYangMills
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Jacobi -> second Bianchi for matrix connection operators

The operator connection has F_ij = [N_i,N_j] and
D_k F_ij = [N_k,F_ij]. Jacobi implies second Bianchi without assuming it.
This is a finite operator model for a commuting coordinate frame, NOT
a smooth Levi-Civita Riemann tensor.

The second section imports the ACTUAL pinned mathlib Levi-Civita
construction and checks metric compatibility and torsion-free facts.
Mathlib's curvature-to-operator identification is not claimed.
-/

namespace BianchiOperatorBridge

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℚ

def bracket {n : ℕ} (A B : Mat n) : Mat n := A * B - B * A

theorem bracket_skew {n : ℕ} (A B : Mat n) :
    bracket A B = -bracket B A := by
  unfold bracket
  abel

theorem bracket_neg_right {n : ℕ} (A B : Mat n) :
    bracket A (-B) = -bracket A B := by
  unfold bracket
  simp only [mul_neg, neg_mul]
  abel

/-- Operator Jacobi, proved by matrix associativity. -/
theorem bracket_jacobi {n : ℕ} (A B C : Mat n) :
    bracket A (bracket B C) +
      bracket B (bracket C A) +
      bracket C (bracket A B) = 0 := by
  unfold bracket
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

abbrev ConnectionOps (n : ℕ) := Fin n → Mat n

def curvature {n : ℕ} (N : ConnectionOps n)
    (i j : Fin n) : Mat n := bracket (N i) (N j)

def covariantCurvature {n : ℕ} (N : ConnectionOps n)
    (k i j : Fin n) : Mat n :=
  bracket (N k) (curvature N i j)

/-- Second Bianchi follows from Jacobi, not a postulated axiom. -/
theorem operator_second_bianchi {n : ℕ}
    (N : ConnectionOps n) (e c d : Fin n) :
    covariantCurvature N e c d +
      covariantCurvature N c d e +
      covariantCurvature N d e c = 0 := by
  exact bracket_jacobi (N e) (N c) (N d)

def derivativeTensor {n : ℕ} (N : ConnectionOps n) :
    RicciFlatBianchiYangMills.CurvatureDerivative n :=
  fun e a b c d => (covariantCurvature N e c d) a b

/-- Derived in precisely the tensor format required by PR #186. -/
theorem tensor_second_bianchi {n : ℕ}
    (N : ConnectionOps n) :
    RicciFlatBianchiYangMills.SecondBianchi (derivativeTensor N) := by
  intro e a b c d
  have h := operator_second_bianchi N e c d
  have hentry := congrArg (fun M : Mat n => M a b) h
  simpa [derivativeTensor, Matrix.add_apply] using hentry

theorem tensor_skew_last_pair {n : ℕ} (N : ConnectionOps n) :
    RicciFlatBianchiYangMills.SkewLastPair (derivativeTensor N) := by
  intro e a b c d
  have h : covariantCurvature N e c d =
      -covariantCurvature N e d c := by
    unfold covariantCurvature curvature
    rw [bracket_skew (N c) (N d), bracket_neg_right]
  have he := congrArg (fun M : Mat n => M a b) h
  simpa [derivativeTensor] using he

/-- Contract Bianchi without assuming Bianchi as an input hypothesis. -/
theorem contracted_for_operator_connection {n : ℕ}
    (N : ConnectionOps n) (signature : Fin n → ℚ)
    (b c d : Fin n) :
    RicciFlatBianchiYangMills.FirstPairDivergence
      signature (derivativeTensor N) b c d =
    RicciFlatBianchiYangMills.RicciDerivative
      signature (derivativeTensor N) c b d -
    RicciFlatBianchiYangMills.RicciDerivative
      signature (derivativeTensor N) d b c := by
  exact RicciFlatBianchiYangMills.contracted_second_bianchi
    signature (derivativeTensor N)
    (tensor_second_bianchi N) (tensor_skew_last_pair N) b c d

/-- Pair exchange and parallel Ricci are still additional hypotheses;
    a matrix operator connection is not necessarily Levi-Civita. -/
theorem conditional_yang_mills {n : ℕ}
    (N : ConnectionOps n) (signature : Fin n → ℚ)
    (hEx : RicciFlatBianchiYangMills.ExchangePairs (derivativeTensor N))
    (hParallel : ∀ e b d,
      RicciFlatBianchiYangMills.RicciDerivative
        signature (derivativeTensor N) e b d = 0) :
    ∀ a b d,
      RicciFlatBianchiYangMills.YangMillsDivergence
        signature (derivativeTensor N) a b d = 0 :=
  RicciFlatBianchiYangMills.parallel_ricci_implies_yang_mills
    signature (derivativeTensor N)
    (tensor_second_bianchi N) (tensor_skew_last_pair N)
    hEx hParallel

/-- Explicit non-flat finite operator connection. -/
def op0 : Mat 3 := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
def op1 : Mat 3 := !![0, 0, 0; 1, 0, 0; 0, 0, 0]
def ops3 (i : Fin 3) : Mat 3 :=
  if i = 0 then op0 else if i = 1 then op1 else 0

theorem ops3_curvature_nonzero : (curvature ops3 0 1) 0 0 = 1 := by
  norm_num [curvature, bracket, ops3, op0, op1,
    Matrix.mul_apply, Fin.sum_univ_succ]

theorem ops3_second_bianchi :
    RicciFlatBianchiYangMills.SecondBianchi (derivativeTensor ops3) :=
  tensor_second_bianchi ops3

end BianchiOperatorBridge

/-!
## Verified facts about the ACTUAL mathlib Levi-Civita connection

The pinned Mathlib Levi-Civita API concerns smooth finite-dimensional
Riemannian manifolds. It proves the constructed connection is metric
compatible and torsion free. We have not built its Riemann curvature
or its derivative within this file. The operator-model Bianchi theorem
must not be mistaken for a completed manifold-level instance.
-/

namespace MathlibLeviCivitaBridge

open Bundle FiberBundle Function NormedSpace VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]
  [FiniteDimensional ℝ E]

theorem actual_levi_civita_is_metric_compatible :
    (CovariantDerivative.leviCivitaConnection I M).IsMetricCompatible
      (M := M) (V := TangentSpace I) :=
  (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).isMetricCompatible

theorem actual_levi_civita_torsion_zero :
    (CovariantDerivative.leviCivitaConnection I M).torsion = 0 :=
  (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).torsion

theorem actual_levi_civita_exists :
    (CovariantDerivative.leviCivitaConnection I M).IsLeviCivitaConnection :=
  CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I

end MathlibLeviCivitaBridge
