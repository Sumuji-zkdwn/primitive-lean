import Research.SmoothMetricBianchi
import Research.RicciFlatBianchiYangMills

/-!
# Actual smooth Levi-Civita curvature -> real-index second Bianchi

PR #189 constructs a C2 smooth Levi-Civita connection from a C3
Riemannian metric, then proves the genuine second Bianchi identity.
The older PR #186 formulates its contraction on rational frame tensors.

Here we move the frame algebra to the actual scalar field R, and
instantiate its second Bianchi tensor directly with inner products of
covariant-curvature vectors of the actual mathlib connection.

The last-pair skew is also proved from a real curvature identity, not
assumed. The final Yang-Mills statement still requires the pair-exchange
symmetry and parallel Ricci in the chosen frame as EXPLICIT assumptions;
these are future integration tasks. No independent 4D gauge bosons.
-/

open Bundle FiberBundle VectorField
open scoped Manifold ContDiff RealInnerProductSpace

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  (cov : CovariantDerivative I E (fun x : M => TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]
  [ContMDiffCovariantDerivative cov 2]

/-- The curvature of C3 fields is a C1 section. Derived from its
definition using real covariant derivatives, as in the upstream
CurvatureDeriv proof (Apache-2.0, cited in docs). -/
theorem contMDiff_curvature_bridge
    {Y Z W : Π y : M, TangentSpace I y}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    CMDiff 1 (T% (fun y => cov.curvature Y Z W y)) := by
  have hW3 : CMDiff ((2 : ℕ∞ω) + 1) (T% W) := by
    rw [show ((2 : ℕ∞ω) + 1) = 3 by norm_num]
    exact hW
  have hW2 : CMDiff ((1 : ℕ∞ω) + 1) (T% W) := by
    rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]
    exact hW.of_le (by norm_num)
  have hY1 : CMDiff 1 (T% Y) := hY.of_le (by norm_num)
  have hZ1 : CMDiff 1 (T% Z) := hZ.of_le (by norm_num)
  have hZW : CMDiff ((1 : ℕ∞ω) + 1)
      (T% (fun u => cov W u (Z u))) := by
    rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]
    exact cov.contMDiff_cov_apply hW3 hZ
  have hYW : CMDiff ((1 : ℕ∞ω) + 1)
      (T% (fun u => cov W u (Y u))) := by
    rw [show ((1 : ℕ∞ω) + 1) = 2 by norm_num]
    exact cov.contMDiff_cov_apply hW3 hY
  have t1 : CMDiff 1
      (T% (fun y => cov (fun u => cov W u (Z u)) y (Y y))) :=
    cov.contMDiff_cov_apply hZW hY1
  have t2 : CMDiff 1
      (T% (fun y => cov (fun u => cov W u (Y u)) y (Z y))) :=
    cov.contMDiff_cov_apply hYW hZ1
  have hb : CMDiff 1 (T% (mlieBracket I Y Z)) := fun y =>
    (hY y).mlieBracket_vectorField (n := 2) (m := 1) (hZ y) (by norm_num)
  have t3 : CMDiff 1 (T% (fun y => cov W y (mlieBracket I Y Z y))) :=
    cov.contMDiff_cov_apply hW2 hb
  show CMDiff 1 (T% (((fun y => cov (fun u => cov W u (Z u)) y (Y y))
    - (fun y => cov (fun u => cov W u (Y u)) y (Z y)))
    - (fun y => cov W y (mlieBracket I Y Z y))))
  exact (t1.sub_section t2).sub_section t3

/-- The covariant derivative of R is skew in its two curvature
directions, derived from the antisymmetry of R and differentiability. -/
theorem covCurvature_skew_bridge
    (X : Π y : M, TangentSpace I y)
    {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiff 2 (T% Y)) (hZ : CMDiff 2 (T% Z))
    (hW : CMDiff 3 (T% W)) :
    cov.covCurvature X Y Z W x = -cov.covCurvature X Z Y W x := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have hc : MDiffAt (T% (fun y => cov.curvature Y Z W y)) x :=
    ((cov.contMDiff_curvature_bridge hY hZ hW).mdifferentiable h1) x
  have hneg : (fun y => cov.curvature Z Y W y) =
      -(fun y => cov.curvature Y Z W y) := by
    funext y
    exact cov.curvature_antisymm Z Y W y
  simp only [covCurvature, hneg, cov.neg_apply hc, _root_.neg_apply,
    cov.curvature_antisymm (fun y => cov Z y (X y)) Y W x,
    cov.curvature_antisymm Z (fun y => cov Y y (X y)) W x,
    cov.curvature_antisymm Z Y (fun y => cov W y (X y)) x]
  module

end CovariantDerivative

namespace SmoothCurvatureRealFrame

/-- Covariant derivative of a (0,4) real curvature tensor. -/
abbrev Deriv (n : ℕ) := Fin n → Fin n → Fin n → Fin n → Fin n → ℝ

def SecondBianchi {n : ℕ} (D : Deriv n) : Prop :=
  ∀ e a b c d, D e a b c d + D c a b d e + D d a b e c = 0

def SkewLast {n : ℕ} (D : Deriv n) : Prop :=
  ∀ e a b c d, D e a b c d = -D e a b d c

def PairExchange {n : ℕ} (D : Deriv n) : Prop :=
  ∀ e a b c d, D e a b c d = D e c d a b

def RicciDerivative {n : ℕ} (D : Deriv n)
    (e b d : Fin n) : ℝ :=
  ∑ i : Fin n, D e i b i d

def FirstDivergence {n : ℕ} (D : Deriv n)
    (b c d : Fin n) : ℝ :=
  ∑ i : Fin n, D i i b c d

def YangMillsDivergence {n : ℕ} (D : Deriv n)
    (a b d : Fin n) : ℝ :=
  ∑ i : Fin n, D i a b i d

/-- Real-valued contraction, with NO precontracted Bianchi hypothesis. -/
theorem contracted_bianchi_real {n : ℕ} (D : Deriv n)
    (hB : SecondBianchi D) (hSk : SkewLast D)
    (b c d : Fin n) :
    FirstDivergence D b c d =
      RicciDerivative D c b d - RicciDerivative D d b c := by
  change (∑ i : Fin n, D i i b c d) =
    (∑ i : Fin n, D c i b i d) -
      (∑ i : Fin n, D d i b i c)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hb := hB i i b c d
  have hs := hSk c i b d i
  rw [hs] at hb
  linarith

theorem yang_mills_eq_ricci_derivatives_real {n : ℕ}
    (D : Deriv n) (hB : SecondBianchi D)
    (hSk : SkewLast D) (hEx : PairExchange D) (a b d : Fin n) :
    YangMillsDivergence D a b d =
      RicciDerivative D a d b - RicciDerivative D b d a := by
  have hEq : YangMillsDivergence D a b d =
      FirstDivergence D d a b := by
    unfold YangMillsDivergence FirstDivergence
    apply Finset.sum_congr rfl
    intro i hi
    rw [hEx i a b i d]
  rw [hEq]
  exact contracted_bianchi_real D hB hSk d a b

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  (I : ModelWithCorners ℝ E H) (M : Type*)
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun x : M => TangentSpace I x)]

/-- Build a genuine real curvature-derivative tensor from the actual
Levi-Civita connection, evaluated against any chosen vector fields.
An orthonormal frame is required when interpreting sums as metric
traces; the Bianchi identity itself holds for arbitrary fields. -/
noncomputable def frameDerivative {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M) : Deriv n :=
  fun e a b c d =>
    inner ℝ
      ((CovariantDerivative.leviCivitaConnection I M).covCurvature
        (fr e) (fr c) (fr d) (fr b) x)
      (fr a x)

/-- REAL second Bianchi for the actual Levi-Civita curvature in
any chosen smooth frame, not an axiom in the interface. -/
theorem actual_frame_second_bianchi {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) :
    SecondBianchi (frameDerivative I M fr x) := by
  intro e a b c d
  have h2 (i : Fin n) : CMDiff 2 (T% (fr i)) :=
    (hfr i).of_le (by norm_num)
  have hb := SmoothMetricBianchi.levi_civita_second_bianchi_of_C3_metric
    I M (h2 e) (h2 c) (h2 d) (hfr b)
  have hInner := congrArg
    (fun v : TangentSpace I x => inner ℝ v (fr a x)) hb
  simpa [frameDerivative, inner_add_left] using hInner

/-- This skewness is derived from the actual smooth curvature
rather than postulated on the component tensor. -/
theorem actual_frame_skew_last {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) :
    SkewLast (frameDerivative I M fr x) := by
  intro e a b c d
  have h2 (i : Fin n) : CMDiff 2 (T% (fr i)) :=
    (hfr i).of_le (by norm_num)
  letI : IsContMDiffRiemannianBundle I 1 E
      (fun y : M => TangentSpace I y) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.leviCivitaConnection I M) 1 :=
    SmoothMetricBianchi.levi_civita_C1 I M
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.leviCivitaConnection I M) 2 :=
    SmoothMetricBianchi.levi_civita_C2 I M
  have h := (CovariantDerivative.leviCivitaConnection I M).covCurvature_skew_bridge
    (fr e) (h2 c) (h2 d) (hfr b)
  have he := congrArg
    (fun v : TangentSpace I x => inner ℝ v (fr a x)) h
  simpa [frameDerivative, inner_neg_left] using he

/-- A genuine manifold-frame contraction of smooth second Bianchi. -/
theorem actual_frame_contracted_bianchi {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) (b c d : Fin n) :
    FirstDivergence (frameDerivative I M fr x) b c d =
      RicciDerivative (frameDerivative I M fr x) c b d -
      RicciDerivative (frameDerivative I M fr x) d b c := by
  exact contracted_bianchi_real (frameDerivative I M fr x)
    (actual_frame_second_bianchi I M fr x hfr)
    (actual_frame_skew_last I M fr x hfr) b c d

/-- The corresponding curvature Yang-Mills conclusion with the
two still-missing smooth Riemannian ingredients explicit:
the pair-exchange property of nabla R and parallel Ricci. -/
theorem actual_frame_yang_mills_of_parallel_ricci {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M)
    (hfr : ∀ i, CMDiff 3 (T% (fr i)))
    (hEx : PairExchange (frameDerivative I M fr x))
    (hParallel : ∀ e b d,
      RicciDerivative (frameDerivative I M fr x) e b d = 0) :
    ∀ a b d,
      YangMillsDivergence (frameDerivative I M fr x) a b d = 0 := by
  intro a b d
  rw [yang_mills_eq_ricci_derivatives_real
    (frameDerivative I M fr x)
    (actual_frame_second_bianchi I M fr x hfr)
    (actual_frame_skew_last I M fr x hfr) hEx]
  rw [hParallel a d b, hParallel b d a]
  ring

end SmoothCurvatureRealFrame
