import Research.SmoothCurvatureRealFrame
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

/-!
# Riemann and covariant-Riemann pair symmetry for actual Levi-Civita

A targeted Apache-2.0-licensed adaptation of proofs in:
- RicciFlowBlueprint/Sectional.lean (metric skewness of curvature)
- RicciFlowBlueprint/CurvatureSymm.lean (algebraic pair symmetry)
- RicciFlowBlueprint/Divergence.lean (covariant-derivative pair symmetry)
at upstream SHA c8017e2c26898d11f39cec0dfce89368d5a0506a.

Rather than porting the full Ricci-flow dependency tree, this file
imports the already tested smooth curvature and Bianchi modules.
Its final real component tensor uses the input/output index order
that makes the proven geometric pair-exchange symmetry literal.

The resulting proper Yang-Mills divergence theorem only assumes
that the *real Ricci derivative* vanishes. The last unsolved step
for a global Ricci-flatness theorem is the geometric Ricci trace
compatibility and local orthonormal-frame reduction.
-/

open Bundle VectorField
open scoped Manifold ContDiff

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun (x : M) => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun (x : M) => TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (fun (x : M) => TangentSpace I x) I]
  (cov : CovariantDerivative I E (fun (x : M) => TangentSpace I x))
  [ContMDiffCovariantDerivative cov 1]
  [ContMDiffCovariantDerivative cov 2]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- C2 regularity of the metric inner product of two smooth sections. -/
theorem cmdiff_inner_vector_field_bridge
    {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y)) :
    CMDiff 2 (fun y => ⟪X y, Y y⟫) :=
  ContMDiff.inner_bundle (E := TangentSpace I) (F := E) hX hY

/-- Curvature of a metric-compatible connection is skew-adjoint.
This proof is adapted from upstream Sectional.lean. -/
theorem inner_curvature_self_right_bridge
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : CMDiff 2 (T% Z)) :
    ⟪cov.curvature X Y Z x, Z x⟫ = 0 := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hZm : MDiff (T% Z) := hZ.mdifferentiable h2
  have hAx : MDiffAt (T% (fun y => cov Z y (Y y))) x :=
    cov.mdiffAt_cov_apply hZ hY
  have hBx : MDiffAt (T% (fun y => cov Z y (X y))) x :=
    cov.mdiffAt_cov_apply hZ hX
  have hfC2 : CMDiffAt 2 (fun y => ⟪Z y, Z y⟫) x :=
    (cmdiff_inner_vector_field_bridge hZ hZ) x
  have hdf : ∀ V : Π y : M, TangentSpace I y,
      (fun y => d% (fun z => ⟪Z z, Z z⟫) y (V y))
        = (fun y => ⟪cov Z y (V y), Z y⟫) +
          (fun y => ⟪Z y, cov Z y (V y)⟫) := by
    intro V
    funext y
    exact hcov.mvfderiv_inner_eq V (hZm y) (hZm y)
  have e1 : d% (fun y => d% (fun z => ⟪Z z, Z z⟫) y (Y y)) x (X x)
      = (⟪cov (fun y => cov Z y (Y y)) x (X x), Z x⟫
           + ⟪cov Z x (Y x), cov Z x (X x)⟫)
        + (⟪cov Z x (X x), cov Z x (Y x)⟫
           + ⟪Z x, cov (fun y => cov Z y (Y y)) x (X x)⟫) := by
    rw [hdf Y, mvfderiv_add (MDifferentiableAt.inner_bundle (E := TangentSpace I)
       (F := E) hAx (hZm x))
       (MDifferentiableAt.inner_bundle (E := TangentSpace I)
       (F := E) (hZm x) hAx), add_apply,
      hcov.mvfderiv_inner_eq X hAx (hZm x),
      hcov.mvfderiv_inner_eq X (hZm x) hAx]
  have e2 : d% (fun y => d% (fun z => ⟪Z z, Z z⟫) y (X y)) x (Y x)
      = (⟪cov (fun y => cov Z y (X y)) x (Y x), Z x⟫
           + ⟪cov Z x (X x), cov Z x (Y x)⟫)
        + (⟪cov Z x (Y x), cov Z x (X x)⟫
           + ⟪Z x, cov (fun y => cov Z y (X y)) x (Y x)⟫) := by
    rw [hdf X, mvfderiv_add (MDifferentiableAt.inner_bundle (E := TangentSpace I)
       (F := E) hBx (hZm x))
       (MDifferentiableAt.inner_bundle (E := TangentSpace I)
       (F := E) (hZm x) hBx), add_apply,
      hcov.mvfderiv_inner_eq Y hBx (hZm x),
      hcov.mvfderiv_inner_eq Y (hZm x) hBx]
  have ebr : d% (fun z => ⟪Z z, Z z⟫) x (mlieBracket I X Y x)
      = ⟪cov Z x (mlieBracket I X Y x), Z x⟫
          + ⟪Z x, cov Z x (mlieBracket I X Y x)⟫ :=
    hcov.mvfderiv_inner_eq (mlieBracket I X Y) (hZm x) (hZm x)
  have hsym := VectorField.mlieBracket_apply_fun
    (f := fun y => ⟪Z y, Z y⟫) hfC2 hX hY
  have c1 : ⟪Z x, cov (fun y => cov Z y (Y y)) x (X x)⟫
      = ⟪cov (fun y => cov Z y (Y y)) x (X x), Z x⟫ := real_inner_comm _ _
  have c2 : ⟪Z x, cov (fun y => cov Z y (X y)) x (Y x)⟫
      = ⟪cov (fun y => cov Z y (X y)) x (Y x), Z x⟫ := real_inner_comm _ _
  have c3 : ⟪cov Z x (Y x), cov Z x (X x)⟫
      = ⟪cov Z x (X x), cov Z x (Y x)⟫ := real_inner_comm _ _
  have c4 : ⟪Z x, cov Z x (mlieBracket I X Y x)⟫
      = ⟪cov Z x (mlieBracket I X Y x), Z x⟫ := real_inner_comm _ _
  simp only [curvature, inner_sub_left]
  linarith

/-- Polarization of the self-pairing zero identity. -/
theorem inner_curvature_right_skew_bridge
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 2 (T% W)) :
    ⟪cov.curvature X Y Z x, W x⟫ =
      -⟪cov.curvature X Y W x, Z x⟫ := by
  have h0 := cov.inner_curvature_self_right_bridge
    hmetric hX hY (hZ.add_section hW)
  rw [cov.curvature_add_right hZ hW hX hY] at h0
  have hz := cov.inner_curvature_self_right_bridge hmetric hX hY hZ
  have hw := cov.inner_curvature_self_right_bridge hmetric hX hY hW
  simp only [Pi.add_apply, inner_add_left, inner_add_right] at h0
  linarith [real_inner_comm (cov.curvature X Y Z x) (W x),
    real_inner_comm (cov.curvature X Y W x) (Z x)]

/-- Algebraic first Bianchi projected into the Riemann metric. -/
theorem inner_first_bianchi_bridge
    (htor : cov.torsion = 0)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hZ : CMDiff 2 (T% Z)) (w : TangentSpace I x) :
    ⟪cov.curvature X Y Z x, w⟫ +
      ⟪cov.curvature Y Z X x, w⟫ +
      ⟪cov.curvature Z X Y x, w⟫ = 0 := by
  have h := cov.bianchi_first (x := x) htor hX hY hZ
  have e : ⟪cov.curvature X Y Z x
        + cov.curvature Y Z X x + cov.curvature Z X Y x, w⟫ =
      ⟪cov.curvature X Y Z x, w⟫ +
      ⟪cov.curvature Y Z X x, w⟫ +
      ⟪cov.curvature Z X Y x, w⟫ := by
    rw [inner_add_left, inner_add_left]
  rw [← e, h, inner_zero_left]

theorem inner_curvature_left_skew_bridge
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (w : TangentSpace I x) :
    ⟪cov.curvature X Y Z x, w⟫ =
      -⟪cov.curvature Y X Z x, w⟫ := by
  rw [cov.curvature_antisymm X Y Z x, inner_neg_left]

/-- Riemann pair symmetry from 4 algebraic Bianchi relations
and the two skew symmetries. -/
theorem inner_curvature_pair_symm_bridge
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hY : CMDiff 2 (T% Y))
    (hZ : CMDiff 2 (T% Z)) (hW : CMDiff 2 (T% W)) :
    ⟪cov.curvature X Y Z x, W x⟫ =
      ⟪cov.curvature Z W X x, Y x⟫ := by
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have mX : MDiffAt (T% X) x := (hX.mdifferentiable h2) x
  have mY : MDiffAt (T% Y) x := (hY.mdifferentiable h2) x
  have mZ : MDiffAt (T% Z) x := (hZ.mdifferentiable h2) x
  have mW : MDiffAt (T% W) x := (hW.mdifferentiable h2) x
  have b1 := cov.inner_first_bianchi_bridge htor hX hY hZ (W x)
  have b2 := cov.inner_first_bianchi_bridge htor hY hZ hW (X x)
  have b3 := cov.inner_first_bianchi_bridge htor hZ hW hX (Y x)
  have b4 := cov.inner_first_bianchi_bridge htor hW hX hY (Z x)
  have l1 : ⟪cov.curvature Y Z X x, W x⟫ =
      -⟪cov.curvature Y Z W x, X x⟫ :=
    cov.inner_curvature_right_skew_bridge hmet mY mZ hX hW
  have l2 : ⟪cov.curvature Z X Y x, W x⟫ =
      -⟪cov.curvature Z X W x, Y x⟫ :=
    cov.inner_curvature_right_skew_bridge hmet mZ mX hY hW
  have l2' : ⟪cov.curvature Z X W x, Y x⟫ =
      -⟪cov.curvature X Z W x, Y x⟫ :=
    cov.inner_curvature_left_skew_bridge (Y x)
  have l3 : ⟪cov.curvature Z W Y x, X x⟫ =
      -⟪cov.curvature Z W X x, Y x⟫ :=
    cov.inner_curvature_right_skew_bridge hmet mZ mW hY hX
  have l4 : ⟪cov.curvature W Y Z x, X x⟫ =
      -⟪cov.curvature W Y X x, Z x⟫ :=
    cov.inner_curvature_right_skew_bridge hmet mW mY hZ hX
  have l4' : ⟪cov.curvature W Y X x, Z x⟫ =
      -⟪cov.curvature Y W X x, Z x⟫ :=
    cov.inner_curvature_left_skew_bridge (Z x)
  have l5 : ⟪cov.curvature W X Z x, Y x⟫ =
      -⟪cov.curvature W X Y x, Z x⟫ :=
    cov.inner_curvature_right_skew_bridge hmet mW mX hZ hY
  have l6 : ⟪cov.curvature X Y W x, Z x⟫ =
      -⟪cov.curvature X Y Z x, W x⟫ :=
    cov.inner_curvature_right_skew_bridge hmet mX mY hW hZ
  linarith

/-- Expand the covariant Riemann derivative via metric compatibility,
following the upstream Divergence pair symmetry argument. -/
theorem inner_covCurvature_expand_bridge
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X A B C D : Π y : M, TangentSpace I y} {x : M}
    (hA : CMDiff 2 (T% A)) (hB : CMDiff 2 (T% B))
    (hC : CMDiff 3 (T% C)) (hD : CMDiff 2 (T% D)) :
    ⟪cov.covCurvature X A B C x, D x⟫ =
      mvfderiv I (fun y => ⟪cov.curvature A B C y, D y⟫) x (X x) -
      ⟪cov.curvature (fun y => cov A y (X y)) B C x, D x⟫ -
      ⟪cov.curvature A (fun y => cov B y (X y)) C x, D x⟫ -
      ⟪cov.curvature A B (fun y => cov C y (X y)) x, D x⟫ -
      ⟪cov.curvature A B C x, cov D x (X x)⟫ := by
  have h1 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  have h2 : (2 : ℕ∞ω) ≠ 0 := by norm_num
  have hcs : MDiffAt (T% (fun y => cov.curvature A B C y)) x :=
    ((cov.contMDiff_curvature_bridge hA hB hC).mdifferentiable h1) x
  have hlead := hmet.mvfderiv_inner_eq (V := fun y : M => TangentSpace I y) X
    hcs ((hD.mdifferentiable h2) x)
  show ⟪cov (fun y => cov.curvature A B C y) x (X x) -
      cov.curvature (fun y => cov A y (X y)) B C x -
      cov.curvature A (fun y => cov B y (X y)) C x -
      cov.curvature A B (fun y => cov C y (X y)) x, D x⟫ = _
  rw [inner_sub_left, inner_sub_left, inner_sub_left, hlead]
  ring

/-- Actual pair exchange of the covariant Riemann tensor. -/
theorem inner_covCurvature_pair_symm_bridge
    (hmet : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htor : cov.torsion = 0)
    {X A B C D : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiff 2 (T% X)) (hA : CMDiff 3 (T% A))
    (hB : CMDiff 3 (T% B)) (hC : CMDiff 3 (T% C))
    (hD : CMDiff 3 (T% D)) :
    ⟪cov.covCurvature X A B C x, D x⟫ =
      ⟪cov.covCurvature X C D A x, B x⟫ := by
  have hA2 : CMDiff 2 (T% A) := hA.of_le (by norm_num)
  have hB2 : CMDiff 2 (T% B) := hB.of_le (by norm_num)
  have hC2 : CMDiff 2 (T% C) := hC.of_le (by norm_num)
  have hD2 : CMDiff 2 (T% D) := hD.of_le (by norm_num)
  have hDA : CMDiff 2 (T% (fun y => cov A y (X y))) :=
    cov.contMDiff_cov_apply hA hX
  have hDB : CMDiff 2 (T% (fun y => cov B y (X y))) :=
    cov.contMDiff_cov_apply hB hX
  have hDC : CMDiff 2 (T% (fun y => cov C y (X y))) :=
    cov.contMDiff_cov_apply hC hX
  have hDD : CMDiff 2 (T% (fun y => cov D y (X y))) :=
    cov.contMDiff_cov_apply hD hX
  have hfun : (fun y => ⟪cov.curvature A B C y, D y⟫) =
      (fun y => ⟪cov.curvature C D A y, B y⟫) := by
    funext y
    exact cov.inner_curvature_pair_symm_bridge hmet htor hA2 hB2 hC2 hD2
  rw [cov.inner_covCurvature_expand_bridge hmet hA2 hB2 hC hD2,
      cov.inner_covCurvature_expand_bridge hmet hC2 hD2 hA hB2, hfun,
      cov.inner_curvature_pair_symm_bridge
        (X := fun y => cov A y (X y)) hmet htor hDA hB2 hC2 hD2,
      cov.inner_curvature_pair_symm_bridge
        (X := A) (Y := fun y => cov B y (X y)) hmet htor hA2 hDB hC2 hD2,
      cov.inner_curvature_pair_symm_bridge
        (Z := fun y => cov C y (X y)) hmet htor hA2 hB2 hDC hD2,
      cov.inner_curvature_pair_symm_bridge
        (W := fun y => cov D y (X y)) hmet htor hA2 hB2 hC2 hDD]
  ring

end CovariantDerivative

namespace SmoothCurvatureDualFrame

open SmoothCurvatureRealFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 3 E (fun x : M => TangentSpace I x)]

/-- Swap the endomorphism input/output indices of the real frame tensor.
In this order the classical Riemann pair-exchange is a literal swap. -/
noncomputable def dualFrameDerivative {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M) : Deriv n :=
  fun e a b c d => frameDerivative I M fr x e b a c d

theorem dual_frame_bianchi {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) :
    SecondBianchi (dualFrameDerivative I M fr x) := by
  intro e a b c d
  exact actual_frame_second_bianchi I M fr x hfr e b a c d

theorem dual_frame_skew {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) :
    SkewLast (dualFrameDerivative I M fr x) := by
  intro e a b c d
  exact actual_frame_skew_last I M fr x hfr e b a c d

/-- The previously assumed hEx is now PROVED for the actual LC tensor. -/
theorem dual_frame_pair_exchange {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M)
    (hfr : ∀ i, CMDiff 3 (T% (fr i))) :
    PairExchange (dualFrameDerivative I M fr x) := by
  intro e a b c d
  letI : IsContMDiffRiemannianBundle I 1 E
      (fun y : M => TangentSpace I y) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  letI : IsContMDiffRiemannianBundle I 2 E
      (fun y : M => TangentSpace I y) :=
    IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.leviCivitaConnection I M) 1 :=
    SmoothMetricBianchi.levi_civita_C1 I M
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.leviCivitaConnection I M) 2 :=
    SmoothMetricBianchi.levi_civita_C2 I M
  have h2 (i : Fin n) : CMDiff 2 (T% (fr i)) :=
    (hfr i).of_le (by norm_num)
  have hmet : (CovariantDerivative.leviCivitaConnection I M).IsMetricCompatible
      (M := M) (V := TangentSpace I) :=
    CovariantDerivative.isMetricCompatible_leviCivitaConnection I
  have htor : (CovariantDerivative.leviCivitaConnection I M).torsion = 0 :=
    CovariantDerivative.torsion_leviCivitaConnection_eq_zero I
  have hpair :=
    (CovariantDerivative.leviCivitaConnection I M).inner_covCurvature_pair_symm_bridge
      (x := x) hmet htor (h2 e) (hfr c) (hfr d) (hfr a) (hfr b)
  simpa [dualFrameDerivative, frameDerivative] using hpair

/-- No pair-exchange hypothesis. The only remaining analytic
assumption is the vanishing of the true derivative of the Ricci trace
in the chosen frame. -/
theorem dual_frame_yang_mills_of_parallel_ricci {n : ℕ}
    (fr : Fin n → Π y : M, TangentSpace I y) (x : M)
    (hfr : ∀ i, CMDiff 3 (T% (fr i)))
    (hParallel : ∀ e b d, RicciDerivative
        (dualFrameDerivative I M fr x) e b d = 0) :
    ∀ a b d, YangMillsDivergence
      (dualFrameDerivative I M fr x) a b d = 0 := by
  intro a b d
  rw [yang_mills_eq_ricci_derivatives_real
    (dualFrameDerivative I M fr x)
    (dual_frame_bianchi I M fr x hfr)
    (dual_frame_skew I M fr x hfr)
    (dual_frame_pair_exchange I M fr x hfr)]
  rw [hParallel a d b, hParallel b d a]
  ring

end SmoothCurvatureDualFrame
