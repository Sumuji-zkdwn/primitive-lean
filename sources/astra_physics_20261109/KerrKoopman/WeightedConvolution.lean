import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Actual all-mode product for the analytic construction.
An actual absolutely convergent convolution in l1 of a Banach algebra,
assembled from single-mode interactions. The kernel is allowed to depend
on both input modes; a continuous shrinking-strip kernel is instantiated below.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal

namespace KerrKoopman.Phase3WeightedConvolution

abbrev L1 (A : Type*) [NormedAddCommGroup A] := lp (fun _ : ℤ => A) 1

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem l1_summable_norm (u : L1 A) : Summable (fun k => ‖u k‖) := by
  simpa using u.2.summable

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem l1_norm_eq_tsum (u : L1 A) : ‖u‖ = ∑' k, ‖u k‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := 1) (by norm_num) u

def interaction (w : ℤ → ℤ → A) (u v : L1 A) (p : ℤ × ℤ) : L1 A :=
  lp.single 1 (p.1 + p.2) (w p.1 p.2 * (u p.1 * v p.2))

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem interaction_norm_le (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (u v : L1 A) (p : ℤ × ℤ) :
    ‖interaction w u v p‖ ≤ ‖u p.1‖ * ‖v p.2‖ := by
  rw [interaction, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  calc
    ‖w p.1 p.2 * (u p.1 * v p.2)‖ ≤ ‖w p.1 p.2‖ * ‖u p.1 * v p.2‖ := norm_mul_le _ _
    _ ≤ ‖w p.1 p.2‖ * (‖u p.1‖ * ‖v p.2‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖u p.1‖ * ‖v p.2‖) :=
      mul_le_mul_of_nonneg_right (hw _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖u p.1‖ * ‖v p.2‖ := one_mul _

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem summable_norm_product (u v : L1 A) :
    Summable (fun p : ℤ × ℤ => ‖u p.1‖ * ‖v p.2‖) :=
  (l1_summable_norm u).mul_of_nonneg (l1_summable_norm v)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem summable_norm_interaction (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (u v : L1 A) : Summable (fun p => ‖interaction w u v p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (interaction_norm_le w hw u v) (summable_norm_product u v)

omit [NormedAlgebra ℂ A] in
theorem summable_interaction (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (u v : L1 A) : Summable (interaction w u v) :=
  (summable_norm_interaction w hw u v).of_norm

/-- The full infinite convolution is a sum in the complete l1 Banach space. -/
def product (w : ℤ → ℤ → A) (u v : L1 A) : L1 A := ∑' p, interaction w u v p

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem product_norm_le (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (u v : L1 A) : ‖product w u v‖ ≤ ‖u‖ * ‖v‖ := by
  calc
    ‖product w u v‖ ≤ ∑' p, ‖interaction w u v p‖ :=
      norm_tsum_le_tsum_norm (summable_norm_interaction w hw u v)
    _ ≤ ∑' p : ℤ × ℤ, ‖u p.1‖ * ‖v p.2‖ :=
      Summable.tsum_le_tsum (interaction_norm_le w hw u v)
        (summable_norm_interaction w hw u v) (summable_norm_product u v)
    _ = (∑' k, ‖u k‖) * ∑' l, ‖v l‖ :=
      ((l1_summable_norm u).tsum_mul_tsum (l1_summable_norm v)
        (summable_norm_product u v)).symm
    _ = ‖u‖ * ‖v‖ := by rw [← l1_norm_eq_tsum, ← l1_norm_eq_tsum]

omit [NormedAlgebra ℂ A] in
theorem product_add_left (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (u v z : L1 A) : product w (u + v) z = product w u z + product w v z := by
  unfold product
  rw [← (summable_interaction w hw u z).tsum_add (summable_interaction w hw v z)]
  apply tsum_congr
  intro p
  simp only [interaction, lp.coeFn_add, Pi.add_apply, add_mul, mul_add, lp.single_add]

omit [NormedAlgebra ℂ A] in
theorem product_add_right (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (u v z : L1 A) : product w u (v + z) = product w u v + product w u z := by
  unfold product
  rw [← (summable_interaction w hw u v).tsum_add (summable_interaction w hw u z)]
  apply tsum_congr
  intro p
  simp only [interaction, lp.coeFn_add, Pi.add_apply, mul_add, lp.single_add]

theorem product_smul_left (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (c : ℂ) (u v : L1 A) : product w (c • u) v = c • product w u v := by
  unfold product
  rw [← (summable_interaction w hw u v).tsum_const_smul c]
  apply tsum_congr
  intro p
  simp [interaction, lp.coeFn_smul, lp.single_smul]

theorem product_smul_right (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (c : ℂ) (u v : L1 A) : product w u (c • v) = c • product w u v := by
  unfold product
  rw [← (summable_interaction w hw u v).tsum_const_smul c]
  apply tsum_congr
  intro p
  simp [interaction, lp.coeFn_smul, lp.single_smul]

/-- The genuinely constructed bounded bilinear convolution map. -/
def productCLM (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1) :
    L1 A →L[ℂ] L1 A →L[ℂ] L1 A :=
  (LinearMap.mk₂ ℂ (product w) (product_add_left w hw) (product_smul_left w hw)
    (product_add_right w hw) (product_smul_right w hw)).mkContinuous₂ 1
      (fun u v => by simpa using product_norm_le w hw u v)

theorem productCLM_apply (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (u v : L1 A) : productCLM w hw u v = product w u v := rfl

/-- The same constructed product bundled over the real scalar field. -/
def productRealCLM (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1) :
    L1 A →L[ℝ] L1 A →L[ℝ] L1 A :=
  (LinearMap.mk₂ ℝ (product w) (product_add_left w hw)
    (fun c u v => by simpa only [Complex.coe_smul] using product_smul_left w hw (c : ℂ) u v)
    (product_add_right w hw)
    (fun c u v => by simpa only [Complex.coe_smul] using product_smul_right w hw (c : ℂ) u v)).mkContinuous₂ 1
      (fun u v => by simpa using product_norm_le w hw u v)

theorem productRealCLM_apply (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (u v : L1 A) : productRealCLM w hw u v = product w u v := rfl

theorem productRealCLM_norm_le (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (u v : L1 A) : ‖productRealCLM w hw u v‖ ≤ ‖u‖ * ‖v‖ :=
  product_norm_le w hw u v

section Traces

variable {I : Type*} [TopologicalSpace I] [CompactSpace I]

/-- A continuous moving analytic-width multiplier on a pair of Fourier modes. -/
def twist (ρ : C(I, ℝ)) (k l : ℤ) : C(I, ℂ) :=
  ⟨fun t => (Real.exp (ρ t * (|((k + l : ℤ) : ℝ)| - |(k : ℝ)| - |(l : ℝ)|)) : ℂ),
    by fun_prop⟩

theorem twist_norm_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t) (k l : ℤ) :
    ‖twist ρ k l‖ ≤ 1 := by
  apply (ContinuousMap.norm_le (twist ρ k l) (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro t
  change ‖(Real.exp (ρ t * (|((k + l : ℤ) : ℝ)| - |(k : ℝ)| - |(l : ℝ)|)) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  apply mul_nonpos_of_nonneg_of_nonpos (hρ t)
  have h := abs_add_le (k : ℝ) (l : ℝ)
  push_cast
  linarith

/-- Actual lp(C(I,C)) is complete; no custom weighted-space completeness axiom. -/
example : CompleteSpace (L1 C(I, ℂ)) := inferInstance

def twistedProduct (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t) :
    L1 C(I, ℂ) →L[ℂ] L1 C(I, ℂ) →L[ℂ] L1 C(I, ℂ) :=
  productCLM (twist ρ) (twist_norm_le ρ hρ)

theorem twistedProduct_norm_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u v : L1 C(I, ℂ)) : ‖twistedProduct ρ hρ u v‖ ≤ ‖u‖ * ‖v‖ :=
  product_norm_le (twist ρ) (twist_norm_le ρ hρ) u v

def twistedProductReal (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t) :
    L1 C(I, ℂ) →L[ℝ] L1 C(I, ℂ) →L[ℝ] L1 C(I, ℂ) :=
  productRealCLM (twist ρ) (twist_norm_le ρ hρ)

theorem twistedProductReal_norm_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u v : L1 C(I, ℂ)) : ‖twistedProductReal ρ hρ u v‖ ≤ ‖u‖ * ‖v‖ :=
  product_norm_le (twist ρ) (twist_norm_le ρ hρ) u v

end Traces
end KerrKoopman.Phase3WeightedConvolution
