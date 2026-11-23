import Mathlib.MeasureTheory.Integral.Prod

/-!
Normalized restrictions of the factor measures to two balls are probability measures.
The following tensorization theorem is for arbitrary probability measures and arbitrary
integrable real functions. Its two terms are exactly the mean oscillations of slices.
-/

open MeasureTheory
open scoped ENNReal

namespace SandpileLaakso.ProductPI

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The L¹ deviation from the mean, using a probability measure. -/
noncomputable def oscillation {A : Type*} [MeasurableSpace A] (P : Measure A)
    (f : A → ℝ) : ℝ :=
  ∫ x, ‖f x - ∫ y, f y ∂P‖ ∂P

/-- The product mean oscillation is bounded with constant one by the sum of the
two averaged directional oscillations. The only function hypothesis is integrability. -/
theorem product_oscillation_le (f : X × Y → ℝ) (hf : Integrable f (μ.prod ν)) :
    oscillation (μ.prod ν) f ≤
      (∫ x, oscillation ν (fun y => f (x, y)) ∂μ) +
      ∫ y, oscillation μ (fun x => f (x, y)) ∂ν := by
  let row (x : X) := ∫ y, f (x, y) ∂ν
  let col (y : Y) := ∫ x, f (x, y) ∂μ
  let c := ∫ z, f z ∂μ.prod ν
  have hr : Integrable row μ := hf.integral_prod_left
  have hc : Integrable col ν := hf.integral_prod_right
  have he : c = ∫ y, col y ∂ν := integral_prod_symm _ hf
  have hv : Integrable (fun z : X × Y => f z - row z.1) (μ.prod ν) :=
    hf.sub (hr.comp_fst ν)
  have hh : Integrable (fun z : X × Y => f z - col z.2) (μ.prod ν) :=
    hf.sub (hc.comp_snd μ)
  have ht : Integrable (fun x : X => row x - c) μ := hr.sub (integrable_const c)
  have hs : (∫ x, ‖row x - c‖ ∂μ) ≤ ∫ z, ‖f z - col z.2‖ ∂μ.prod ν := by
    rw [integral_prod _ hh.norm]
    apply integral_mono_ae ht.norm hh.integral_norm_prod_left
    filter_upwards [hf.prod_right_ae] with x hx
    change ‖(∫ y, f (x, y) ∂ν) - c‖ ≤ ∫ y, ‖f (x, y) - col y‖ ∂ν
    rw [he, ← integral_sub hx hc]
    exact norm_integral_le_integral_norm _
  change (∫ z, ‖f z - c‖ ∂μ.prod ν) ≤ _
  calc
    _ ≤ ∫ z, (‖f z - row z.1‖ + ‖row z.1 - c‖) ∂μ.prod ν := by
      apply integral_mono (hf.sub (integrable_const c)).norm
        (hv.norm.add (ht.norm.comp_fst ν))
      intro z
      calc
        ‖f z - c‖ = ‖(f z - row z.1) + (row z.1 - c)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    _ = (∫ z, ‖f z - row z.1‖ ∂μ.prod ν) + ∫ x, ‖row x - c‖ ∂μ := by
      rw [integral_add hv.norm (ht.norm.comp_fst ν)]
      congr 1
      simpa using integral_fun_fst (μ := μ) (ν := ν) (fun x => ‖row x - c‖)
    _ ≤ (∫ z, ‖f z - row z.1‖ ∂μ.prod ν) + ∫ z, ‖f z - col z.2‖ ∂μ.prod ν :=
      add_le_add_right hs _
    _ = _ := by
      rw [integral_prod _ hv.norm, integral_prod_symm _ hh.norm]
      rfl

/-- Testing a property on functions pulled back from the first factor preserves
the exact oscillation. This is the necessity direction for the product. -/
theorem pullback_oscillation (f : X → ℝ) :
    oscillation (μ.prod ν) (fun z => f z.1) = oscillation μ f := by
  unfold oscillation
  simp only [integral_fun_fst, probReal_univ, one_smul]
  simpa using integral_fun_fst (μ := μ) (ν := ν) (fun x => ‖f x - ∫ y, f y ∂μ‖)

/-- Integrating a sectional estimate over a smaller normalized ball costs at most
the given ratio of volumes of the larger and smaller balls. -/
private theorem integrate_section {A : Type*} [MeasurableSpace A]
    {small large : Measure A} (D : NNReal) (K : ℝ) (hK : 0 ≤ K)
    (hdom : small ≤ D • large) {o g : A → ℝ}
    (ho : Integrable o small) (hg : Integrable g large) (hpos : ∀ x, 0 ≤ g x)
    (h : ∀ᵐ x ∂small, o x ≤ K * g x) :
    (∫ x, o x ∂small) ≤ (K * D) * ∫ x, g x ∂large := by
  have hD : Integrable g (D • large) := hg.smul_measure_nnreal
  have hcomp := integral_mono_measure hdom (Filter.Eventually.of_forall hpos) hD
  calc
    _ ≤ ∫ x, K * g x ∂small := integral_mono_ae ho ((hD.mono_measure hdom).const_mul K) h
    _ = K * ∫ x, g x ∂small := integral_const_mul _ _
    _ ≤ K * ∫ x, g x ∂(D • large) := mul_le_mul_of_nonneg_left hcomp hK
    _ = _ := by
      rw [integral_smul_nnreal_measure]
      change K * ((D : ℝ) * _) = (K * (D : ℝ)) * _
      rw [mul_assoc]

/-- Rectangular version of weak L¹ Poincaré tensorization. The four measures are
the normalized restrictions to the factor balls and their dilates. Dilation may
be different in the two factors. The sectional hypotheses are the factor PI
estimates applied to slices of the function and upper gradient. -/
theorem product_of_slice_PI
    (μ' : Measure X) (ν' : Measure Y) [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (DX DY : NNReal) (KX KY : ℝ) (hKX : 0 ≤ KX) (hKY : 0 ≤ KY)
    (hdomX : μ ≤ DX • μ') (hdomY : ν ≤ DY • ν') (f g : X × Y → ℝ)
    (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ'.prod ν')) (hn : ∀ z, 0 ≤ g z)
    (hY : ∀ᵐ x ∂μ, oscillation ν (fun y => f (x,y)) ≤ KY * ∫ y, g (x,y) ∂ν')
    (hX : ∀ᵐ y ∂ν, oscillation μ (fun x => f (x,y)) ≤ KX * ∫ x, g (x,y) ∂μ') :
    oscillation (μ.prod ν) f ≤ (KY * DX + KX * DY) * ∫ z, g z ∂(μ'.prod ν') := by
  have v := (hf.sub (hf.integral_prod_left.comp_fst ν)).integral_norm_prod_left
  have h := (hf.sub (hf.integral_prod_right.comp_snd μ)).integral_norm_prod_right
  have A := integrate_section DX KY hKY hdomX v hg.integral_prod_left
    (fun x => integral_nonneg (fun y => hn (x,y))) hY
  have B := integrate_section DY KX hKX hdomY h hg.integral_prod_right
    (fun y => integral_nonneg (fun x => hn (x,y))) hX
  rw [← integral_prod _ hg] at A
  rw [← integral_prod_symm _ hg] at B
  rw [add_mul]
  exact (product_oscillation_le μ ν f hf).trans (add_le_add A B)

#print axioms product_oscillation_le
#print axioms pullback_oscillation
#print axioms product_of_slice_PI

end SandpileLaakso.ProductPI
