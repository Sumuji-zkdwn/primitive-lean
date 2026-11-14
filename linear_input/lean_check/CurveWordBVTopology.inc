/-!
Compact signature ranges, shuffle density, and continuous one-forms for actual
continuous-BV Stieltjes signatures. These are analytic ingredients and do not
assert the geometric Hambly--Lyons tree-factorization conclusion.
-/

noncomputable section
namespace LinearInputCurveWordBVTopology
open Set MeasureTheory
open LinearInputCurveWordStieltjes LinearInputCurveWordBVSignature LinearInputCurveWordBVShuffle
open LinearInputCurveWordChen LinearInputCurveWordSignatureTopology

section LineFunctional
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
variable {γ : ℝ → X} (hγ : Continuous γ) {d : ℝ → ℝ} (hd : Continuous d) (a b : ℝ)

def measureLineLinear : C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ t in a..b, f (γ t) * d t ∂μ
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_mul]
    exact intervalIntegral.integral_add ((f.continuous.comp hγ).mul hd |>.intervalIntegrable a b)
      ((g.continuous.comp hγ).mul hd |>.intervalIntegrable a b)
  map_smul' r f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact intervalIntegral.integral_const_mul r _

theorem measureLineLinear_bound (hab : a ≤ b) (f : C(X, ℝ)) :
    ‖measureLineLinear μ hγ hd a b f‖ ≤ (∫ t in a..b, ‖d t‖ ∂μ) * ‖f‖ := by
  change ‖∫ t in a..b, f (γ t) * d t ∂μ‖ ≤ _
  calc
    _ ≤ ∫ t in a..b, ‖f (γ t) * d t‖ ∂μ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, ‖f‖ * ‖d t‖ ∂μ := by
      apply intervalIntegral.integral_mono_on hab
        (((f.continuous.comp hγ).mul hd).norm.intervalIntegrable a b)
        ((continuous_const.mul hd.norm).intervalIntegrable a b)
      intro t _
      change ‖f (γ t) * d t‖ ≤ ‖f‖ * ‖d t‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm (γ t)) (norm_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, mul_comm]

def measureLineFunctional (hab : a ≤ b) : C(X, ℝ) →L[ℝ] ℝ :=
  (measureLineLinear μ hγ hd a b).mkContinuous (∫ t in a..b, ‖d t‖ ∂μ)
    (measureLineLinear_bound μ hγ hd a b hab)

omit μ [IsLocallyFiniteMeasure μ] in
def stieltjesLineFunctional (p m : StieltjesFunction ℝ) (hab : a ≤ b) : C(X, ℝ) →L[ℝ] ℝ :=
  measureLineFunctional p.measure hγ hd a b hab - measureLineFunctional m.measure hγ hd a b hab

omit μ [IsLocallyFiniteMeasure μ] in
theorem stieltjesLineFunctional_apply (p m : StieltjesFunction ℝ) (hab : a ≤ b) (f : C(X, ℝ)) :
    stieltjesLineFunctional hγ hd a b p m hab f =
      stieltjesIntegral p m a b (fun t => f (γ t) * d t) := rfl

omit μ [IsLocallyFiniteMeasure μ] in
theorem stieltjesLineFunctional_bound (p m : StieltjesFunction ℝ) (hab : a ≤ b) (f : C(X, ℝ)) :
    ‖stieltjesLineFunctional hγ hd a b p m hab f‖ ≤
      ((∫ t in a..b, ‖d t‖ ∂p.measure) + (∫ t in a..b, ‖d t‖ ∂m.measure)) * ‖f‖ := by
  change ‖measureLineLinear p.measure hγ hd a b f - measureLineLinear m.measure hγ hd a b f‖ ≤ _
  calc
    _ ≤ ‖measureLineLinear p.measure hγ hd a b f‖ + ‖measureLineLinear m.measure hγ hd a b f‖ :=
      norm_sub_le _ _
    _ ≤ (∫ t in a..b, ‖d t‖ ∂p.measure) * ‖f‖ + (∫ t in a..b, ‖d t‖ ∂m.measure) * ‖f‖ :=
      add_le_add (measureLineLinear_bound p.measure hγ hd a b hab f)
        (measureLineLinear_bound m.measure hγ hd a b hab f)
    _ = _ := by ring

end LineFunctional

def signatureRange {ι : Type*} (p m : ι → StieltjesFunction ℝ) (a b : ℝ) : Set (List ι → ℝ) :=
  Set.range (fun t : Icc a b => stieltjesSignature p m a t.val)

theorem signature_lift_continuous {ι : Type*} {p m : ι → StieltjesFunction ℝ}
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ)) (a : ℝ) : Continuous (fun t => stieltjesSignature p m a t) := by
  apply continuous_pi
  intro w
  exact reverseStieltjes_continuous p m hp hm a w.reverse

def signaturePoint {ι : Type*} (p m : ι → StieltjesFunction ℝ) (a b : ℝ) (hab : a ≤ b)
    (t : ℝ) : signatureRange p m a b :=
  ⟨stieltjesSignature p m a (projIcc a b hab t).val, ⟨projIcc a b hab t, rfl⟩⟩

theorem signaturePoint_continuous {ι : Type*} {p m : ι → StieltjesFunction ℝ}
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ)) (a b : ℝ) (hab : a ≤ b) :
    Continuous (signaturePoint p m a b hab) := by
  exact ((signature_lift_continuous hp hm a).comp
    (continuous_subtype_val.comp continuous_projIcc)).subtype_mk _

theorem signatureRange_isCompact {ι : Type*} {p m : ι → StieltjesFunction ℝ}
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ)) (a b : ℝ) : IsCompact (signatureRange p m a b) := by
  exact isCompact_range ((signature_lift_continuous hp hm a).comp continuous_subtype_val)

def coordinate {ι : Type*} (p m : ι → StieltjesFunction ℝ) (a b : ℝ) (w : List ι) :
    C(signatureRange p m a b, ℝ) :=
  ⟨fun x => x.val w, (continuous_apply w).comp continuous_subtype_val⟩

theorem coordinate_empty {ι : Type*} (p m : ι → StieltjesFunction ℝ) (a b : ℝ) :
    coordinate p m a b [] = 1 := by
  ext x
  obtain ⟨t, ht⟩ := x.property
  change x.val [] = 1
  rw [← ht]
  exact show stieltjesSignature p m a t.val [] = 1 from rfl

theorem coordinate_shuffle {ι : Type*} {p m : ι → StieltjesFunction ℝ}
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ)) (a b : ℝ) (u w : List ι) :
    coordinate p m a b u * coordinate p m a b w =
      ((chronologicalShuffles u w).map (coordinate p m a b)).sum := by
  ext x
  obtain ⟨t, ht⟩ := x.property
  have he (l : List (List ι)) : ((l.map (coordinate p m a b)).sum) x = (l.map x.val).sum := by
    induction l with
    | nil => simp
    | cons z l ih => simpa only [List.map_cons, List.sum_cons, ContinuousMap.add_apply,
        coordinate, ContinuousMap.coe_mk] using congrArg (fun r => x.val z + r) ih
  simp only [ContinuousMap.mul_apply, he]
  change x.val u * x.val w = ((chronologicalShuffles u w).map x.val).sum
  rw [← ht]
  exact stieltjesSignature_shuffle p m hp hm a t.val t.property.1 u w

/-- Every continuous function on the actual signature range is uniformly
approximable by finite linear combinations of word coordinates. -/
theorem signature_coordinates_dense {ι : Type*} {p m : ι → StieltjesFunction ℝ}
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ)) (a b : ℝ) :
    letI : CompactSpace (signatureRange p m a b) :=
      isCompact_iff_compactSpace.mp (signatureRange_isCompact hp hm a b)
    (coordinateAlgebra (coordinate p m a b) (coordinate_empty p m a b)
      (coordinate_shuffle hp hm a b)).topologicalClosure = ⊤ := by
  let : CompactSpace (signatureRange p m a b) :=
    isCompact_iff_compactSpace.mp (signatureRange_isCompact hp hm a b)
  apply coordinates_dense
  intro x y hxy
  by_contra! h
  apply hxy
  apply Subtype.ext
  exact funext h


theorem integral_coordinate_against_coordinate {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (hab : a ≤ b) (u w : List ι) (i : ι) :
    stieltjesIntegral (p i) (m i) a b
        (fun t => reverseStieltjes p m a u t * reverseStieltjes p m a w t) =
      ((shuffles u w).map (fun z => reverseStieltjes p m a (i :: z) b)).sum := by
  rw [sum_reverseStieltjes_cons p m hp hm]
  apply stieltjesIntegral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact reverseStieltjes_shuffle p m hp hm a t ht.1 u w

theorem coordinate_one_form_zero_of_trivial_signature {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (hab : a ≤ b)
    (hzero : ∀ w : List ι, w ≠ [] → stieltjesSignature p m a b w = 0)
    (u w : List ι) (i : ι) :
    stieltjesIntegral (p i) (m i) a b
      (fun t => reverseStieltjes p m a u t * reverseStieltjes p m a w t) = 0 := by
  rw [integral_coordinate_against_coordinate p m hp hm a b hab]
  have hrev (z : List ι) : reverseStieltjes p m a (i :: z) b = 0 := by
    have hz := hzero (i :: z).reverse (by simp)
    simpa only [stieltjesSignature, List.reverse_reverse] using hz
  simp [hrev]

/-- Trivial total BV signature annihilates every continuous coefficient
one-form on its full signature range. Integration here is genuinely against
the positive and negative Stieltjes measures of the original coordinates. -/
theorem continuous_one_form_zero_of_trivial_signature {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (hab : a ≤ b)
    (hzero : ∀ w : List ι, w ≠ [] → stieltjesSignature p m a b w = 0)
    (f : C(signatureRange p m a b, ℝ)) (w : List ι) (i : ι) :
    stieltjesIntegral (p i) (m i) a b
      (fun t => f (signaturePoint p m a b hab t) * reverseStieltjes p m a w t) = 0 := by
  let : CompactSpace (signatureRange p m a b) :=
    isCompact_iff_compactSpace.mp (signatureRange_isCompact hp hm a b)
  let L := stieltjesLineFunctional (signaturePoint_continuous hp hm a b hab)
    (reverseStieltjes_continuous p m hp hm a w) a b (p i) (m i) hab
  have hz (u : List ι) : L (coordinate p m a b u) = 0 := by
    change stieltjesIntegral (p i) (m i) a b
      (fun t => coordinate p m a b u (signaturePoint p m a b hab t) * reverseStieltjes p m a w t) = 0
    rw [← coordinate_one_form_zero_of_trivial_signature p m hp hm a b hab hzero u.reverse w i]
    apply stieltjesIntegral_congr
    intro t ht
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    simp only [coordinate, ContinuousMap.coe_mk, signaturePoint, projIcc_of_mem hab ht', stieltjesSignature]
  exact functional_zero_of_coordinates (coordinate p m a b) (coordinate_empty p m a b)
    (coordinate_shuffle hp hm a b) (fun x y hxy => by
      by_contra! h
      exact hxy (Subtype.ext (funext h))) L hz f

end LinearInputCurveWordBVTopology
