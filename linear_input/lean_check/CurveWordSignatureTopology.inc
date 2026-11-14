/-!
The signature lift has compact range on a compact time interval. The linear
span of its word coordinates is an algebra (by the actual shuffle identity)
and is uniformly dense in the continuous real functions on that range.
This is a genuine topological ingredient of signature uniqueness, not the
tree-factorization or general bounded-variation uniqueness theorem itself.
-/

noncomputable section

namespace LinearInputCurveWordSignatureTopology
open Set
open LinearInputCurveWordSignature LinearInputCurveWordChen

section Coordinates
variable {ι X : Type*} [TopologicalSpace X]

def coordinateSpan (c : List ι → C(X, ℝ)) : Submodule ℝ C(X, ℝ) :=
  Submodule.span ℝ (Set.range c)

theorem coordinate_mem_span (c : List ι → C(X, ℝ)) (w : List ι) :
    c w ∈ coordinateSpan c := Submodule.subset_span (Set.mem_range_self w)

theorem coordinate_list_sum_mem (c : List ι → C(X, ℝ)) (l : List (List ι)) :
    (l.map c).sum ∈ coordinateSpan c := by
  induction l with
  | nil => exact (coordinateSpan c).zero_mem
  | cons w l ih => simpa using (coordinateSpan c).add_mem (coordinate_mem_span c w) ih

theorem coordinateSpan_mul_mem (c : List ι → C(X, ℝ))
    (hmul : ∀ u w, c u * c w = ((chronologicalShuffles u w).map c).sum)
    {f g : C(X, ℝ)} (hf : f ∈ coordinateSpan c) (hg : g ∈ coordinateSpan c) :
    f * g ∈ coordinateSpan c := by
  induction hf, hg using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    rw [hmul]
    exact coordinate_list_sum_mem c _
  | zero_left => simp only [zero_mul, Submodule.zero_mem]
  | zero_right => simp only [mul_zero, Submodule.zero_mem]
  | add_left x y z _ _ _ hx hy =>
    rw [add_mul]
    exact (coordinateSpan c).add_mem hx hy
  | add_right x y z _ _ _ hx hy =>
    rw [mul_add]
    exact (coordinateSpan c).add_mem hx hy
  | smul_left r x y _ _ h =>
    rw [smul_mul_assoc]
    exact (coordinateSpan c).smul_mem r h
  | smul_right r x y _ _ h =>
    rw [mul_smul_comm]
    exact (coordinateSpan c).smul_mem r h

def coordinateAlgebra (c : List ι → C(X, ℝ)) (hunit : c [] = 1)
    (hmul : ∀ u w, c u * c w = ((chronologicalShuffles u w).map c).sum) :
    Subalgebra ℝ C(X, ℝ) where
  carrier := coordinateSpan c
  zero_mem' := (coordinateSpan c).zero_mem
  add_mem' := (coordinateSpan c).add_mem
  one_mem' := hunit ▸ coordinate_mem_span c []
  mul_mem' := coordinateSpan_mul_mem c hmul
  algebraMap_mem' r := by
    have h := (coordinateSpan c).smul_mem r (coordinate_mem_span c [])
    simpa [hunit, Algebra.smul_def] using h

theorem coordinates_dense [CompactSpace X] (c : List ι → C(X, ℝ))
    (hunit : c [] = 1)
    (hmul : ∀ u w, c u * c w = ((chronologicalShuffles u w).map c).sum)
    (hsep : ∀ x y : X, x ≠ y → ∃ w, c w x ≠ c w y) :
    (coordinateAlgebra c hunit hmul).topologicalClosure = ⊤ := by
  apply ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
  intro x y hxy
  obtain ⟨w, hw⟩ := hsep x y hxy
  exact ⟨(c w : X → ℝ), ⟨c w, coordinate_mem_span c w, rfl⟩, hw⟩

/-- Density transfers vanishing on all word coordinates to any continuous
linear functional, including the line integrals constructed below. -/
theorem functional_zero_of_coordinates [CompactSpace X] (c : List ι → C(X, ℝ))
    (hunit : c [] = 1)
    (hmul : ∀ u w, c u * c w = ((chronologicalShuffles u w).map c).sum)
    (hsep : ∀ x y : X, x ≠ y → ∃ w, c w x ≠ c w y)
    (L : C(X, ℝ) →L[ℝ] ℝ) (hz : ∀ w, L (c w) = 0) : ∀ f, L f = 0 := by
  have hs : (coordinateSpan c : Set C(X, ℝ)) ⊆ {f | L f = 0} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hz w
    | zero => exact map_zero L
    | add x y _ _ hx hy =>
      change L (x + y) = 0
      change L x = 0 at hx
      change L y = 0 at hy
      simp only [map_add, hx, hy, add_zero]
    | smul r x _ hx =>
      change L (r • x) = 0
      change L x = 0 at hx
      simp only [map_smul, hx, smul_zero]
  have hcl := closure_minimal hs (isClosed_eq L.continuous continuous_const)
  have hd := coordinates_dense c hunit hmul hsep
  intro f
  apply hcl
  change f ∈ (coordinateAlgebra c hunit hmul).topologicalClosure
  rw [hd]
  trivial

end Coordinates

section LineFunctional
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable {γ : ℝ → X} (hγ : Continuous γ) {d : ℝ → ℝ} (hd : Continuous d) (a b : ℝ)

def lineIntegralLinear : C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ t in a..b, f (γ t) * d t
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_mul]
    exact intervalIntegral.integral_add ((f.continuous.comp hγ).mul hd |>.intervalIntegrable a b)
      ((g.continuous.comp hγ).mul hd |>.intervalIntegrable a b)
  map_smul' r f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact intervalIntegral.integral_const_mul r _

theorem lineIntegralLinear_bound (hab : a ≤ b) (f : C(X, ℝ)) :
    ‖lineIntegralLinear hγ hd a b f‖ ≤ (∫ t in a..b, ‖d t‖) * ‖f‖ := by
  change ‖∫ t in a..b, f (γ t) * d t‖ ≤ _
  calc
    _ ≤ ∫ t in a..b, ‖f (γ t) * d t‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, ‖f‖ * ‖d t‖ := by
      apply intervalIntegral.integral_mono_on hab
        (((f.continuous.comp hγ).mul hd).norm.intervalIntegrable a b)
        ((continuous_const.mul hd.norm).intervalIntegrable a b)
      intro t _
      change ‖f (γ t) * d t‖ ≤ ‖f‖ * ‖d t‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm (γ t)) (norm_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, mul_comm]

def lineIntegralFunctional (hab : a ≤ b) : C(X, ℝ) →L[ℝ] ℝ :=
  (lineIntegralLinear hγ hd a b).mkContinuous (∫ t in a..b, ‖d t‖)
    (lineIntegralLinear_bound hγ hd a b hab)

theorem lineIntegralFunctional_apply (hab : a ≤ b) (f : C(X, ℝ)) :
    lineIntegralFunctional hγ hd a b hab f = ∫ t in a..b, f (γ t) * d t := rfl

end LineFunctional

def signatureRange {ι : Type*} (v : ι → ℝ → ℝ) (a b : ℝ) : Set (List ι → ℝ) :=
  Set.range (fun t : Icc a b => signature v a t.val)

theorem signature_lift_continuous {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a : ℝ) : Continuous (fun t => signature v a t) := by
  apply continuous_pi
  intro w
  exact reverseIntegral_continuous hv a w.reverse

def signaturePoint {ι : Type*} (v : ι → ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (t : ℝ) : signatureRange v a b :=
  ⟨signature v a (projIcc a b hab t).val, ⟨projIcc a b hab t, rfl⟩⟩

theorem signaturePoint_continuous {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (hab : a ≤ b) :
    Continuous (signaturePoint v a b hab) := by
  exact ((signature_lift_continuous hv a).comp
    (continuous_subtype_val.comp continuous_projIcc)).subtype_mk _

theorem reverseIntegral_deriv_continuous {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a : ℝ) (w : List ι) :
    Continuous (deriv (reverseIntegral v a w)) := by
  cases w with
  | nil =>
    have he : deriv (reverseIntegral v a []) = fun _ => 0 := by
      funext t
      simp [reverseIntegral]
    rw [he]
    exact continuous_const
  | cons i w =>
    have he : deriv (reverseIntegral v a (i :: w)) =
        fun t => reverseIntegral v a w t * v i t := by
      funext t
      exact (reverseIntegral_hasDerivAt hv a t i w).deriv
    rw [he]
    exact (reverseIntegral_continuous hv a w).mul (hv i)

theorem signatureRange_isCompact {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) : IsCompact (signatureRange v a b) := by
  exact isCompact_range ((signature_lift_continuous hv a).comp continuous_subtype_val)

def coordinate {ι : Type*} (v : ι → ℝ → ℝ) (a b : ℝ) (w : List ι) :
    C(signatureRange v a b, ℝ) :=
  ⟨fun x => x.val w, (continuous_apply w).comp continuous_subtype_val⟩

theorem coordinate_empty {ι : Type*} (v : ι → ℝ → ℝ) (a b : ℝ) :
    coordinate v a b [] = 1 := by
  ext x
  obtain ⟨t, ht⟩ := x.property
  change x.val [] = 1
  rw [← ht]
  exact signature_empty v a t.val

theorem coordinate_shuffle {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (u w : List ι) :
    coordinate v a b u * coordinate v a b w =
      ((chronologicalShuffles u w).map (coordinate v a b)).sum := by
  ext x
  obtain ⟨t, ht⟩ := x.property
  have he (l : List (List ι)) : ((l.map (coordinate v a b)).sum) x = (l.map x.val).sum := by
    induction l with
    | nil => simp
    | cons z l ih => simpa only [List.map_cons, List.sum_cons, ContinuousMap.add_apply,
        coordinate, ContinuousMap.coe_mk] using congrArg (fun r => x.val z + r) ih
  simp only [ContinuousMap.mul_apply, he]
  change x.val u * x.val w = ((chronologicalShuffles u w).map x.val).sum
  rw [← ht]
  exact signature_shuffle hv a t.val u w

/-- Every continuous function on the actual signature range is uniformly
approximable by finite linear combinations of word coordinates. -/
theorem signature_coordinates_dense {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) :
    let : CompactSpace (signatureRange v a b) :=
      isCompact_iff_compactSpace.mp (signatureRange_isCompact hv a b)
    (coordinateAlgebra (coordinate v a b) (coordinate_empty v a b)
      (coordinate_shuffle hv a b)).topologicalClosure = ⊤ := by
  let : CompactSpace (signatureRange v a b) :=
    isCompact_iff_compactSpace.mp (signatureRange_isCompact hv a b)
  apply coordinates_dense
  intro x y hxy
  by_contra! h
  apply hxy
  apply Subtype.ext
  exact funext h

/-- An integral of one signature coordinate against the differential of another
is a finite sum of higher signature coordinates, calculated from shuffle. -/
theorem integral_coordinate_against_coordinate {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (u w : List ι) (i : ι) :
    (∫ t in a..b, reverseIntegral v a u t * deriv (reverseIntegral v a (i :: w)) t) =
      ((shuffles u w).map (fun z => reverseIntegral v a (i :: z) b)).sum := by
  have hd : deriv (reverseIntegral v a (i :: w)) =
      fun t => reverseIntegral v a w t * v i t := by
    funext t
    exact (reverseIntegral_hasDerivAt hv a t i w).deriv
  rw [hd, sum_reverseIntegral_cons hv]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← reverseIntegral_shuffle hv]
  ring

/-- Trivial total signature forces these genuine line integrals to vanish.
This is one ingredient of the geometric uniqueness argument. -/
theorem coordinate_one_form_zero_of_trivial_signature {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ)
    (hzero : ∀ w : List ι, w ≠ [] → signature v a b w = 0)
    (u w : List ι) :
    (∫ t in a..b, reverseIntegral v a u t * deriv (reverseIntegral v a w) t) = 0 := by
  cases w with
  | nil => simp [reverseIntegral]
  | cons i w =>
    rw [integral_coordinate_against_coordinate hv]
    have hrev (z : List ι) : reverseIntegral v a (i :: z) b = 0 := by
      have hz := hzero (i :: z).reverse (by simp)
      simpa only [signature, List.reverse_reverse] using hz
    simp [hrev]

/-- Every continuous coefficient on the full signature range has zero line
integral against every signature coordinate when the total signature is
trivial. The passage from word coefficients uses the actual shuffle density
and continuity of integration. -/
theorem continuous_one_form_zero_of_trivial_signature {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (hab : a ≤ b)
    (hzero : ∀ w : List ι, w ≠ [] → signature v a b w = 0)
    (f : C(signatureRange v a b, ℝ)) (w : List ι) :
    (∫ t in a..b, f (signaturePoint v a b hab t) * deriv (reverseIntegral v a w) t) = 0 := by
  let : CompactSpace (signatureRange v a b) :=
    isCompact_iff_compactSpace.mp (signatureRange_isCompact hv a b)
  let L := lineIntegralFunctional (signaturePoint_continuous hv a b hab)
    (reverseIntegral_deriv_continuous hv a w) a b hab
  have hz (u : List ι) : L (coordinate v a b u) = 0 := by
    change (∫ t in a..b, coordinate v a b u (signaturePoint v a b hab t) *
      deriv (reverseIntegral v a w) t) = 0
    rw [← coordinate_one_form_zero_of_trivial_signature hv a b hzero u.reverse w]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    simp only [coordinate, ContinuousMap.coe_mk, signaturePoint, projIcc_of_mem hab ht', signature]
  exact functional_zero_of_coordinates (coordinate v a b) (coordinate_empty v a b)
    (coordinate_shuffle hv a b) (fun x y hxy => by
      by_contra! h
      exact hxy (Subtype.ext (funext h))) L hz f

end LinearInputCurveWordSignatureTopology
