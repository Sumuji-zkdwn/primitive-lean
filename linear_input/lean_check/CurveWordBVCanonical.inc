/-!
Canonical signatures of continuous BV coordinate curves on compact intervals.
Representation independence is local to the actual interval of integration;
no equality of extensions or increments outside that interval is assumed.
-/

noncomputable section

namespace LinearInputCurveWordBVCanonical

open Set MeasureTheory
open LinearInputCurveWordBoundedVariation LinearInputCurveWordStieltjes
open LinearInputCurveWordBVSignature LinearInputCurveWordBVReparam

def SameIncrementsOn (p m q n : StieltjesFunction ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
    (p y - p x) - (m y - m x) = (q y - q x) - (n y - n x)

theorem SameIncrementsOn.mono {p m q n : StieltjesFunction ℝ} {a b c d : ℝ}
    (h : SameIncrementsOn p m q n a b) (hsub : Set.Icc c d ⊆ Set.Icc a b) :
    SameIncrementsOn p m q n c d :=
  fun x hx y hy => h x (hsub hx) y (hsub hy)

/-- Equality of coordinate increments only inside the compact interval
determines the difference of the two restricted Stieltjes measures. -/
theorem restricted_measure_sum_eq {p m q n : StieltjesFunction ℝ} {a b : ℝ}
    (h : SameIncrementsOn p m q n a b) :
    (p.measure + n.measure).restrict (Set.Ioc a b) =
      (q.measure + m.measure).restrict (Set.Ioc a b) := by
  rw [← StieltjesFunction.measure_add, ← StieltjesFunction.measure_add]
  apply Measure.ext_of_Ioc
  intro c d _
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Set.Ioc_inter_Ioc]
  by_cases hxy : max c a < min d b
  · have hx : max c a ∈ Set.Icc a b :=
      ⟨le_max_right _ _, hxy.le.trans (min_le_right _ _)⟩
    have hy : min d b ∈ Set.Icc a b :=
      ⟨(le_max_right _ _).trans hxy.le, min_le_right _ _⟩
    rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc]
    congr 1
    change (p (min d b) + n (min d b)) - (p (max c a) + n (max c a)) =
      (q (min d b) + m (min d b)) - (q (max c a) + m (max c a))
    linarith [h (max c a) hx (min d b) hy]
  · simp only [Set.Ioc_eq_empty hxy, measure_empty]

theorem stieltjesIntegral_independent_on {p m q n : StieltjesFunction ℝ} {a b : ℝ}
    (hab : a ≤ b) (h : SameIncrementsOn p m q n a b)
    {F : ℝ → ℝ} (hF : Continuous F) :
    stieltjesIntegral p m a b F = stieltjesIntegral q n a b F := by
  have he := congrArg (fun μ : Measure ℝ => ∫ t, F t ∂μ) (restricted_measure_sum_eq h)
  rw [Measure.restrict_add, Measure.restrict_add,
    integral_add_measure (hF.intervalIntegrable a b).1 (hF.intervalIntegrable a b).1,
    integral_add_measure (hF.intervalIntegrable a b).1 (hF.intervalIntegrable a b).1] at he
  unfold stieltjesIntegral
  simp only [intervalIntegral.integral_of_le hab]
  linarith

theorem stieltjesIntegral_congr_on (p m : StieltjesFunction ℝ) {a b : ℝ} {F G : ℝ → ℝ}
    (hab : a ≤ b) (h : Set.EqOn F G (Set.Icc a b)) :
    stieltjesIntegral p m a b F = stieltjesIntegral p m a b G := by
  have hu : Set.EqOn F G (Set.uIcc a b) := by simpa only [Set.uIcc_of_le hab] using h
  unfold stieltjesIntegral
  rw [intervalIntegral.integral_congr hu, intervalIntegral.integral_congr hu]

theorem reverseStieltjes_independent_on {ι : Type*} {p m q n : ι → StieltjesFunction ℝ}
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    {a b : ℝ} (h : ∀ i, SameIncrementsOn (p i) (m i) (q i) (n i) a b)
    (w : List ι) :
    ∀ t ∈ Set.Icc a b, reverseStieltjes p m a w t = reverseStieltjes q n a w t := by
  induction w with
  | nil => intro t _; rfl
  | cons i w ih =>
    intro t ht
    change stieltjesIntegral (p i) (m i) a t _ = stieltjesIntegral (q i) (n i) a t _
    have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl ht.2
    rw [stieltjesIntegral_congr_on (p i) (m i) ht.1 (fun s hs => ih s (hsub hs))]
    exact stieltjesIntegral_independent_on ht.1 ((h i).mono hsub)
      (reverseStieltjes_continuous q n hq hn a w)

/-- All degrees of the signature are independent of representations which
have the same signed coordinate increments on this interval alone. -/
theorem stieltjesSignature_independent_on {ι : Type*} {p m q n : ι → StieltjesFunction ℝ}
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    {a b : ℝ} (hab : a ≤ b)
    (h : ∀ i, SameIncrementsOn (p i) (m i) (q i) (n i) a b) (w : List ι) :
    stieltjesSignature p m a b w = stieltjesSignature q n a b w :=
  reverseStieltjes_independent_on hq hn h w.reverse b ⟨hab, le_rfl⟩

/-- A Stieltjes pair represents the coordinate increments on the given
interval. Its two functions may behave arbitrarily outside that interval. -/
def RepresentsOn (p m : StieltjesFunction ℝ) (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
    (p y - p x) - (m y - m x) = f y - f x

theorem representsOn_of_values {p m : StieltjesFunction ℝ} {f : ℝ → ℝ} {a b c : ℝ}
    (h : ∀ t ∈ Set.Icc a b, p t - m t = f t + c) : RepresentsOn p m f a b := by
  intro x hx y hy
  linarith [h x hx, h y hy]

theorem RepresentsOn.sameIncrementsOn {p m q n : StieltjesFunction ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (h : RepresentsOn p m f a b) (h' : RepresentsOn q n f a b) :
    SameIncrementsOn p m q n a b := by
  intro x hx y hy
  rw [h x hx y hy, h' x hx y hy]

def canonicalPositive {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Set.Icc a b)) (hc : ContinuousOn f (Set.Icc a b)) :
    StieltjesFunction ℝ :=
  bvPositive (constantExtension_boundedVariation hab hf) (constantExtension_continuous hab hc) a

def canonicalNegative {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Set.Icc a b)) (hc : ContinuousOn f (Set.Icc a b)) :
    StieltjesFunction ℝ :=
  bvNegative (constantExtension_boundedVariation hab hf) (constantExtension_continuous hab hc) a

theorem canonicalPositive_continuous {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Set.Icc a b)) (hc : ContinuousOn f (Set.Icc a b)) :
    Continuous (canonicalPositive hab hf hc : ℝ → ℝ) :=
  (jordan_continuous (constantExtension_boundedVariation hab hf)
    (constantExtension_continuous hab hc) a).1

theorem canonicalNegative_continuous {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Set.Icc a b)) (hc : ContinuousOn f (Set.Icc a b)) :
    Continuous (canonicalNegative hab hf hc : ℝ → ℝ) :=
  (jordan_continuous (constantExtension_boundedVariation hab hf)
    (constantExtension_continuous hab hc) a).2

theorem canonical_difference {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Set.Icc a b)) (hc : ContinuousOn f (Set.Icc a b))
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    canonicalPositive hab hf hc t - canonicalNegative hab hf hc t = f t - f a := by
  change jordanPositive (f ∘ clamp a b) a t - jordanNegative (f ∘ clamp a b) a t = _
  rw [jordan_difference]
  simp only [Function.comp_apply, clamp_eq ht,
    clamp_eq (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)]

theorem canonical_represents {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Set.Icc a b)) (hc : ContinuousOn f (Set.Icc a b)) :
    RepresentsOn (canonicalPositive hab hf hc) (canonicalNegative hab hf hc) f a b := by
  intro x hx y hy
  linarith [canonical_difference hab hf hc hx, canonical_difference hab hf hc hy]

/-- The actual signature of a coordinatewise continuous BV curve on a compact
interval, using the explicit Jordan decomposition of its constant extension. -/
def curveSignature {ι : Type*} (f : ι → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ i, BoundedVariationOn (f i) (Set.Icc a b))
    (hc : ∀ i, ContinuousOn (f i) (Set.Icc a b)) : List ι → ℝ :=
  stieltjesSignature (fun i => canonicalPositive hab (hf i) (hc i))
    (fun i => canonicalNegative hab (hf i) (hc i)) a b

/-- Every continuous Stieltjes representation of the same coordinate curve
on the interval gives the canonical signature, at all word degrees. -/
theorem curveSignature_eq_representation {ι : Type*} (f : ι → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ i, BoundedVariationOn (f i) (Set.Icc a b))
    (hc : ∀ i, ContinuousOn (f i) (Set.Icc a b))
    (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (hrep : ∀ i, RepresentsOn (p i) (m i) (f i) a b) (w : List ι) :
    curveSignature f hab hf hc w = stieltjesSignature p m a b w := by
  apply stieltjesSignature_independent_on hp hm hab
  intro i
  exact (canonical_represents hab (hf i) (hc i)).sameIncrementsOn (hrep i)

/-- Changes outside the integration interval do not alter the curve API. -/
theorem curveSignature_congr {ι : Type*} {f g : ι → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ i, BoundedVariationOn (f i) (Set.Icc a b))
    (hc : ∀ i, ContinuousOn (f i) (Set.Icc a b))
    (hg : ∀ i, BoundedVariationOn (g i) (Set.Icc a b))
    (hgc : ∀ i, ContinuousOn (g i) (Set.Icc a b))
    (he : ∀ i, Set.EqOn (f i) (g i) (Set.Icc a b)) (w : List ι) :
    curveSignature f hab hf hc w = curveSignature g hab hg hgc w := by
  apply curveSignature_eq_representation f hab hf hc
    (fun i => canonicalPositive hab (hg i) (hgc i))
    (fun i => canonicalNegative hab (hg i) (hgc i))
    (fun i => canonicalPositive_continuous hab (hg i) (hgc i))
    (fun i => canonicalNegative_continuous hab (hg i) (hgc i))
  intro i x hx y hy
  rw [canonical_represents hab (hg i) (hgc i) x hx y hy, he i hx, he i hy]

theorem coordinate_boundedVariation {ι : Type*} [Fintype ι] {γ : ℝ → (ι → ℝ)}
    {a b : ℝ} (hγ : BoundedVariationOn γ (Set.Icc a b)) (i : ι) :
    BoundedVariationOn (fun t => γ t i) (Set.Icc a b) :=
  (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).lipschitzWith.comp_boundedVariationOn hγ

theorem coordinate_continuousOn {ι : Type*} {γ : ℝ → (ι → ℝ)} {a b : ℝ}
    (hγ : ContinuousOn γ (Set.Icc a b)) (i : ι) :
    ContinuousOn (fun t => γ t i) (Set.Icc a b) :=
  (continuous_apply i).comp_continuousOn hγ

/-- A direct finite-dimensional path API. Bounded variation is imposed on
the path itself with its usual finite-product norm. -/
def pathSignature {ι : Type*} [Fintype ι] (γ : ℝ → (ι → ℝ)) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Set.Icc a b)) (hc : ContinuousOn γ (Set.Icc a b)) :
    List ι → ℝ :=
  curveSignature (fun i t => γ t i) hab (coordinate_boundedVariation hγ)
    (coordinate_continuousOn hc)

theorem pathSignature_eq_representation {ι : Type*} [Fintype ι]
    (γ : ℝ → (ι → ℝ)) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Set.Icc a b)) (hc : ContinuousOn γ (Set.Icc a b))
    (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (hrep : ∀ i, RepresentsOn (p i) (m i) (fun t => γ t i) a b) (w : List ι) :
    pathSignature γ hab hγ hc w = stieltjesSignature p m a b w :=
  curveSignature_eq_representation _ hab _ _ p m hp hm hrep w

theorem clock_mapsTo {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hm : MonotoneOn φ (Set.Icc a b)) :
    Set.MapsTo φ (Set.Icc a b) (Set.Icc (φ a) (φ b)) := by
  intro t ht
  exact ⟨hm ⟨le_rfl, hab⟩ ht ht.1, hm ht ⟨hab, le_rfl⟩ ht.2⟩

theorem clock_endpoints {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hm : MonotoneOn φ (Set.Icc a b)) : φ a ≤ φ b :=
  hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem reparam_boundedVariation {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hm : MonotoneOn φ (Set.Icc a b))
    (hf : BoundedVariationOn f (Set.Icc (φ a) (φ b))) :
    BoundedVariationOn (f ∘ φ) (Set.Icc a b) :=
  ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_monotoneOn f φ hm (clock_mapsTo hab hm))

theorem reparam_continuousOn {E : Type*} [TopologicalSpace E]
    {f : ℝ → E} {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hm : MonotoneOn φ (Set.Icc a b)) (hφ : ContinuousOn φ (Set.Icc a b))
    (hf : ContinuousOn f (Set.Icc (φ a) (φ b))) :
    ContinuousOn (f ∘ φ) (Set.Icc a b) :=
  hf.comp hφ (clock_mapsTo hab hm)

/-- The canonical curve signature is invariant under continuous monotone
clocks, including flat fibers and singular clocks. Only interval hypotheses
are used; the affine-tail extension is an internal construction. -/
theorem curveSignature_reparametrize {ι : Type*} (f : ι → ℝ → ℝ)
    {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hm : MonotoneOn φ (Set.Icc a b)) (hφ : ContinuousOn φ (Set.Icc a b))
    (hf : ∀ i, BoundedVariationOn (f i) (Set.Icc (φ a) (φ b)))
    (hc : ∀ i, ContinuousOn (f i) (Set.Icc (φ a) (φ b))) (w : List ι) :
    curveSignature (fun i => f i ∘ φ) hab
        (fun i => reparam_boundedVariation hab hm (hf i))
        (fun i => reparam_continuousOn hab hm hφ (hc i)) w =
      curveSignature f (clock_endpoints hab hm) hf hc w := by
  let p (i : ι) := canonicalPositive (clock_endpoints hab hm) (hf i) (hc i)
  let m (i : ι) := canonicalNegative (clock_endpoints hab hm) (hf i) (hc i)
  have hp (i : ι) : Continuous (p i : ℝ → ℝ) :=
    canonicalPositive_continuous _ _ _
  have hmp (i : ι) : Continuous (m i : ℝ → ℝ) :=
    canonicalNegative_continuous _ _ _
  let p' (i : ι) := reparam (p i) (hp i) (ontoExtension φ a b)
    (ontoExtension_monotone hab hm) (ontoExtension_continuous hab hφ)
  let m' (i : ι) := reparam (m i) (hmp i) (ontoExtension φ a b)
    (ontoExtension_monotone hab hm) (ontoExtension_continuous hab hφ)
  have hp' (i : ι) : Continuous (p' i : ℝ → ℝ) :=
    (hp i).comp (ontoExtension_continuous hab hφ)
  have hm' (i : ι) : Continuous (m' i : ℝ → ℝ) :=
    (hmp i).comp (ontoExtension_continuous hab hφ)
  have hrep (i : ι) : RepresentsOn (p' i) (m' i) (f i ∘ φ) a b := by
    intro x hx y hy
    change (p i (ontoExtension φ a b y) - p i (ontoExtension φ a b x)) -
      (m i (ontoExtension φ a b y) - m i (ontoExtension φ a b x)) = _
    rw [ontoExtension_eq hx, ontoExtension_eq hy]
    exact canonical_represents (clock_endpoints hab hm) (hf i) (hc i)
      (φ x) (clock_mapsTo hab hm hx) (φ y) (clock_mapsTo hab hm hy)
  rw [curveSignature_eq_representation _ hab _ _ p' m' hp' hm' hrep]
  exact stieltjesSignature_interval_reparam p m hp hmp hab hm hφ w

theorem pathSignature_reparametrize {ι : Type*} [Fintype ι] (γ : ℝ → (ι → ℝ))
    {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hm : MonotoneOn φ (Set.Icc a b)) (hφ : ContinuousOn φ (Set.Icc a b))
    (hγ : BoundedVariationOn γ (Set.Icc (φ a) (φ b)))
    (hc : ContinuousOn γ (Set.Icc (φ a) (φ b))) (w : List ι) :
    pathSignature (γ ∘ φ) hab (reparam_boundedVariation hab hm hγ)
        (reparam_continuousOn hab hm hφ hc) w =
      pathSignature γ (clock_endpoints hab hm) hγ hc w :=
  curveSignature_reparametrize _ hab hm hφ (coordinate_boundedVariation hγ)
    (coordinate_continuousOn hc) w

theorem pathSignature_congr {ι : Type*} [Fintype ι] {γ δ : ℝ → (ι → ℝ)}
    {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Set.Icc a b)) (hcγ : ContinuousOn γ (Set.Icc a b))
    (hδ : BoundedVariationOn δ (Set.Icc a b)) (hcδ : ContinuousOn δ (Set.Icc a b))
    (he : Set.EqOn γ δ (Set.Icc a b)) (w : List ι) :
    pathSignature γ hab hγ hcγ w = pathSignature δ hab hδ hcδ w := by
  apply curveSignature_congr hab
  intro i t ht
  exact congrFun (he ht) i

theorem c1_representsOn {f v : ℝ → ℝ} (hv : Continuous v)
    (hd : ∀ t, HasDerivAt f (v t) t) (a b : ℝ) :
    RepresentsOn (positiveStieltjes v hv) (negativeStieltjes v hv) f a b := by
  intro x _ y _
  change (primitive (positiveVelocity v) y - primitive (positiveVelocity v) x) -
    (primitive (negativeVelocity v) y - primitive (negativeVelocity v) x) = _
  rw [primitive_sub (positiveVelocity_continuous hv), primitive_sub (negativeVelocity_continuous hv),
    ← intervalIntegral.integral_sub ((positiveVelocity_continuous hv).intervalIntegrable x y)
      ((negativeVelocity_continuous hv).intervalIntegrable x y)]
  simp only [velocity_decomposition]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hv.intervalIntegrable x y)

/-- The canonical BV curve API agrees with the actual velocity-integral
signature for continuously differentiable coordinates. -/
theorem curveSignature_eq_c1 {ι : Type*} {f v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (hd : ∀ i t, HasDerivAt (f i) (v i t) t)
    {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ i, BoundedVariationOn (f i) (Set.Icc a b))
    (hc : ∀ i, ContinuousOn (f i) (Set.Icc a b)) (w : List ι) :
    curveSignature f hab hf hc w = LinearInputCurveWordSignature.signature v a b w := by
  rw [curveSignature_eq_representation f hab hf hc
    (fun i => positiveStieltjes (v i) (hv i)) (fun i => negativeStieltjes (v i) (hv i))
    (fun i => primitive_continuous (positiveVelocity_continuous (hv i)))
    (fun i => primitive_continuous (negativeVelocity_continuous (hv i)))
    (fun i => c1_representsOn (hv i) (hd i) a b)]
  exact c1_stieltjesSignature_eq_signature hv a b w

theorem pathSignature_eq_c1 {ι : Type*} [Fintype ι] {γ : ℝ → (ι → ℝ)}
    {v : ι → ℝ → ℝ} (hv : ∀ i, Continuous (v i))
    (hd : ∀ i t, HasDerivAt (fun s => γ s i) (v i t) t)
    {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Set.Icc a b)) (hc : ContinuousOn γ (Set.Icc a b))
    (w : List ι) : pathSignature γ hab hγ hc w =
      LinearInputCurveWordSignature.signature v a b w :=
  curveSignature_eq_c1 hv hd hab (coordinate_boundedVariation hγ) (coordinate_continuousOn hc) w

/-- Arc-length factorization preserves the actual canonical BV signature in
every word degree. The factor is constructed, is 1-Lipschitz, and retains the
original variation length; flat portions of the variation clock are allowed. -/
theorem arcLength_signature_factorization {ι : Type*} [Fintype ι]
    {γ : ℝ → (ι → ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Set.Icc a b)) (hc : ContinuousOn γ (Set.Icc a b)) :
    ∃ G : ℝ → (ι → ℝ),
      ∃ hG : BoundedVariationOn G (Set.Icc 0 (variationLength γ a b)),
      ∃ hGC : ContinuousOn G (Set.Icc 0 (variationLength γ a b)),
        LipschitzWith 1 G ∧ Set.EqOn γ (G ∘ variationClock γ a b) (Set.Icc a b) ∧
        (eVariationOn G (Set.Icc 0 (variationLength γ a b))).toReal = variationLength γ a b ∧
        ∀ w, pathSignature γ hab hγ hc w =
          pathSignature G ENNReal.toReal_nonneg hG hGC w := by
  let L := variationLength γ a b
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  obtain ⟨g, hg, hfactor⟩ := arcLength_factorization hab hγ hc
  let G : ℝ → (ι → ℝ) := g ∘ Set.projIcc 0 L hL
  have hLip : LipschitzWith 1 G := by
    simpa only [one_mul] using hg.comp (LipschitzWith.projIcc hL)
  have hG : BoundedVariationOn G (Set.Icc 0 L) := by
    simpa only [Set.inter_self] using
      (hLip.locallyBoundedVariationOn (Set.Icc 0 L)) 0 L ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩
  have hGC : ContinuousOn G (Set.Icc 0 L) := hLip.continuous.continuousOn
  have hfac : Set.EqOn γ (G ∘ variationClock γ a b) (Set.Icc a b) := by
    intro t ht
    dsimp only [G, Function.comp_apply]
    rw [Set.projIcc_of_mem hL (variationClock_mem hab hγ ht)]
    exact (hfactor ⟨t, ht⟩).symm
  have hm := variationClock_monotoneOn hab hγ
  have hclock : ContinuousOn (variationClock γ a b) (Set.Icc a b) :=
    variation_clock_continuousOn hγ hc ⟨le_rfl, hab⟩
  refine ⟨G, hG, hGC, hLip, hfac, ?_, ?_⟩
  · have he := eVariationOn.comp_eq_of_monotoneOn G (variationClock γ a b) hm
    rw [variationClock_image hab hγ hc] at he
    rw [← he, ← eVariationOn.congr hfac]
    rfl
  · intro w
    have hG' : BoundedVariationOn G
        (Set.Icc (variationClock γ a b a) (variationClock γ a b b)) := by
      simpa only [variationClock_initial, variationClock_terminal γ hab] using hG
    have hGC' : ContinuousOn G
        (Set.Icc (variationClock γ a b a) (variationClock γ a b b)) := by
      simpa only [variationClock_initial, variationClock_terminal γ hab] using hGC
    have hs := pathSignature_reparametrize G hab hm hclock hG' hGC' w
    calc
      pathSignature γ hab hγ hc w =
          pathSignature (G ∘ variationClock γ a b) hab
            (reparam_boundedVariation hab hm hG')
            (reparam_continuousOn hab hm hclock hGC') w :=
        pathSignature_congr hab hγ hc _ _ hfac w
      _ = _ := by simpa only [variationClock_initial, variationClock_terminal γ hab] using! hs

end LinearInputCurveWordBVCanonical
