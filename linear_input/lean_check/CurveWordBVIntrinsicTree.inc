/-!
Actual signature routes and the geometric triangle bridge. Every arc used
here is produced from an actual coordinate curve inside a specified closed
signature set; no arbitrary image arc is identified with a time subinterval.
-/

noncomputable section
namespace LinearInputCurveWordBVIntrinsicTree

open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
open LinearInputCurveWordFormalSeries LinearInputCurveWordBVCanonical
open LinearInputCurveWordBVCompactness LinearInputCurveWordBVReduced
open LinearInputCurveWordBVLoopErase LinearInputCurveWordBVPathOperations
open LinearInputCurveWordBVArc LinearInputCurveWordBVIntrinsic

def routeLift {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) (t : Icc (0 : ℝ) r.duration) : Series ι :=
  product P (lipSignature r.curve r.lipschitz 0 t.val t.property.1)

def routeImage {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) : Set (Series ι) := range (routeLift r)

theorem route_prefix_eq_controlled {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q)
    (t : Icc (0 : ℝ) r.duration) :
    routeLift r t = basedPrefixSignature r.nonneg (r.curve 0) P
      (speedControlledOfLipschitz r.nonneg r.curve r.lipschitz) t.val := by
  change product P (lipSignature r.curve r.lipschitz 0 t.val t.property.1) =
    product P (prefixSignature r.nonneg (r.curve 0)
      (speedControlledOfLipschitz r.nonneg r.curve r.lipschitz) t.val)
  rw [prefixSignature_eq_pathSignature _ _ _ t.property.1]
  apply congrArg (product P)
  funext w
  apply pathSignature_congr t.property.1
  exact (speedControlledOfLipschitz_eq r.nonneg r.curve r.lipschitz).symm.mono
    (Icc_subset_Icc le_rfl t.property.2)

theorem routeLift_continuous {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    Continuous (routeLift r) := by
  have he : routeLift r = fun t : Icc (0 : ℝ) r.duration =>
      basedPrefixSignature r.nonneg (r.curve 0) P
        (speedControlledOfLipschitz r.nonneg r.curve r.lipschitz) t.val :=
    funext (route_prefix_eq_controlled r)
  rw [he]
  exact (basedPrefixSignature_continuous_time _ _ _ _).comp continuous_subtype_val

theorem routeImage_isCompact {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    IsCompact (routeImage r) := isCompact_range (routeLift_continuous r)

theorem routeImage_subset {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) : routeImage r ⊆ K := by
  rintro _ ⟨t, rfl⟩
  exact r.within t.val t.property

/-- Every actual route in a closed signature set admits an actual simple
signature arc in that same set, with no greater travel time. -/
theorem exists_injective_route {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} (hK : IsClosed K) {P Q : Series ι} (hP : P [] = 1)
    (r : Route K P Q) :
    ∃ s : Route K P Q, Function.Injective (routeLift s) ∧ s.duration ≤ r.duration := by
  let f := speedControlledOfLipschitz r.nonneg r.curve r.lipschitz
  have hf : f ∈ signatureRangeClass r.nonneg (r.curve 0) P Q K := by
    constructor
    · exact (route_prefix_eq_controlled r ⟨r.duration, r.nonneg, le_rfl⟩).symm.trans r.terminal
    · intro t
      rw [← route_prefix_eq_controlled r t]
      exact r.within t.val t.property
  obtain ⟨ℓ, hℓ, G, hG, hstart, _, hend, hrange, hinj, hmin⟩ :=
    exists_injective_signature_lift_in_closed_range r.nonneg (r.curve 0) P Q hP hK f hf
  let s : Route K P Q :=
    { duration := ℓ
      nonneg := hℓ
      curve := G
      lipschitz := hG
      initial := hstart.trans r.initial
      terminal := hend
      within := fun t ht => hrange ⟨t, ht⟩ }
  refine ⟨s, hinj, ?_⟩
  have hbound := unitLipschitz_variation_toReal_le
    (pathExtension_lipschitz r.nonneg f.val f.property.1) r.nonneg
  exact (hmin f hf).trans (by simpa only [sub_zero] using hbound)

theorem injective_route_images_eq {ι : Type*} [Fintype ι]
    {K J : Set (Series ι)} {P Q : Series ι} (hP : P [] = 1)
    (r : Route K P Q) (s : Route J P Q)
    (hr : Function.Injective (routeLift r)) (hs : Function.Injective (routeLift s)) :
    routeImage r = routeImage s :=
  LinearInputCurveWordBVArcUnique.injective_lipSignature_ranges_eq r.curve s.curve
    r.lipschitz s.lipschitz r.nonneg s.nonneg P hP (r.initial.trans s.initial.symm)
    hr hs (r.terminal.trans s.terminal.symm)

/-- A simple actual arc is contained in every closed set that admits an
actual route between the same endpoints. The competing route is first
reduced within that closed set, then actual arc uniqueness applies. -/
theorem injective_route_image_subset {ι : Type*} [Fintype ι]
    {K J : Set (Series ι)} (hJ : IsClosed J) {P Q : Series ι} (hP : P [] = 1)
    (r : Route K P Q) (s : Route J P Q) (hr : Function.Injective (routeLift r)) :
    routeImage r ⊆ J := by
  obtain ⟨s', hs', _⟩ := exists_injective_route hJ hP s
  rw [injective_route_images_eq hP r s' hr hs']
  exact routeImage_subset s'

def routeInImage {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    Route (routeImage r) P Q :=
  { r with within := fun t ht => ⟨⟨t, ht⟩, rfl⟩ }

/-- An actual simple signature arc is contained in the union of any two
actual connecting routes. Compactness, an actual joined competitor, and
actual arc uniqueness discharge the geometric triangle-cover property. -/
theorem routeImage_subset_union {ι : Type*} [Fintype ι]
    {K J H : Set (Series ι)} {P Q R : Series ι} (hP : P [] = 1)
    (r : Route K P Q) (s : Route J P R) (t : Route H R Q)
    (hr : Function.Injective (routeLift r)) :
    routeImage r ⊆ routeImage s ∪ routeImage t := by
  let s' : Route (routeImage s ∪ routeImage t) P R :=
    (routeInImage s).mono subset_union_left
  let t' : Route (routeImage s ∪ routeImage t) R Q :=
    (routeInImage t).mono subset_union_right
  exact injective_route_image_subset
    ((routeImage_isCompact s).union (routeImage_isCompact t)).isClosed hP r (s'.join t') hr

open LinearInputCurveWordGeodesicTree LinearInputCurveWordSignatureTree

/-- The metric application only asks for the actual route representation
of its geodesics. Triangle thinness is proved from the preceding actual
curve constructions, rather than supplied as an extra hypothesis. -/
theorem fourPoint_of_actual_signature_geodesics {ι E : Type*} [Fintype ι] [MetricSpace E]
    {K : Set (Series ι)} (value : E → Series ι) (hvalue : Function.Injective value)
    (hunit : ∀ x, value x [] = 1) (G : GeodesicSystem E)
    (routes : ∀ x y, Route K (value x) (value y))
    (hinj : ∀ x y, Function.Injective (routeLift (routes x y)))
    (himage : ∀ x y, value '' segment G x y = routeImage (routes x y)) :
    @FourPoint E _ := by
  apply fourPoint_of_thin_geodesics G
  intro x y z p hp
  have hv : value p ∈ routeImage (routes x y) := by
    rw [← himage x y]
    exact ⟨p, hp, rfl⟩
  have hcover := routeImage_subset_union (hunit x) (routes x y) (routes x z) (routes z y)
    (hinj x y) hv
  rcases hcover with h | h
  · left
    rw [← himage x z] at h
    obtain ⟨q, hq, he⟩ := h
    exact hvalue he ▸ hq
  · right
    rw [← himage z y] at h
    obtain ⟨q, hq, he⟩ := h
    exact hvalue he ▸ hq

/-- The actual intrinsic signature space satisfies the four-point condition.
The metric, attained shortest routes, geodesics, and triangle containment
are all constructed from continuous BV coordinate curves. -/
theorem intrinsic_fourPoint {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) {P0 : Series ι} (hP0 : P0 [] = 1) :
    @FourPoint (IntrinsicPoint K hK P0) _ :=
  fourPoint_of_actual_signature_geodesics IntrinsicPoint.value IntrinsicPoint.value_injective
    (IntrinsicPoint.value_nil hP0) (intrinsicGeodesicSystem K hK P0) shortestRoute
    shortestRoute_lift_injective geodesicPoint_value_range

end LinearInputCurveWordBVIntrinsicTree
