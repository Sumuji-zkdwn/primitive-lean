import Research.SiphonPredictiveQuotient

/-!
# Relational round trips and observation-relative forgetting

`comp r s` means r after s.  A relation is a possibly empty set-valued
map; composition takes the union over all intermediate candidates.

For a surjective function f, f g f = f is equivalent to f g = identity,
and hence already implies g f g = g.  These are consistency statements,
not claims of individual reconstruction or physical erasure.

The polynomial example reuses the existing E, signature, and fresh probe.
The existing signature has codomain R x R, including unrealized negative
second coordinates.  Its full inverse is empty there.  The two full-inverse
round-trip identities do not require surjectivity onto that codomain.

No energetic, neural, or fluid-dynamical interpretation is assumed.
-/

namespace Elastica.ForgettingRoundTrips

abbrev Rel (α β : Type*) := α → β → Prop

/-- Relation composition: first s, then r. -/
def comp {α β γ : Type*} (r : Rel β γ) (s : Rel α β) : Rel α γ :=
  fun x z => ∃ y, s x y ∧ r y z

def graph {α β : Type*} (f : α → β) : Rel α β := fun x y => f x = y

def idRel (α : Type*) : Rel α α := fun x y => x = y

/-- The entire inverse image, with no choice of a representative. -/
def fullInverse {α β : Type*} (f : α → β) : Rel β α := fun y x => f x = y

/-- Every label has a candidate and every candidate re-encodes to that label. -/
def FiberSupported {α β : Type*} (f : α → β) (g : Rel β α) : Prop :=
  ∀ y, (∃ x, g y x) ∧ ∀ x, g y x → f x = y

theorem comp_assoc {α β γ δ : Type*}
    (r : Rel γ δ) (s : Rel β γ) (t : Rel α β) :
    comp r (comp s t) = comp (comp r s) t := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨a, hta, hsy⟩, hrz⟩
    exact ⟨a, hta, ⟨y, hsy, hrz⟩⟩
  · rintro ⟨a, hta, y, hsy, hrz⟩
    exact ⟨y, ⟨a, hta, hsy⟩, hrz⟩

theorem graph_decoder_iff_supported {α β : Type*}
    (f : α → β) (g : Rel β α) :
    comp (graph f) g = idRel β ↔ FiberSupported f g := by
  constructor
  · intro h y
    have hyy : comp (graph f) g y y := by
      rw [h]
      rfl
    rcases hyy with ⟨x, hx, _⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    intro z hz
    have hy : comp (graph f) g y (f z) := ⟨z, hz, rfl⟩
    rw [h] at hy
    change y = f z at hy
    exact hy.symm
  · intro h
    funext y y'
    apply propext
    constructor
    · rintro ⟨x, hx, hfx⟩
      change y = y'
      exact ((h y).2 x hx).symm.trans hfx
    · intro hyy
      change y = y' at hyy
      subst y'
      rcases (h y).1 with ⟨x, hx⟩
      exact ⟨x, hx, (h y).2 x hx⟩

/-- Surjectivity is needed in the forward implication. -/
theorem first_roundtrip_iff_identity {α β : Type*}
    (f : α → β) (g : Rel β α) (hf : Function.Surjective f) :
    comp (graph f) (comp g (graph f)) = graph f ↔
      comp (graph f) g = idRel β := by
  constructor
  · intro h
    funext y y'
    apply propext
    constructor
    · rintro ⟨x', hg, hfy⟩
      obtain ⟨x, hx⟩ := hf y
      have ht : comp (graph f) (comp g (graph f)) x y' :=
        ⟨x', ⟨y, hx, hg⟩, hfy⟩
      rw [h] at ht
      change f x = y' at ht
      change y = y'
      exact hx.symm.trans ht
    · intro hyy
      change y = y' at hyy
      subst y'
      obtain ⟨x, hx⟩ := hf y
      have ht : comp (graph f) (comp g (graph f)) x y := by
        rw [h]
        exact hx
      rcases ht with ⟨x', ⟨a, hxa, hg⟩, hfy⟩
      have ha : a = y := hxa.symm.trans hx
      rw [ha] at hg
      exact ⟨x', hg, hfy⟩
  · intro h
    funext x y
    apply propext
    constructor
    · rintro ⟨x', ⟨a, hxa, hg⟩, hfy⟩
      have hay : comp (graph f) g a y := ⟨x', hg, hfy⟩
      rw [h] at hay
      change a = y at hay
      exact hxa.trans hay
    · intro hxy
      have hfx : comp (graph f) g (f x) (f x) := by
        rw [h]
        rfl
      rcases hfx with ⟨x', hg, hfx'⟩
      exact ⟨x', ⟨f x, rfl, hg⟩, hfx'.trans hxy⟩

theorem first_roundtrip_iff_supported {α β : Type*}
    (f : α → β) (g : Rel β α) (hf : Function.Surjective f) :
    comp (graph f) (comp g (graph f)) = graph f ↔ FiberSupported f g :=
  (first_roundtrip_iff_identity f g hf).trans (graph_decoder_iff_supported f g)

theorem second_roundtrip_of_identity {α β : Type*}
    (f : α → β) (g : Rel β α) (h : comp (graph f) g = idRel β) :
    comp g (comp (graph f) g) = g := by
  funext y z
  apply propext
  constructor
  · rintro ⟨a, hya, haz⟩
    rw [h] at hya
    change y = a at hya
    subst a
    exact haz
  · intro hyz
    have hyy : comp (graph f) g y y := by
      rw [h]
      rfl
    exact ⟨y, hyy, hyz⟩

theorem second_roundtrip_of_first {α β : Type*}
    (f : α → β) (g : Rel β α) (hf : Function.Surjective f)
    (h : comp (graph f) (comp g (graph f)) = graph f) :
    comp g (comp (graph f) g) = g :=
  second_roundtrip_of_identity f g ((first_roundtrip_iff_identity f g hf).mp h)

/-- Fixed, perfectly consistent round trips are idempotent as relations. -/
theorem saturation_idempotent_of_identity {α β : Type*}
    (f : α → β) (g : Rel β α) (h : comp (graph f) g = idRel β) :
    comp (comp g (graph f)) (comp g (graph f)) = comp g (graph f) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨a, ⟨b, hxb, hba⟩, c, hac, hcz⟩
    have hbc : comp (graph f) g b c := ⟨a, hba, hac⟩
    rw [h] at hbc
    change b = c at hbc
    rw [← hbc] at hcz
    exact ⟨b, hxb, hcz⟩
  · rintro ⟨b, hxb, hbz⟩
    have hbb : comp (graph f) g b b := by
      rw [h]
      rfl
    rcases hbb with ⟨a, hba, hab⟩
    exact ⟨a, ⟨b, hxb, hba⟩, ⟨b, hab, hbz⟩⟩

/-- This identity needs no surjectivity assumption. -/
theorem full_inverse_first_roundtrip {α β : Type*} (f : α → β) :
    comp (graph f) (comp (fullInverse f) (graph f)) = graph f := by
  funext x y
  apply propext
  constructor
  · rintro ⟨x', ⟨a, hxa, hx'a⟩, hx'y⟩
    exact hxa.trans (hx'a.symm.trans hx'y)
  · intro hxy
    exact ⟨x, ⟨f x, rfl, rfl⟩, hxy⟩

/-- Empty fibers outside the image do not invalidate the inverse relation law. -/
theorem full_inverse_second_roundtrip {α β : Type*} (f : α → β) :
    comp (fullInverse f) (comp (graph f) (fullInverse f)) = fullInverse f := by
  funext y x
  apply propext
  constructor
  · rintro ⟨a, ⟨x', hx'y, hx'a⟩, hxa⟩
    exact hxa.trans (hx'a.symm.trans hx'y)
  · intro hxy
    exact ⟨y, ⟨x, hxy, hxy⟩, hxy⟩

theorem full_inverse_saturation_iff {α β : Type*} (f : α → β) (x x' : α) :
    comp (fullInverse f) (graph f) x x' ↔ f x = f x' := by
  constructor
  · rintro ⟨y, hxy, hx'y⟩
    exact hxy.trans hx'y.symm
  · intro hxx'
    exact ⟨f x, rfl, hxx'.symm⟩

theorem full_inverse_contains_original {α β : Type*} (f : α → β) (x : α) :
    comp (fullInverse f) (graph f) x x :=
  ⟨f x, rfl, rfl⟩

theorem full_inverse_saturation_idempotent {α β : Type*} (f : α → β) :
    comp (comp (fullInverse f) (graph f)) (comp (fullInverse f) (graph f)) =
      comp (fullInverse f) (graph f) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact (full_inverse_saturation_iff f x z).mpr
      (((full_inverse_saturation_iff f x y).mp hxy).trans
        ((full_inverse_saturation_iff f y z).mp hyz))
  · intro hxz
    exact ⟨x, full_inverse_contains_original f x, hxz⟩

/-- Under consistency, retaining every original state characterizes the full inverse. -/
theorem full_inverse_iff_contains_all {α β : Type*}
    (f : α → β) (g : Rel β α) (hs : FiberSupported f g) :
    g = fullInverse f ↔ ∀ x, g (f x) x := by
  constructor
  · intro h x
    rw [h]
    rfl
  · intro h
    funext y x
    apply propext
    constructor
    · intro hxy
      exact (hs y).2 x hxy
    · intro hxy
      change f x = y at hxy
      have hx := h x
      simpa only [hxy] using hx

/-! ## Small counterexamples: consistency is not individual reconstruction -/

def constantEncode (_ : Bool) : Unit := ()

def representativeDecoder (_ : Unit) (x : Bool) : Prop := x = false

theorem representative_consistent :
    comp (graph constantEncode) representativeDecoder = idRel Unit := by
  apply (graph_decoder_iff_supported constantEncode representativeDecoder).mpr
  intro y
  constructor
  · exact ⟨false, rfl⟩
  · intro x _
    cases y
    rfl

theorem representative_roundtrips :
    comp (graph constantEncode) (comp representativeDecoder (graph constantEncode)) =
        graph constantEncode ∧
      comp representativeDecoder (comp (graph constantEncode) representativeDecoder) =
        representativeDecoder := by
  have hf : Function.Surjective constantEncode := by
    intro y
    cases y
    exact ⟨false, rfl⟩
  constructor
  · exact (first_roundtrip_iff_identity constantEncode representativeDecoder hf).mpr
      representative_consistent
  · exact second_roundtrip_of_identity constantEncode representativeDecoder
      representative_consistent

theorem representative_omits_original :
    ¬ comp representativeDecoder (graph constantEncode) true true := by
  rintro ⟨y, _, h⟩
  change (true : Bool) = false at h
  cases h

def badDecoder (_ : Bool) (x : Bool × Bool) : Prop := x = (false, false)

/-- A nonempty decoder can satisfy only the second of the two identities. -/
theorem second_only_counterexample :
    comp badDecoder (comp (graph (Prod.fst : Bool × Bool → Bool)) badDecoder) =
        badDecoder ∧
      comp (graph (Prod.fst : Bool × Bool → Bool))
        (comp badDecoder (graph (Prod.fst : Bool × Bool → Bool))) ≠
        graph (Prod.fst : Bool × Bool → Bool) := by
  constructor
  · funext y x
    apply propext
    constructor
    · rintro ⟨a, _, hax⟩
      exact hax
    · intro hyx
      exact ⟨false, ⟨(false, false), rfl, rfl⟩, hyx⟩
  · intro h
    have ht : comp (graph (Prod.fst : Bool × Bool → Bool))
        (comp badDecoder (graph (Prod.fst : Bool × Bool → Bool)))
        (true, false) true := by
      rw [h]
      rfl
    rcases ht with ⟨x, ⟨a, _, hx⟩, hfx⟩
    change x = (false, false) at hx
    subst x
    change (false : Bool) = true at hfx
    cases hfx

/-! ## Existing polynomial dynamics and its observation signature -/

open Elastica.SiphonPolynomialE
open Elastica.SiphonPredictiveQuotient

theorem signature_inverse_roundtrips :
    comp (graph signature) (comp (fullInverse signature) (graph signature)) =
        graph signature ∧
      comp (fullInverse signature) (comp (graph signature) (fullInverse signature)) =
        fullInverse signature :=
  ⟨full_inverse_first_roundtrip signature, full_inverse_second_roundtrip signature⟩

theorem signature_inverse_contains_mirror (z : State) :
    fullInverse signature (signature z) (mirror z) :=
  signature_mirror z

theorem signature_has_distinct_pair :
    ∃ z t : State, z ≠ t ∧ signature z = signature t := by
  refine ⟨(0, 1), (0, -1), ?_, ?_⟩
  · intro h
    have h2 := congrArg Prod.snd h
    norm_num at h2
  · norm_num [signature, K, I]

/-- The observed signature alone cannot identify every individual full state. -/
theorem no_full_state_decoder :
    ¬ ∃ d : (ℝ × ℝ) → State, ∀ z, d (signature z) = z := by
  rintro ⟨d, hd⟩
  obtain ⟨z, t, hne, hs⟩ := signature_has_distinct_pair
  apply hne
  calc
    z = d (signature z) := (hd z).symm
    _ = d (signature t) := congrArg d hs
    _ = t := hd t

/-- The fresh probe acts on the retained full state, not on the old quotient alone. -/
theorem fresh_does_not_descend :
    ¬ ∃ a : (ℝ × ℝ) → (ℝ × ℝ),
      ∀ z : State, signature (freshStep () z) = a (signature z) := by
  rintro ⟨a, ha⟩
  have hs : signature ((0, 1) : State) = signature ((0, -1) : State) := by
    norm_num [signature, K, I]
  have ht : signature (freshStep () ((0, 1) : State)) =
      signature (freshStep () ((0, -1) : State)) := by
    calc
      _ = a (signature ((0, 1) : State)) := ha _
      _ = a (signature ((0, -1) : State)) := congrArg a hs
      _ = _ := (ha _).symm
  have h2 := congrArg Prod.snd ht
  norm_num [signature, freshStep, K, I] at h2

/-- Sequential readouts use the action sequence E, R, E on one full state. -/
theorem sequential_invariant_reconstruction (z : State) :
    I z =
      (K (E (freshStep () (E z))) - 2 * K (E z) + K z - 1) / 2 := by
  rw [readout_fresh_E, I_E]
  simp only [readout_E]
  ring

def sequentialSignature (z : State) : ℝ × ℝ × ℝ :=
  (K z, K (E z), K (E (freshStep () (E z))))

/-- No duplicated initial state is needed for this exact algebraic recovery. -/
theorem sequentialSignature_injective : Function.Injective sequentialSignature := by
  intro z t h
  have h0 := congrArg (fun p : ℝ × ℝ × ℝ => p.1) h
  have h1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) h
  have h2 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) h
  change K z = K t at h0
  change K (E z) = K (E t) at h1
  change K (E (freshStep () (E z))) = K (E (freshStep () (E t))) at h2
  have hi : I z = I t := by
    calc
      I z = (K (E (freshStep () (E z))) - 2 * K (E z) + K z - 1) / 2 :=
        sequential_invariant_reconstruction z
      _ = (K (E (freshStep () (E t))) - 2 * K (E t) + K t - 1) / 2 := by
        rw [h0, h1, h2]
      _ = I t := (sequential_invariant_reconstruction t).symm
  apply Prod.ext
  · exact h0
  · dsimp [I] at hi
    change z.1 = t.1 at h0
    rw [h0] at hi
    linarith

#print axioms comp_assoc
#print axioms graph_decoder_iff_supported
#print axioms first_roundtrip_iff_identity
#print axioms first_roundtrip_iff_supported
#print axioms second_roundtrip_of_identity
#print axioms second_roundtrip_of_first
#print axioms saturation_idempotent_of_identity
#print axioms full_inverse_first_roundtrip
#print axioms full_inverse_second_roundtrip
#print axioms full_inverse_saturation_iff
#print axioms full_inverse_contains_original
#print axioms full_inverse_saturation_idempotent
#print axioms full_inverse_iff_contains_all
#print axioms representative_consistent
#print axioms representative_roundtrips
#print axioms representative_omits_original
#print axioms second_only_counterexample
#print axioms signature_inverse_roundtrips
#print axioms signature_inverse_contains_mirror
#print axioms signature_has_distinct_pair
#print axioms no_full_state_decoder
#print axioms fresh_does_not_descend
#print axioms sequential_invariant_reconstruction
#print axioms sequentialSignature_injective

end Elastica.ForgettingRoundTrips
