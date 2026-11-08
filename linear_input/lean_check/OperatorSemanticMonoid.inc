/-!
# Semantic monoid of all compatible operators

Every operator preserving the complete old observation kernel can act
on the canonical predictive quotient. These compatible operators form
a monoid under function composition. Two different raw operators may
induce the same quotient operator; quotienting by that observational
kernel yields an injectively represented algebra of effective actions.

This formally distinguishes raw operator count from the count of
observationally distinct operators, a requirement for nontrivial
self-extending computation.
-/

noncomputable section

namespace LinearInputOperatorSemanticMonoid

open LinearInputOperatorWords
open LinearInputOperatorSemanticClosure

/-- An operator equipped with a proof that it respects predictive states. -/
def Op {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :=
  {T : α → α // Compatible K step T}

/-- The identity operator is always semantically compatible. -/
def identity {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) : Op K step :=
  ⟨fun x => x, compatible_id K step⟩

/-- Sequential composition of two compatible operators is compatible. -/
def compose {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A B : Op K step) : Op K step :=
  ⟨fun x => B.1 (A.1 x),
    compatible_comp K step A.1 B.1 A.2 B.2⟩

/-- Every old operator word is contained in the semantic monoid. -/
def fromWord {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (word : List ι) : Op K step :=
  ⟨run step word, compatible_word K step word⟩

/-- All constant operations also belong to the semantic monoid. -/
def constant {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (c : α) : Op K step :=
  ⟨fun _ => c, compatible_constant K step c⟩

theorem identity_apply {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (x : α) :
    (identity K step).1 x = x := rfl

theorem compose_apply {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A B : Op K step) (x : α) :
    (compose K step A B).1 x = B.1 (A.1 x) := rfl

theorem constant_apply {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (c x : α) : (constant K step c).1 x = c := rfl

/-- Semantic composition has the identity on the left. -/
theorem identity_left {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Op K step) :
    compose K step (identity K step) A = A := by
  apply Subtype.ext
  funext x
  rfl

theorem identity_right {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Op K step) :
    compose K step A (identity K step) = A := by
  apply Subtype.ext
  funext x
  rfl

/-- Composition is associative, without commutativity or invertibility. -/
theorem compose_assoc {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A B C : Op K step) :
    compose K step (compose K step A B) C =
      compose K step A (compose K step B C) := by
  apply Subtype.ext
  funext x
  rfl

/-- The identity is the empty old operator program. -/
theorem fromWord_nil {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    fromWord K step [] = identity K step := by
  apply Subtype.ext
  funext x
  rfl

/-- Old program compilation is a homomorphism into the semantic monoid. -/
theorem fromWord_append {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (w v : List ι) :
    fromWord K step (w ++ v) =
      compose K step (fromWord K step w) (fromWord K step v) := by
  apply Subtype.ext
  funext x
  exact run_append step w v x

/-- Every compatible operation determines a quotient endomorphism. -/
def onState {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Op K step → State K step → State K step :=
  fun A => induced K step A.1 A.2

theorem onState_encode {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Op K step) (x : α) :
    onState K step A (encode K step x) =
      encode K step (A.1 x) :=
  induced_encode K step A.1 A.2 x

/-- The quotient action of the identity is again the identity. -/
theorem onState_identity {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    onState K step (identity K step) = (fun q => q) :=
  induced_id K step

/-- Quotient actions preserve sequential composition exactly. -/
theorem onState_compose {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A B : Op K step) (q : State K step) :
    onState K step (compose K step A B) q =
      onState K step B (onState K step A q) :=
  induced_comp K step A.1 B.1 A.2 B.2 q

/-- Two compatible raw operators act identically after prediction quotienting. -/
def ObsEq {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A B : Op K step) : Prop :=
  ∀ x, WordEq K step (A.1 x) (B.1 x)

theorem obs_refl {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Op K step) :
    ObsEq K step A A := by
  intro x
  exact word_refl K step _

theorem obs_symm {α ω ι : Type*}
    {K : α → ω} {step : ι → α → α}
    {A B : Op K step} (h : ObsEq K step A B) :
    ObsEq K step B A := by
  intro x
  exact word_symm (h x)

theorem obs_trans {α ω ι : Type*}
    {K : α → ω} {step : ι → α → α}
    {A B C : Op K step}
    (hAB : ObsEq K step A B) (hBC : ObsEq K step B C) :
    ObsEq K step A C := by
  intro x
  exact word_trans (hAB x) (hBC x)

/-- The equivalence is preserved by composing any fixed suffix operator. -/
theorem obs_compose_right {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A B C : Op K step) (h : ObsEq K step A B) :
    ObsEq K step (compose K step A C) (compose K step B C) := by
  intro x
  exact C.2 _ _ (h x)

/-- It is also preserved by composing any fixed prefix operator. -/
theorem obs_compose_left {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (C A B : Op K step) (h : ObsEq K step A B) :
    ObsEq K step (compose K step C A) (compose K step C B) := by
  intro x
  exact h (C.1 x)

/-- Observational equality supports replacement in an arbitrary operator context. -/
theorem obs_compose_context {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (P A B S : Op K step) (h : ObsEq K step A B) :
    ObsEq K step
      (compose K step (compose K step P A) S)
      (compose K step (compose K step P B) S) :=
  obs_compose_right K step _ _ S
    (obs_compose_left K step P A B h)

/-- Two raw operators are observationally equal exactly if their
induced predictive quotient maps are the same function. -/
theorem obs_iff_same_quotient {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A B : Op K step) :
    ObsEq K step A B ↔
      onState K step A = onState K step B := by
  constructor
  · intro h
    funext q
    induction q using Quotient.inductionOn with
    | _ x =>
        exact (encode_eq_iff K step _ _).2 (h x)
  · intro h x
    apply (encode_eq_iff K step _ _).1
    have he := congrFun h (encode K step x)
    exact he

/-- Concrete equality of compatible endomorphisms implies observational equality. -/
theorem equal_operators_obsEq {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A B : Op K step) (h : A = B) : ObsEq K step A B := by
  subst B
  exact obs_refl K step A

/-- The quotient of raw operators by observational equality is well formed. -/
def obsSetoid {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Setoid (Op K step) where
  r := ObsEq K step
  iseqv := ⟨obs_refl K step, (fun h => obs_symm h),
    (fun h1 h2 => obs_trans h1 h2)⟩

/-- Effective operators are compatible operators modulo the predictive kernel. -/
abbrev Effective {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :=
  Quotient (obsSetoid K step)

/-- Represent an effective operator by its action on prediction states. -/
def evaluate {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Effective K step → (State K step → State K step) :=
  Quotient.lift (onState K step) (by
    intro A B h
    exact (obs_iff_same_quotient K step A B).1 h)

theorem evaluate_rep {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Op K step) :
    evaluate K step (Quotient.mk (obsSetoid K step) A) =
      onState K step A := rfl

/-- Distinct effective operators have distinct quotient-state actions. -/
theorem evaluate_injective {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Function.Injective (evaluate K step) := by
  intro q r h
  induction q using Quotient.inductionOn with
  | _ A =>
    induction r using Quotient.inductionOn with
    | _ B =>
      apply Quotient.sound
      exact (obs_iff_same_quotient K step A B).2 h

/-- The effective action algebra is embedded in the full endomorphism
monoid on predictive states. -/
theorem effective_acts_faithfully {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (q r : Effective K step) :
    evaluate K step q = evaluate K step r ↔ q = r := by
  constructor
  · exact fun h => evaluate_injective K step h
  · intro h
    rw [h]

/-- A constant state transformer induces a constant quotient-state map. -/
theorem onState_constant {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (c : α) (q : State K step) :
    onState K step (constant K step c) q =
      encode K step c := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- Every predictive quotient state has an original-state representative. -/
theorem encode_surjective {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Function.Surjective (encode K step) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨x, rfl⟩

/-- Choose one original state representing any predictive quotient state. -/
noncomputable def representative {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (q : State K step) : α :=
  Classical.choose (encode_surjective K step q)

theorem encode_representative {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (q : State K step) :
    encode K step (representative K step q) = q :=
  Classical.choose_spec (encode_surjective K step q)

/-- Every desired endomorphism on minimal predictive states has a raw
state transformer implementation, by choosing representatives. -/
noncomputable def realize {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (F : State K step → State K step) : α → α :=
  fun x => representative K step (F (encode K step x))

theorem realize_compatible {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (F : State K step → State K step) :
    Compatible K step (realize K step F) := by
  intro x y hxy
  apply (encode_eq_iff K step _ _).1
  change encode K step (representative K step (F (encode K step x))) =
    encode K step (representative K step (F (encode K step y)))
  rw [encode_representative, encode_representative]
  exact congrArg F ((encode_eq_iff K step x y).2 hxy)

/-- The constructed raw transformer is an element of the semantic monoid. -/
noncomputable def realizedOp {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (F : State K step → State K step) : Op K step :=
  ⟨realize K step F, realize_compatible K step F⟩

/-- The constructed operator realizes *exactly* the specified quotient map. -/
theorem realizedOp_exact {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (F : State K step → State K step) :
    onState K step (realizedOp K step F) = F := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x =>
      change encode K step (representative K step
        (F (encode K step x))) = F (encode K step x)
      exact encode_representative K step _

/-- Every endomorphism of the predictive state space is implementable
by some semantically compatible original-state operator. -/
theorem onState_surjective {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Function.Surjective (onState K step) := by
  intro F
  exact ⟨realizedOp K step F, realizedOp_exact K step F⟩

/-- The faithful representation of effective operators is also onto. -/
theorem evaluate_surjective {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Function.Surjective (evaluate K step) := by
  intro F
  refine ⟨Quotient.mk (obsSetoid K step) (realizedOp K step F), ?_⟩
  exact realizedOp_exact K step F

/-- Effective operators correspond bijectively to *all* self-maps
of predictive quotient states. -/
theorem evaluate_bijective {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Function.Bijective (evaluate K step) :=
  ⟨evaluate_injective K step, evaluate_surjective K step⟩

end LinearInputOperatorSemanticMonoid
