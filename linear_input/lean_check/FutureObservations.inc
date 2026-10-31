/-!
# Future-observation equivalence and its canonical minimal deterministic state

Given an observation K : α → ω and a deterministic update U : α → α,
two states are equivalent if all their future observation traces coincide.

The quotient by this equivalence has a well-defined output and transition.
Any other deterministic state representation that exactly preserves the
output and update can distinguish at least as many pairs of original
states. This is kernel minimality, not a geometric packing result.

No idempotence, finiteness, or probability assumptions are needed here.
-/

noncomputable section

namespace LinearInputFutureObservation

/-- Same entire future stream of observations under a deterministic update. -/
def FutureEq {α ω : Type*} (K : α → ω) (U : α → α) (x y : α) : Prop :=
  ∀ t : ℕ, K (U^[t] x) = K (U^[t] y)

theorem future_refl {α ω : Type*} (K : α → ω) (U : α → α) (x : α) :
    FutureEq K U x x := by
  intro t
  rfl

theorem future_symm {α ω : Type*} {K : α → ω} {U : α → α}
    {x y : α} (h : FutureEq K U x y) : FutureEq K U y x := by
  intro t
  exact (h t).symm

theorem future_trans {α ω : Type*} {K : α → ω} {U : α → α}
    {x y z : α} (hxy : FutureEq K U x y) (hyz : FutureEq K U y z) :
    FutureEq K U x z := by
  intro t
  exact (hxy t).trans (hyz t)

/-- One transition preserves future-equivalence. -/
theorem future_step {α ω : Type*} {K : α → ω} {U : α → α}
    {x y : α} (h : FutureEq K U x y) :
    FutureEq K U (U x) (U y) := by
  intro t
  simpa only [Function.iterate_succ_apply'] using h (t + 1)

/-- The canonical equivalence relation on input states. -/
def futureSetoid {α ω : Type*} (K : α → ω) (U : α → α) : Setoid α where
  r := FutureEq K U
  iseqv := ⟨future_refl K U, (fun _ _ => future_symm), (fun _ _ _ => future_trans)⟩

/-- Minimal predictive states, defined as future-observation classes. -/
abbrev State {α ω : Type*} (K : α → ω) (U : α → α) : Type* :=
  Quotient (futureSetoid K U)

def encode {α ω : Type*} (K : α → ω) (U : α → α) (x : α) : State K U :=
  Quotient.mk (futureSetoid K U) x

/-- A quotient state has an unambiguous current observation. -/
def readout {α ω : Type*} (K : α → ω) (U : α → α) : State K U → ω :=
  Quotient.lift (fun x => K x) (by
    intro x y h
    simpa only [Function.iterate_zero, id_eq] using h 0)

/-- The deterministic update descends to the quotient, with no lost prediction. -/
def transition {α ω : Type*} (K : α → ω) (U : α → α) :
    State K U → State K U :=
  Quotient.lift (fun x => encode K U (U x)) (by
    intro x y h
    exact Quotient.sound (future_step h))

theorem readout_encode {α ω : Type*} (K : α → ω) (U : α → α) (x : α) :
    readout K U (encode K U x) = K x := rfl

theorem transition_encode {α ω : Type*} (K : α → ω) (U : α → α) (x : α) :
    transition K U (encode K U x) = encode K U (U x) := rfl

theorem encode_iff_future {α ω : Type*} {K : α → ω} {U : α → α}
    (x y : α) :
    encode K U x = encode K U y ↔ FutureEq K U x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- An exact predictive representation preserves the whole time trace. -/
theorem representation_iterate {α β : Type*}
    (U : α → α) (V : β → β) (f : α → β)
    (hf : ∀ x, f (U x) = V (f x)) (t : ℕ) (x : α) :
    f (U^[t] x) = V^[t] (f x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    calc
      f (U^[t + 1] x) = f (U^[t] (U x)) := by rw [Function.iterate_succ_apply']
      _ = V^[t] (f (U x)) := ih (U x)
      _ = V^[t] (V (f x)) := by rw [hf x]
      _ = V^[t + 1] (f x) := by rw [Function.iterate_succ_apply']

/-- Any two states merged by a correct deterministic representation
must already be future-equivalent. -/
theorem predictive_kernel_sub {α β ω : Type*}
    (K : α → ω) (U : α → α)
    (f : α → β) (V : β → β) (out : β → ω)
    (hout : ∀ x, out (f x) = K x)
    (hstep : ∀ x, f (U x) = V (f x))
    {x y : α} (hxy : f x = f y) : FutureEq K U x y := by
  intro t
  calc
    K (U^[t] x) = out (f (U^[t] x)) := (hout _).symm
    _ = out (V^[t] (f x)) :=
      congrArg out (representation_iterate U V f hstep t x)
    _ = out (V^[t] (f y)) := by rw [hxy]
    _ = out (f (U^[t] y)) :=
      congrArg out (representation_iterate U V f hstep t y).symm
    _ = K (U^[t] y) := hout _

/-- The canonical quotient never distinguishes more pairs than any exact
predictive representation. -/
theorem predictive_minimal {α β ω : Type*}
    (K : α → ω) (U : α → α)
    (f : α → β) (V : β → β) (out : β → ω)
    (hout : ∀ x, out (f x) = K x)
    (hstep : ∀ x, f (U x) = V (f x))
    {x y : α} (hxy : f x = f y) :
    encode K U x = encode K U y := by
  exact (encode_iff_future x y).2
    (predictive_kernel_sub K U f V out hout hstep hxy)

/-- Any surjective predictive representation maps onto the canonical one. -/
noncomputable def factor {α β ω : Type*}
    (K : α → ω) (U : α → α)
    (f : α → β) (hf : Function.Surjective f) :
    β → State K U := fun b => encode K U (Classical.choose (hf b))

theorem factor_encode {α β ω : Type*}
    (K : α → ω) (U : α → α)
    (f : α → β) (V : β → β) (out : β → ω)
    (hf : Function.Surjective f)
    (hout : ∀ x, out (f x) = K x)
    (hstep : ∀ x, f (U x) = V (f x)) (x : α) :
    factor K U f hf (f x) = encode K U x := by
  apply predictive_minimal K U f V out hout hstep
  exact Classical.choose_spec (hf (f x))

theorem factor_surjective {α β ω : Type*}
    (K : α → ω) (U : α → α)
    (f : α → β) (V : β → β) (out : β → ω)
    (hf : Function.Surjective f)
    (hout : ∀ x, out (f x) = K x)
    (hstep : ∀ x, f (U x) = V (f x)) :
    Function.Surjective (factor K U f hf) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
      exact ⟨f x, factor_encode K U f V out hf hout hstep x⟩

/-- If a symmetry commutes with U, then every future U-iterate commutes with it. -/
theorem commute_iterates {α : Type*} (U M : α → α)
    (h : ∀ x, U (M x) = M (U x)) (t : ℕ) (x : α) :
    U^[t] (M x) = M (U^[t] x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    calc
      U^[t + 1] (M x) = U^[t] (U (M x)) := by rw [Function.iterate_succ_apply']
      _ = U^[t] (M (U x)) := by rw [h x]
      _ = M (U^[t] (U x)) := ih (U x)
      _ = M (U^[t + 1] x) := by rw [Function.iterate_succ_apply']

/-- An observation-invisible symmetry commutes with compression to
the future-minimal state. -/
theorem invisible_symmetry {α ω : Type*}
    (K : α → ω) (U M : α → α)
    (hM : ∀ x, U (M x) = M (U x))
    (hK : ∀ x, K (M x) = K x) (x : α) :
    encode K U (M x) = encode K U x := by
  apply (encode_iff_future (K := K) (U := U) (M x) x).2
  intro t
  calc
    K (U^[t] (M x)) = K (M (U^[t] x)) := by rw [commute_iterates U M hM t x]
    _ = K (U^[t] x) := hK _

end LinearInputFutureObservation
