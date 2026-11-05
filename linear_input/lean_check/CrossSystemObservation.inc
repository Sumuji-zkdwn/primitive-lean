/-!
# Exact observational bridges between different operator systems

The two systems can have unrelated state spaces but share an action alphabet
and an output space. CrossTrace is equality of all finite observable traces;
CrossBisim is a relation respected by current observations and each action.

A state map only produces a sound map between predictive quotients when its
outputs and its dynamics commute. Surjectivity/injectivity of the induced map
have distinct guarantees. A finite Bool-pair example distinguishes a
valid loss of latent state from an impossible, dynamics-breaking forgetting.

This is a general structural tool, not a formalization of modularity of an
elliptic curve or an assertion that a finite trace comparison proves it.
-/

noncomputable section

namespace LinearInputCrossSystemObservation

open LinearInputOperatorWords

/-- Equal output traces for every word in a common operator language. -/
def CrossTrace {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (x : α) (y : β) : Prop :=
  ∀ word : List ι, K (run stepA word x) = L (run stepB word y)

/-- Cross-system observational bisimulation, without assuming a state map. -/
def CrossBisim {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (R : α → β → Prop) : Prop :=
  ∀ x y, R x y →
    K x = L y ∧ (∀ i, R (stepA i x) (stepB i y))

/-- Every full trace relation agrees on the present observation. -/
theorem crossTrace_now {α β ω ι : Type*}
    {K : α → ω} {L : β → ω}
    {stepA : ι → α → α} {stepB : ι → β → β}
    {x : α} {y : β}
    (h : CrossTrace K L stepA stepB x y) : K x = L y := by
  simpa only [CrossTrace, run_nil] using h []

/-- A matched action leaves the two traces observationally matched. -/
theorem crossTrace_step {α β ω ι : Type*}
    {K : α → ω} {L : β → ω}
    {stepA : ι → α → α} {stepB : ι → β → β}
    {x : α} {y : β}
    (h : CrossTrace K L stepA stepB x y) (i : ι) :
    CrossTrace K L stepA stepB (stepA i x) (stepB i y) := by
  intro word
  exact h (i :: word)

/-- Equal complete traces form a cross-system bisimulation. -/
theorem trace_is_bisim {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β) :
    CrossBisim K L stepA stepB (CrossTrace K L stepA stepB) := by
  intro x y h
  exact ⟨crossTrace_now h, fun i => crossTrace_step h i⟩

/-- A cross-bisimulation is preserved under every finite operator word. -/
theorem bisim_run {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (R : α → β → Prop) (hR : CrossBisim K L stepA stepB R)
    (word : List ι) {x : α} {y : β} (hxy : R x y) :
    R (run stepA word x) (run stepB word y) := by
  induction word generalizing x y with
  | nil => simpa [run] using hxy
  | cons i rest ih => exact ih ((hR x y hxy).2 i)

/-- Related states under any cross-bisimulation have matching full traces. -/
theorem bisim_sub_trace {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (R : α → β → Prop) (hR : CrossBisim K L stepA stepB R)
    {x : α} {y : β} (hxy : R x y) :
    CrossTrace K L stepA stepB x y := by
  intro word
  exact (hR _ _ (bisim_run K L stepA stepB R hR word hxy)).1

/-- Equality of every finite trace is the greatest cross-bisimulation. -/
theorem greatest_cross_bisim {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (x : α) (y : β) :
    CrossTrace K L stepA stepB x y ↔
      ∃ R : α → β → Prop, CrossBisim K L stepA stepB R ∧ R x y := by
  constructor
  · intro h
    exact ⟨CrossTrace K L stepA stepB,
      trace_is_bisim K L stepA stepB, h⟩
  · rintro ⟨R, hR, hxy⟩
    exact bisim_sub_trace K L stepA stepB R hR hxy

/-- An exact directed connection preserves outputs and commutes with actions.
The state map is not required to be injective or surjective. -/
def ExactBridge {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) : Prop :=
  (∀ x, L (φ x) = K x) ∧
    (∀ i x, φ (stepA i x) = stepB i (φ x))

/-- A commuting bridge also commutes with every composed operator word. -/
theorem bridge_run {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ)
    (word : List ι) (x : α) :
    φ (run stepA word x) = run stepB word (φ x) := by
  induction word generalizing x with
  | nil => rfl
  | cons i rest ih =>
    change φ (run stepA rest (stepA i x)) =
      run stepB rest (stepB i (φ x))
    rw [ih (stepA i x), h.2 i x]

/-- An exact bridge yields matching observations at every finite word. -/
theorem bridge_trace {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ) (x : α) :
    CrossTrace K L stepA stepB x (φ x) := by
  intro word
  calc
    K (run stepA word x) = L (φ (run stepA word x)) := (h.1 _).symm
    _ = L (run stepB word (φ x)) :=
      congrArg L (bridge_run K L stepA stepB φ h word x)

/-- A bridge cannot split a class that the source language cannot distinguish. -/
theorem bridge_preserves_wordEq {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ)
    {x y : α} (hxy : WordEq K stepA x y) :
    WordEq L stepB (φ x) (φ y) := by
  intro word
  calc
    L (run stepB word (φ x)) = K (run stepA word x) :=
      (bridge_trace K L stepA stepB φ h x word).symm
    _ = K (run stepA word y) := hxy word
    _ = L (run stepB word (φ y)) :=
      bridge_trace K L stepA stepB φ h y word

/-- Exact state bridges also reflect full trace equality: no observable
source distinctions are erased by an exact bridge. -/
theorem bridge_reflects_wordEq {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ)
    {x y : α} (hxy : WordEq L stepB (φ x) (φ y)) :
    WordEq K stepA x y := by
  intro word
  calc
    K (run stepA word x) = L (run stepB word (φ x)) :=
      bridge_trace K L stepA stepB φ h x word
    _ = L (run stepB word (φ y)) := hxy word
    _ = K (run stepA word y) :=
      (bridge_trace K L stepA stepB φ h y word).symm

/-- An exact bridge descends to a map between predictive quotient spaces. -/
def predictiveMap {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ) :
    State K stepA → State L stepB :=
  Quotient.lift (fun x => encode L stepB (φ x)) (by
    intro x y hxy
    exact Quotient.sound (bridge_preserves_wordEq K L stepA stepB φ h hxy))

/-- Quotienting after bridging equals bridging after quotienting. -/
theorem predictiveMap_encode {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ) (x : α) :
    predictiveMap K L stepA stepB φ h (encode K stepA x) =
      encode L stepB (φ x) := rfl

/-- Predictive-quotient output is preserved by an exact bridge. -/
theorem predictiveMap_output {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ)
    (q : State K stepA) :
    readout L stepB (predictiveMap K L stepA stepB φ h q) =
      readout K stepA q := by
  induction q using Quotient.inductionOn with
  | _ x => exact h.1 x

/-- Predictive-quotient transitions commute with an exact bridge. -/
theorem predictiveMap_step {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ)
    (i : ι) (q : State K stepA) :
    predictiveMap K L stepA stepB φ h (transition K stepA i q) =
      transition L stepB i (predictiveMap K L stepA stepB φ h q) := by
  induction q using Quotient.inductionOn with
  | _ x =>
    change encode L stepB (φ (stepA i x)) =
      encode L stepB (stepB i (φ x))
    exact congrArg (encode L stepB) (h.2 i x)

/-- An onto state bridge is onto on predictive quotients. -/
theorem predictiveMap_surjective {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ)
    (hs : Function.Surjective φ) :
    Function.Surjective (predictiveMap K L stepA stepB φ h) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ y =>
    obtain ⟨x, hx⟩ := hs y
    refine ⟨encode K stepA x, ?_⟩
    change encode L stepB (φ x) = encode L stepB y
    exact congrArg (encode L stepB) hx

/-- Injectivity of the quotient bridge requires reflection of trace equality. -/
theorem predictiveMap_injective_of_reflects {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ)
    (hr : ∀ x y, WordEq L stepB (φ x) (φ y) → WordEq K stepA x y) :
    Function.Injective (predictiveMap K L stepA stepB φ h) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      apply (encode_eq_iff K stepA x y).2
      apply hr x y
      apply (encode_eq_iff L stepB (φ x) (φ y)).1
      exact hqr

/-- Every exact state bridge is injective on predictive quotients,
even when the original state map is many-to-one. -/
theorem predictiveMap_injective {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ) :
    Function.Injective (predictiveMap K L stepA stepB φ h) :=
  predictiveMap_injective_of_reflects K L stepA stepB φ h
    (fun x y hxy => bridge_reflects_wordEq K L stepA stepB φ h hxy)

/-- Surjectivity plus reflection gives an isomorphism of predictive states. -/
theorem predictiveMap_bijective {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ)
    (hs : Function.Surjective φ)
    (hr : ∀ x y, WordEq L stepB (φ x) (φ y) → WordEq K stepA x y) :
    Function.Bijective (predictiveMap K L stepA stepB φ h) :=
  ⟨predictiveMap_injective_of_reflects K L stepA stepB φ h hr,
    predictiveMap_surjective K L stepA stepB φ h hs⟩

/-- A surjective exact state bridge always induces a predictive-state
bijection, without needing injectivity on original states. -/
theorem predictiveMap_bijective_of_surjective {α β ω ι : Type*}
    (K : α → ω) (L : β → ω)
    (stepA : ι → α → α) (stepB : ι → β → β)
    (φ : α → β) (h : ExactBridge K L stepA stepB φ)
    (hs : Function.Surjective φ) :
    Function.Bijective (predictiveMap K L stepA stepB φ h) :=
  ⟨predictiveMap_injective K L stepA stepB φ h,
    predictiveMap_surjective K L stepA stepB φ h hs⟩

/-- Exact criterion: any fiber split by a successor obstructs all possible
transition structures on the forgotten state space. -/
theorem no_bridge_if_fiber_splits {α β ω ι : Type*}
    (K : α → ω) (L : β → ω) (stepA : ι → α → α)
    (φ : α → β) (i : ι) (x y : α)
    (hφ : φ x = φ y) (hnext : φ (stepA i x) ≠ φ (stepA i y))
    (stepB : ι → β → β) :
    ¬ ExactBridge K L stepA stepB φ := by
  intro h
  apply hnext
  calc
    φ (stepA i x) = stepB i (φ x) := h.2 i x
    _ = stepB i (φ y) := congrArg (stepB i) hφ
    _ = φ (stepA i y) := (h.2 i y).symm

/-- Forget the hidden second bit; reading the first bit still commutes with
operations that act only on the first bit. -/
def forgetSecond (x : Bool × Bool) : Bool := x.1

def pairOutput (x : Bool × Bool) : Bool := x.1

def flipFirst : Unit → Bool × Bool → Bool × Bool :=
  fun _ x => (Bool.not x.1, x.2)

def flipBit : Unit → Bool → Bool := fun _ b => Bool.not b

/-- A genuinely many-to-one state map can be an exact dynamical bridge. -/
theorem flip_bridge :
    ExactBridge pairOutput (fun b : Bool => b) flipFirst flipBit forgetSecond := by
  constructor
  · intro x
    rfl
  · intro i x
    rfl

theorem forgetSecond_surjective : Function.Surjective forgetSecond := by
  intro b
  exact ⟨(b, false), rfl⟩

/-- Although the raw states have lost a bit, their complete predictive
quotients remain in bijection for this exact bridge. -/
theorem flip_predictive_bijective :
    Function.Bijective
      (predictiveMap pairOutput (fun b : Bool => b)
        flipFirst flipBit forgetSecond flip_bridge) :=
  predictiveMap_bijective_of_surjective pairOutput (fun b : Bool => b)
    flipFirst flipBit forgetSecond flip_bridge forgetSecond_surjective

/-- A different action makes the previously hidden second bit observable. -/
def revealSecond : Unit → Bool × Bool → Bool × Bool :=
  fun _ x => (x.2, x.1)

/-- Present output matches after forgetting, but NO Bool transition can
reproduce the future observation of both original states. -/
theorem reveal_has_no_bridge (stepB : Unit → Bool → Bool) :
    ¬ ExactBridge pairOutput (fun b : Bool => b)
      revealSecond stepB forgetSecond := by
  have hφ : forgetSecond (false, false) = forgetSecond (false, true) := rfl
  have hnext :
      forgetSecond (revealSecond () (false, false)) ≠
        forgetSecond (revealSecond () (false, true)) := by decide
  exact no_bridge_if_fiber_splits pairOutput (fun b : Bool => b)
    revealSecond forgetSecond () (false, false) (false, true) hφ hnext stepB

end LinearInputCrossSystemObservation
