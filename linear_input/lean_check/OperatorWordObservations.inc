/-!
# Observation equivalence for generated operator words

Unlike the single-transition future kernel, this construction observes
every finite sequence of actions drawn from an arbitrary operator alphabet.

The central limitation theorem states that a new operator vocabulary made
only by concatenating words in the old vocabulary cannot distinguish any
pair of states that the old vocabulary could not distinguish. An exact
counterexample shows that an independent new transition may do so.

These are algebraic/observational results. They do not claim that arbitrary
computable programs are compositional words, nor that operator synthesis
creates information in a physical system.
-/

noncomputable section

namespace LinearInputOperatorWords

/-- Sequentially apply the actions in a finite word, from left to right. -/
def run {α ι : Type*} (step : ι → α → α) : List ι → α → α
  | [], x => x
  | i :: word, x => run step word (step i x)

theorem run_nil {α ι : Type*} (step : ι → α → α) (x : α) :
    run step [] x = x := rfl

theorem run_cons {α ι : Type*} (step : ι → α → α)
    (i : ι) (word : List ι) (x : α) :
    run step (i :: word) x = run step word (step i x) := rfl

/-- Operator-word concatenation is sequential composition. -/
theorem run_append {α ι : Type*} (step : ι → α → α)
    (word tail : List ι) (x : α) :
    run step (word ++ tail) x = run step tail (run step word x) := by
  induction word generalizing x with
  | nil => rfl
  | cons i word ih =>
      change run step (word ++ tail) (step i x) =
        run step tail (run step word (step i x))
      exact ih (step i x)

/-- Two states are indistinguishable by every finite operator word. -/
def WordEq {α ω ι : Type*} (K : α → ω) (step : ι → α → α)
    (x y : α) : Prop :=
  ∀ word : List ι, K (run step word x) = K (run step word y)

theorem word_refl {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (x : α) : WordEq K step x x := by
  intro word
  rfl

theorem word_symm {α ω ι : Type*} {K : α → ω}
    {step : ι → α → α} {x y : α}
    (h : WordEq K step x y) : WordEq K step y x := by
  intro word
  exact (h word).symm

theorem word_trans {α ω ι : Type*} {K : α → ω}
    {step : ι → α → α} {x y z : α}
    (hxy : WordEq K step x y) (hyz : WordEq K step y z) :
    WordEq K step x z := by
  intro word
  exact (hxy word).trans (hyz word)

/-- Indistinguishable words already agree before any action. -/
theorem word_now {α ω ι : Type*} {K : α → ω}
    {step : ι → α → α} {x y : α}
    (h : WordEq K step x y) : K x = K y := by
  simpa [run] using h []

/-- Every primitive operator preserves full word equivalence. -/
theorem word_step {α ω ι : Type*} {K : α → ω}
    {step : ι → α → α} {x y : α}
    (h : WordEq K step x y) (i : ι) :
    WordEq K step (step i x) (step i y) := by
  intro word
  simpa [run] using h (i :: word)

/-- The same is true for any composite operator. -/
theorem word_run {α ω ι : Type*} {K : α → ω}
    {step : ι → α → α} {x y : α}
    (h : WordEq K step x y) (word : List ι) :
    WordEq K step (run step word x) (run step word y) := by
  intro tail
  calc
    K (run step tail (run step word x)) =
        K (run step (word ++ tail) x) :=
      congrArg K (run_append step word tail x).symm
    _ = K (run step (word ++ tail) y) := h (word ++ tail)
    _ = K (run step tail (run step word y)) :=
      congrArg K (run_append step word tail y)

def wordSetoid {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) : Setoid α where
  r := WordEq K step
  iseqv := ⟨(fun x => word_refl K step x),
    (fun h => word_symm h),
    (fun hxy hyz => word_trans hxy hyz)⟩

/-- Predictive states for the entire operator language. -/
abbrev State {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) := Quotient (wordSetoid K step)

def encode {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (x : α) : State K step :=
  Quotient.mk (wordSetoid K step) x

def readout {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) : State K step → ω :=
  Quotient.lift K (by
    intro x y h
    exact word_now h)

def transition {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (i : ι) : State K step → State K step :=
  Quotient.lift (fun x => encode K step (step i x)) (by
    intro x y h
    exact Quotient.sound (word_step h i))

theorem readout_encode {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (x : α) :
    readout K step (encode K step x) = K x := rfl

theorem transition_encode {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (i : ι) (x : α) :
    transition K step i (encode K step x) =
      encode K step (step i x) := rfl

theorem encode_eq_iff {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (x y : α) :
    encode K step x = encode K step y ↔ WordEq K step x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Combining two readout channels intersects their indistinguishability. -/
theorem pair_observation {α ω ν ι : Type*}
    (K : α → ω) (L : α → ν) (step : ι → α → α) (x y : α) :
    WordEq (fun a => (K a, L a)) step x y ↔
      WordEq K step x y ∧ WordEq L step x y := by
  constructor
  · intro h
    exact ⟨(fun word => congrArg Prod.fst (h word)),
      (fun word => congrArg Prod.snd (h word))⟩
  · rintro ⟨hK, hL⟩ word
    exact Prod.ext (hK word) (hL word)

/-- Post-processing readouts cannot create new state distinctions. -/
theorem postprocess {α ω ν ι : Type*}
    (K : α → ω) (f : ω → ν) (step : ι → α → α)
    {x y : α} (h : WordEq K step x y) :
    WordEq (fun a => f (K a)) step x y := by
  intro word
  exact congrArg f (h word)

/-- Compile each symbol of a new vocabulary to an old operator word. -/
def compile {ι κ : Type*} (code : κ → List ι) (word : List κ) :
    List ι := word.flatMap code

/-- Execute a newly named operator by running its old-word definition. -/
def generated {α ι κ : Type*} (step : ι → α → α)
    (code : κ → List ι) : κ → α → α :=
  fun j => run step (code j)

theorem compile_cons {ι κ : Type*} (code : κ → List ι)
    (j : κ) (word : List κ) :
    compile code (j :: word) = code j ++ compile code word := rfl

/-- Compiling a word and executing it have exactly the same semantics. -/
theorem run_generated {α ι κ : Type*} (step : ι → α → α)
    (code : κ → List ι) (word : List κ) (x : α) :
    run (generated step code) word x =
      run step (compile code word) x := by
  induction word generalizing x with
  | nil => rfl
  | cons j word ih =>
      change run (generated step code) word (run step (code j) x) =
        run step (code j ++ compile code word) x
      rw [ih (run step (code j) x), run_append]

/-- Renaming or composing old operators cannot increase distinguishability. -/
theorem generated_no_new_distinctions {α ω ι κ : Type*}
    (K : α → ω) (step : ι → α → α) (code : κ → List ι)
    {x y : α} (h : WordEq K step x y) :
    WordEq K (generated step code) x y := by
  intro word
  rw [run_generated step code word x, run_generated step code word y]
  exact h (compile code word)

/-- A vocabulary containing each old letter as a singleton has the same kernel. -/
theorem compile_map_singletons {ι κ : Type*}
    (code : κ → List ι) (embed : ι → κ)
    (he : ∀ i, code (embed i) = [i]) (word : List ι) :
    compile code (word.map embed) = word := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change code (embed i) ++ compile code (word.map embed) = i :: word
      rw [he i, ih]
      rfl

theorem generated_exact_of_singletons {α ω ι κ : Type*}
    (K : α → ω) (step : ι → α → α) (code : κ → List ι)
    (embed : ι → κ) (he : ∀ i, code (embed i) = [i])
    (x y : α) :
    WordEq K (generated step code) x y ↔ WordEq K step x y := by
  constructor
  · intro h word
    have hw := h (word.map embed)
    rw [run_generated step code (word.map embed) x,
        run_generated step code (word.map embed) y,
        compile_map_singletons code embed he word] at hw
    exact hw
  · exact generated_no_new_distinctions K step code

/-- A transition family respects the readout fibers one action at a time. -/
def Respects {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) : Prop :=
  ∀ i x y, K x = K y → K (step i x) = K (step i y)

theorem respects_implies_now_complete {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (hr : Respects K step) {x y : α} (hxy : K x = K y) :
    WordEq K step x y := by
  have hrun : ∀ word : List ι, ∀ a b : α, K a = K b →
      K (run step word a) = K (run step word b) := by
    intro word
    induction word with
    | nil =>
        intro a b hab
        exact hab
    | cons i word ih =>
        intro a b hab
        change K (run step word (step i a)) =
          K (run step word (step i b))
        exact ih (step i a) (step i b) (hr i a b hab)
  intro word
  exact hrun word x y hxy

/-- Present readout suffices for every word iff all actions respect its fibers. -/
theorem respects_iff_now_complete {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Respects K step ↔
      ∀ x y, WordEq K step x y ↔ K x = K y := by
  constructor
  · intro hr x y
    exact ⟨word_now, respects_implies_now_complete K step hr⟩
  · intro hall i x y hxy
    have hs : WordEq K step x y := (hall x y).2 hxy
    simpa [run] using hs [i]

/-- Exact simulations preserve the observation of every operator word. -/
theorem representation_run {α β ι : Type*}
    (step : ι → α → α) (update : ι → β → β)
    (f : α → β) (hf : ∀ i x, f (step i x) = update i (f x))
    (word : List ι) (x : α) :
    f (run step word x) = run update word (f x) := by
  induction word generalizing x with
  | nil => rfl
  | cons i word ih =>
      change f (run step word (step i x)) =
        run update word (update i (f x))
      calc
        f (run step word (step i x)) =
            run update word (f (step i x)) := ih (step i x)
        _ = run update word (update i (f x)) := by rw [hf i x]

/-- State simulations preserve the entire word kernel exactly on represented states. -/
theorem representation_word_eq {α β ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (f : α → β) (update : ι → β → β) (out : β → ω)
    (hout : ∀ x, out (f x) = K x)
    (hf : ∀ i x, f (step i x) = update i (f x))
    (x y : α) :
    WordEq K step x y ↔ WordEq out update (f x) (f y) := by
  constructor
  · intro h word
    calc
      out (run update word (f x)) = out (f (run step word x)) :=
        congrArg out (representation_run step update f hf word x).symm
      _ = K (run step word x) := hout _
      _ = K (run step word y) := h word
      _ = out (f (run step word y)) := (hout _).symm
      _ = out (run update word (f y)) :=
        congrArg out (representation_run step update f hf word y)
  · intro h word
    calc
      K (run step word x) = out (f (run step word x)) := (hout _).symm
      _ = out (run update word (f x)) :=
        congrArg out (representation_run step update f hf word x)
      _ = out (run update word (f y)) := h word
      _ = out (f (run step word y)) :=
        congrArg out (representation_run step update f hf word y).symm
      _ = K (run step word y) := hout _

/-- Every exact representation factors pairwise through the canonical quotient. -/
theorem predictive_minimal {α β ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (f : α → β) (update : ι → β → β) (out : β → ω)
    (hout : ∀ x, out (f x) = K x)
    (hf : ∀ i x, f (step i x) = update i (f x))
    {x y : α} (hxy : f x = f y) :
    encode K step x = encode K step y := by
  apply (encode_eq_iff K step x y).2
  exact (representation_word_eq K step f update out hout hf x y).2
    (by rw [hxy])

/-- A small witness where an independent action reveals a hidden distinction. -/
def exampleK (x : Fin 3) : Fin 2 := if x = 2 then 1 else 0

def baseStep : Unit → Fin 3 → Fin 3 := fun _ x => x

def extendedStep : Bool → Fin 3 → Fin 3 :=
  fun b x => if b then (if x = 1 then 2 else x) else x

theorem run_base (word : List Unit) (x : Fin 3) :
    run baseStep word x = x := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change run baseStep word x = x
      exact ih

theorem base_cannot_distinguish :
    WordEq exampleK baseStep (0 : Fin 3) (1 : Fin 3) := by
  intro word
  rw [run_base, run_base]
  decide

theorem independent_action_distinguishes :
    ¬ WordEq exampleK extendedStep (0 : Fin 3) (1 : Fin 3) := by
  intro h
  have hneq : exampleK (run extendedStep [true] (0 : Fin 3)) ≠
      exampleK (run extendedStep [true] (1 : Fin 3)) := by decide
  exact hneq (h [true])

/-- No dictionary of old words can reproduce the new vocabulary's kernel. -/
theorem independent_not_generated (code : Bool → List Unit) :
    ¬ (∀ x y : Fin 3,
      WordEq exampleK (generated baseStep code) x y ↔
        WordEq exampleK extendedStep x y) := by
  intro h
  have hbase : WordEq exampleK (generated baseStep code) 0 1 :=
    generated_no_new_distinctions exampleK baseStep code base_cannot_distinguish
  exact independent_action_distinguishes ((h 0 1).mp hbase)

end LinearInputOperatorWords
