/-!
# Mono-eye composition versus predictive quotient (finite/open deterministic interface)

A product of two open eyes with independently addressable boundary inputs has
exactly the product of the two operator-word predictive kernels. If instead
each eye receives the *observable output* of its neighbor, local predictive
equivalence for every possible boundary input still implies global predictive
equivalence. The converse fails for a feedback connection unable to generate
all possible boundary inputs (explicit three-state example below).

The source uses the existing LinearInputOperatorWords WordEq/word_step/run
machinery. This is a state-machine bridge to ME-3/T9, not a theorem about
smooth Elastica curve gluing or an assertion of physical self-similarity.
-/

noncomputable section

namespace LinearInputMonoEyeComposition

open LinearInputOperatorWords

/-- Side-by-side open eyes with freely and independently supplied inputs. -/
def pairStep {α β ι κ : Type*} (stepA : ι → α → α) (stepB : κ → β → β) :
    (ι × κ) → (α × β) → (α × β) :=
  fun input state => (stepA input.1 state.1, stepB input.2 state.2)

def pairReadout {α β ω ν : Type*} (oa : α → ω) (ob : β → ν) :
    (α × β) → (ω × ν) :=
  fun state => (oa state.1, ob state.2)

/-- A combined operation word acts coordinatewise on its two projections. -/
theorem pair_run {α β ι κ : Type*}
    (stepA : ι → α → α) (stepB : κ → β → β)
    (word : List (ι × κ)) (state : α × β) :
    run (pairStep stepA stepB) word state =
      (run stepA (word.map Prod.fst) state.1,
       run stepB (word.map Prod.snd) state.2) := by
  induction word generalizing state with
  | nil => rfl
  | cons i tail ih =>
      change run (pairStep stepA stepB) tail (pairStep stepA stepB i state) =
        (run stepA (tail.map Prod.fst) (stepA i.1 state.1),
         run stepB (tail.map Prod.snd) (stepB i.2 state.2))
      simpa only [pairStep] using ih (pairStep stepA stepB i state)

/-- Full local predictive equivalence is *exactly* global predictive
    equivalence when both boundary controls are independently accessible.
    Nonempty input alphabets are expressed by the two chosen dummy symbols. -/
theorem pair_word_eq_iff {α β ι κ ω ν : Type*}
    (oa : α → ω) (ob : β → ν)
    (stepA : ι → α → α) (stepB : κ → β → β)
    (dummyA : ι) (dummyB : κ) (x y : α × β) :
    WordEq (pairReadout oa ob) (pairStep stepA stepB) x y ↔
      WordEq oa stepA x.1 y.1 ∧ WordEq ob stepB x.2 y.2 := by
  constructor
  · intro h
    constructor
    · intro word
      have hh := h (word.map (fun a => (a, dummyB)))
      rw [pair_run stepA stepB _ x, pair_run stepA stepB _ y] at hh
      have hf := congrArg Prod.fst hh
      simpa [pairReadout, List.map_map, Function.comp_def] using hf
    · intro word
      have hh := h (word.map (fun b => (dummyA, b)))
      rw [pair_run stepA stepB _ x, pair_run stepA stepB _ y] at hh
      have hs := congrArg Prod.snd hh
      simpa [pairReadout, List.map_map, Function.comp_def] using hs
  · rintro ⟨ha, hb⟩ word
    rw [pair_run stepA stepB word x, pair_run stepA stepB word y]
    exact Prod.ext (ha (word.map Prod.fst)) (hb (word.map Prod.snd))

/-- The natural map from raw joint states to the pair of local predictive
    quotient states. -/
def productEncode {α β ι κ ω ν : Type*}
    (oa : α → ω) (stepA : ι → α → α)
    (ob : β → ν) (stepB : κ → β → β) (state : α × β) :
    State oa stepA × State ob stepB :=
  (encode oa stepA state.1, encode ob stepB state.2)

/-- 'Quotient after composition = composition after quotient' as exact
    equality of equivalence kernels, with no arbitrary representative choice. -/
theorem product_encode_eq_iff {α β ι κ ω ν : Type*}
    (oa : α → ω) (stepA : ι → α → α)
    (ob : β → ν) (stepB : κ → β → β)
    (dummyA : ι) (dummyB : κ) (x y : α × β) :
    productEncode oa stepA ob stepB x = productEncode oa stepA ob stepB y ↔
      WordEq (pairReadout oa ob) (pairStep stepA stepB) x y := by
  constructor
  · intro h
    apply (pair_word_eq_iff oa ob stepA stepB dummyA dummyB x y).2
    exact ⟨(encode_eq_iff oa stepA x.1 y.1).1 (congrArg Prod.fst h),
      (encode_eq_iff ob stepB x.2 y.2).1 (congrArg Prod.snd h)⟩
  · intro h
    obtain ⟨ha, hb⟩ :=
      (pair_word_eq_iff oa ob stepA stepB dummyA dummyB x y).1 h
    exact Prod.ext ((encode_eq_iff oa stepA x.1 y.1).2 ha)
      ((encode_eq_iff ob stepB x.2 y.2).2 hb)

/-- Each pair of local quotient states has a representing joint state. -/
theorem product_encode_surjective {α β ι κ ω ν : Type*}
    (oa : α → ω) (stepA : ι → α → α)
    (ob : β → ν) (stepB : κ → β → β) :
    Function.Surjective (productEncode oa stepA ob stepB) := by
  rintro ⟨qA, qB⟩
  induction qA using Quotient.inductionOn with
  | _ a =>
      induction qB using Quotient.inductionOn with
      | _ b => exact ⟨(a, b), rfl⟩

/-- Boundary input of either eye is determined solely by the other eye's
    *public* readout. The private state never crosses the boundary. -/
def wiredStep {α β ι ω ν : Type*}
    (oa : α → ω) (ob : β → ν)
    (stepA : ι → ν → α → α) (stepB : ι → ω → β → β) :
    ι → (α × β) → (α × β) :=
  fun i p => (stepA i (ob p.2) p.1, stepB i (oa p.1) p.2)

def localStep {α ι ν : Type*} (step : ι → ν → α → α) :
    (ι × ν) → α → α :=
  fun input => step input.1 input.2

/-- Sound compositional quotienting for public-readout feedback.
    Each local WordEq quantifies over *all* potential boundary values.
    No claim of the converse is made. -/
theorem wired_word_sound {α β ι ω ν : Type*}
    (oa : α → ω) (ob : β → ν)
    (stepA : ι → ν → α → α) (stepB : ι → ω → β → β)
    (x y : α × β)
    (ha : WordEq oa (localStep stepA) x.1 y.1)
    (hb : WordEq ob (localStep stepB) x.2 y.2) :
    WordEq (pairReadout oa ob) (wiredStep oa ob stepA stepB) x y := by
  have invariant :
      ∀ word : List ι, ∀ p q : α × β,
        WordEq oa (localStep stepA) p.1 q.1 →
        WordEq ob (localStep stepB) p.2 q.2 →
        WordEq oa (localStep stepA)
          (run (wiredStep oa ob stepA stepB) word p).1
          (run (wiredStep oa ob stepA stepB) word q).1 ∧
        WordEq ob (localStep stepB)
          (run (wiredStep oa ob stepA stepB) word p).2
          (run (wiredStep oa ob stepA stepB) word q).2 := by
    intro word
    induction word with
    | nil =>
        intro p q hpa hpb
        exact ⟨hpa, hpb⟩
    | cons i tail ih =>
        intro p q hpa hpb
        have hobsA : oa p.1 = oa q.1 := word_now hpa
        have hobsB : ob p.2 = ob q.2 := word_now hpb
        have ha' : WordEq oa (localStep stepA)
            (stepA i (ob p.2) p.1) (stepA i (ob q.2) q.1) := by
          rw [hobsB]
          exact word_step hpa (i, ob q.2)
        have hb' : WordEq ob (localStep stepB)
            (stepB i (oa p.1) p.2) (stepB i (oa q.1) q.2) := by
          rw [hobsA]
          exact word_step hpb (i, oa q.1)
        change WordEq oa (localStep stepA)
            (run (wiredStep oa ob stepA stepB) tail (wiredStep oa ob stepA stepB i p)).1
            (run (wiredStep oa ob stepA stepB) tail (wiredStep oa ob stepA stepB i q)).1 ∧
          WordEq ob (localStep stepB)
            (run (wiredStep oa ob stepA stepB) tail (wiredStep oa ob stepA stepB i p)).2
            (run (wiredStep oa ob stepA stepB) tail (wiredStep oa ob stepA stepB i q)).2
        exact ih (wiredStep oa ob stepA stepB i p)
          (wiredStep oa ob stepA stepB i q) ha' hb'
  intro word
  have h := invariant word x y ha hb
  change
    (oa (run (wiredStep oa ob stepA stepB) word x).1,
     ob (run (wiredStep oa ob stepA stepB) word x).2) =
    (oa (run (wiredStep oa ob stepA stepB) word y).1,
     ob (run (wiredStep oa ob stepA stepB) word y).2)
  apply Prod.ext
  · exact word_now h.1
  · exact word_now h.2

/-- Finite counterexample: the neighbor stays false, so the local input true
    can never be presented in the wired system starting in this state. -/
def exampleOA (a : Fin 3) : Bool := a == 2

def exampleOB (b : Bool) : Bool := b

def exampleA (_ : Unit) (boundary : Bool) (a : Fin 3) : Fin 3 :=
  if boundary && a == 1 then 2 else a

def exampleB (_ : Unit) (_ : Bool) (_ : Bool) : Bool := false

theorem example_run_zero (word : List Unit) :
    run (wiredStep exampleOA exampleOB exampleA exampleB) word
      ((0 : Fin 3), false) = ((0 : Fin 3), false) := by
  induction word with
  | nil => rfl
  | cons i tail ih =>
      change run (wiredStep exampleOA exampleOB exampleA exampleB) tail
          (wiredStep exampleOA exampleOB exampleA exampleB i ((0 : Fin 3), false)) =
          ((0 : Fin 3), false)
      simpa [wiredStep, exampleA, exampleB, exampleOB] using ih

theorem example_run_one (word : List Unit) :
    run (wiredStep exampleOA exampleOB exampleA exampleB) word
      ((1 : Fin 3), false) = ((1 : Fin 3), false) := by
  induction word with
  | nil => rfl
  | cons i tail ih =>
      change run (wiredStep exampleOA exampleOB exampleA exampleB) tail
          (wiredStep exampleOA exampleOB exampleA exampleB i ((1 : Fin 3), false)) =
          ((1 : Fin 3), false)
      simpa [wiredStep, exampleA, exampleB, exampleOB] using ih

theorem example_global_equivalent :
    WordEq (pairReadout exampleOA exampleOB)
      (wiredStep exampleOA exampleOB exampleA exampleB)
      ((0 : Fin 3), false) ((1 : Fin 3), false) := by
  intro word
  rw [example_run_zero word, example_run_one word]
  rfl

theorem example_local_distinct :
    ¬ WordEq exampleOA (localStep exampleA) (0 : Fin 3) (1 : Fin 3) := by
  intro h
  have hh := h [((), true)]
  simp [run, localStep, exampleA, exampleOA] at hh

end LinearInputMonoEyeComposition
