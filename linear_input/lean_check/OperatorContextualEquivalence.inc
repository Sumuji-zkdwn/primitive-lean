/-!
# Contextual equivalence for finite operator programs

An operator word is a program. Two programs may be equal pointwise on
concrete states (SemEq) or merely induce the same predictive quotient
operation (ContextEq).

ContextEq is a two-sided congruence under program concatenation. It is
stronger than equality of immediate readouts: the whole future language
must remain indistinguishable after either program.

This module proves semantic soundness and contextual replacement for
arbitrary deterministic, total operators. It does not assume finite
states, action sets, or decidable program equivalence.
-/

noncomputable section

namespace LinearInputOperatorContexts

open LinearInputOperatorWords

/-- Concrete equality of two finite programs on every original state. -/
def SemEq {α ι : Type*} (step : ι → α → α)
    (w v : List ι) : Prop :=
  ∀ x : α, run step w x = run step v x

/-- Contextual equality means the programs induce the same predictive state. -/
def ContextEq {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (w v : List ι) : Prop :=
  ∀ x : α, WordEq K step (run step w x) (run step v x)

theorem sem_refl {α ι : Type*} (step : ι → α → α) (w : List ι) :
    SemEq step w w := by
  intro x
  rfl

theorem sem_symm {α ι : Type*} {step : ι → α → α}
    {w v : List ι} (h : SemEq step w v) : SemEq step v w := by
  intro x
  exact (h x).symm

theorem sem_trans {α ι : Type*} {step : ι → α → α}
    {w v z : List ι} (hwv : SemEq step w v)
    (hvz : SemEq step v z) : SemEq step w z := by
  intro x
  exact (hwv x).trans (hvz x)

theorem sem_append_left {α ι : Type*}
    (step : ι → α → α) (w v pre : List ι)
    (h : SemEq step w v) :
    SemEq step (pre ++ w) (pre ++ v) := by
  intro x
  rw [run_append, run_append]
  exact h (run step pre x)

theorem sem_append_right {α ι : Type*}
    (step : ι → α → α) (w v suffix : List ι)
    (h : SemEq step w v) :
    SemEq step (w ++ suffix) (v ++ suffix) := by
  intro x
  rw [run_append, run_append, h x]

theorem sem_context {α ι : Type*}
    (step : ι → α → α) (w v pre suffix : List ι)
    (h : SemEq step w v) :
    SemEq step (pre ++ w ++ suffix) (pre ++ v ++ suffix) := by
  exact sem_append_right step _ _ suffix
    (sem_append_left step w v pre h)

theorem sem_empty_identity {α ι : Type*}
    (step : ι → α → α) (w : List ι)
    (h : ∀ x, run step w x = x) : SemEq step w [] := by
  intro x
  simpa only [run_nil] using h x

theorem sem_from_pointwise {α ι : Type*}
    (step : ι → α → α) (w v : List ι)
    (h : run step w = run step v) : SemEq step w v := by
  intro x
  exact congrFun h x

theorem sem_to_pointwise {α ι : Type*}
    (step : ι → α → α) (w v : List ι)
    (h : SemEq step w v) : run step w = run step v := by
  funext x
  exact h x

/-- The semantic congruence can be quotiented without a finite-state hypothesis. -/
def semSetoid {α ι : Type*}
    (step : ι → α → α) : Setoid (List ι) where
  r := SemEq step
  iseqv := ⟨sem_refl step, (fun h => sem_symm h),
    (fun h1 h2 => sem_trans h1 h2)⟩

theorem context_refl {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (w : List ι) :
    ContextEq K step w w := by
  intro x
  exact word_refl K step _

theorem context_symm {α ω ι : Type*}
    {K : α → ω} {step : ι → α → α}
    {w v : List ι} (h : ContextEq K step w v) :
    ContextEq K step v w := by
  intro x
  exact word_symm (h x)

theorem context_trans {α ω ι : Type*}
    {K : α → ω} {step : ι → α → α}
    {w v z : List ι} (hwv : ContextEq K step w v)
    (hvz : ContextEq K step v z) :
    ContextEq K step w z := by
  intro x
  exact word_trans (hwv x) (hvz x)

theorem sem_implies_context {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    {w v : List ι} (h : SemEq step w v) :
    ContextEq K step w v := by
  intro x
  rw [h x]
  exact word_refl K step _

theorem context_append_left {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (w v pre : List ι) (h : ContextEq K step w v) :
    ContextEq K step (pre ++ w) (pre ++ v) := by
  intro x
  rw [run_append, run_append]
  exact h (run step pre x)

theorem context_append_right {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (w v suffix : List ι) (h : ContextEq K step w v) :
    ContextEq K step (w ++ suffix) (v ++ suffix) := by
  intro x
  rw [run_append, run_append]
  exact word_run (h x) suffix

/-- Arbitrary replacement of a subprogram inside any sequential context. -/
theorem context_replacement {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (pre w v suffix : List ι) (h : ContextEq K step w v) :
    ContextEq K step (pre ++ w ++ suffix)
      (pre ++ v ++ suffix) := by
  exact context_append_right K step _ _ suffix
    (context_append_left K step w v pre h)

/-- Context equivalence is equality of the induced quotient programs. -/
theorem context_iff_quotient {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (w v : List ι) :
    ContextEq K step w v ↔
      ∀ x, encode K step (run step w x) =
        encode K step (run step v x) := by
  constructor
  · intro h x
    exact (encode_eq_iff K step _ _).2 (h x)
  · intro h x
    exact (encode_eq_iff K step _ _).1 (h x)

/-- Contextually equal programs agree on the immediate observation. -/
theorem context_now {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    {w v : List ι} (h : ContextEq K step w v)
    (x : α) :
    K (run step w x) = K (run step v x) :=
  word_now (h x)

def contextSetoid {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Setoid (List ι) where
  r := ContextEq K step
  iseqv := ⟨context_refl K step, (fun h => context_symm h),
    (fun h1 h2 => context_trans h1 h2)⟩

/-- Every word is contextual with itself, including concatenated generations. -/
theorem context_append_self {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (w v : List ι) :
    ContextEq K step (w ++ v) (w ++ v) :=
  context_refl K step _

/-- A predictive quotient identifies contextually equivalent actions. -/
theorem context_transition_sound {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (w v : List ι) (h : ContextEq K step w v)
    (x : α) :
    encode K step (run step w x) =
      encode K step (run step v x) :=
  (context_iff_quotient K step w v).1 h x

/-- If an observer is injective, contextual and concrete equality coincide. -/
theorem context_iff_sem_of_injective {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (hK : Function.Injective K) (w v : List ι) :
    ContextEq K step w v ↔ SemEq step w v := by
  constructor
  · intro h x
    exact hK (context_now K step h x)
  · exact sem_implies_context K step

/-- Refining the observer can only make program-context equality stricter. -/
theorem context_pair_implies_first {α ω ν ι : Type*}
    (K : α → ω) (L : α → ν) (step : ι → α → α)
    {w v : List ι}
    (h : ContextEq (fun x => (K x, L x)) step w v) :
    ContextEq K step w v := by
  intro x
  exact ((pair_observation K L step _ _).1 (h x)).1

theorem context_pair_implies_second {α ω ν ι : Type*}
    (K : α → ω) (L : α → ν) (step : ι → α → α)
    {w v : List ι}
    (h : ContextEq (fun x => (K x, L x)) step w v) :
    ContextEq L step w v := by
  intro x
  exact ((pair_observation K L step _ _).1 (h x)).2

theorem context_pair_iff {α ω ν ι : Type*}
    (K : α → ω) (L : α → ν) (step : ι → α → α)
    (w v : List ι) :
    ContextEq (fun x => (K x, L x)) step w v ↔
      ContextEq K step w v ∧ ContextEq L step w v := by
  constructor
  · intro h
    exact ⟨context_pair_implies_first K L step h,
      context_pair_implies_second K L step h⟩
  · rintro ⟨hK, hL⟩ x
    exact (pair_observation K L step _ _).2 ⟨hK x, hL x⟩

theorem context_postprocess {α ω ν ι : Type*}
    (K : α → ω) (f : ω → ν) (step : ι → α → α)
    {w v : List ι} (h : ContextEq K step w v) :
    ContextEq (fun x => f (K x)) step w v := by
  intro x
  exact postprocess K f step (h x)

/-- Syntactically generated words have the same concrete execution. -/
theorem compiled_word_semantics {α ι κ : Type*}
    (step : ι → α → α) (code : κ → List ι)
    (word : List κ) (x : α) :
    run (generated step code) word x =
      run step (compile code word) x :=
  run_generated step code word x

end LinearInputOperatorContexts
