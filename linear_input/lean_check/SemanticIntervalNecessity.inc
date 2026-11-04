/-!
# Interval preservation, local extinction, and forced operator novelty

Model scope: finite operator words acting on a fixed state space; at each
discrete prefix time k, a global state survives iff some local component
accepts it. The theorem does NOT assert that arbitrary finite local systems
must go extinct, or that a repair operator exists without an assumption.

A predicate invariant under every old primitive is an obstruction: when
all local systems at the terminal time reject states in that invariant
region, no old word can preserve global viability. Any viable extended
word must contain a fresh primitive. An explicit Fin 3 model realizes
survival with one fresh primitive and strict predictive-quotient splitting.

A second finite model shows that extinction of *one* local component alone
does not force novelty: another component can take over on the same state.
-/

noncomputable section

namespace LinearInputSemanticIntervals

open LinearInputOperatorWords
open LinearInputOperatorRefinement

/-- The global state survives when at least one local system accepts it. -/
def HasLocal {α σ : Type*}
    (alive : ℕ → σ → α → Prop) (time : ℕ) (x : α) : Prop :=
  ∃ loc, alive time loc x

/-- A word preserves some local witness at every prefix time. -/
def IntervalSurvival {α σ ι : Type*}
    (alive : ℕ → σ → α → Prop)
    (step : ι → α → α) (word : List ι) (x : α) : Prop :=
  ∀ k, k ≤ word.length →
    HasLocal alive k (run step (word.take k) x)

/-- Every primitive of the old language preserves the same region. -/
def OldInvariant {α ι : Type*}
    (region : α → Prop) (old : ι → α → α) : Prop :=
  ∀ i x, region x → region (old i x)

/-- At time n, every local component is extinct inside the old region. -/
def TerminalExtinction {α σ : Type*}
    (alive : ℕ → σ → α → Prop)
    (region : α → Prop) (n : ℕ) : Prop :=
  ∀ x, region x → ∀ loc, ¬ alive n loc x

theorem interval_survival_end {α σ ι : Type*}
    (alive : ℕ → σ → α → Prop)
    (step : ι → α → α) (word : List ι) (x : α)
    (hs : IntervalSurvival alive step word x) :
    HasLocal alive word.length (run step word x) := by
  simpa only [List.take_length] using hs word.length (le_refl _)

theorem invariant_old_word {α ι : Type*}
    (region : α → Prop) (old : ι → α → α)
    (hi : OldInvariant region old)
    (word : List ι) (x : α) (hx : region x) :
    region (run old word x) := by
  induction word generalizing x with
  | nil => exact hx
  | cons i tail ih =>
      change region (run old tail (old i x))
      exact ih (old i x) (hi i x hx)

theorem invariant_word_without_new {α ι κ : Type*}
    (region : α → Prop) (old : ι → α → α)
    (fresh : κ → α → α) (hi : OldInvariant region old)
    (word : List (Sum ι κ)) (x : α) (hx : region x)
    (hn : ∀ j : κ, Sum.inr j ∉ word) :
    region (run (sumStep old fresh) word x) := by
  induction word generalizing x with
  | nil => exact hx
  | cons tag tail ih =>
      cases tag with
      | inl i =>
          have ht : ∀ j : κ, Sum.inr j ∉ tail := by
            intro j hj
            exact hn j (by simp [hj])
          change region (run (sumStep old fresh) tail (old i x))
          exact ih (old i x) (hi i x hx) ht
      | inr j =>
          exact False.elim (hn j (by simp))

theorem terminal_extinction_blocks {α σ : Type*}
    (alive : ℕ → σ → α → Prop)
    (region : α → Prop) (n : ℕ)
    (he : TerminalExtinction alive region n)
    (x : α) (hx : region x) :
    ¬ HasLocal alive n x := by
  rintro ⟨loc, hloc⟩
  exact he x hx loc hloc

/-- No finite old word achieves the terminal viability requirement. -/
theorem no_old_word_reaches_survival {α σ ι : Type*}
    (alive : ℕ → σ → α → Prop) (region : α → Prop)
    (old : ι → α → α) (n : ℕ) (start : α)
    (hi : OldInvariant region old) (hx : region start)
    (he : TerminalExtinction alive region n)
    (word : List ι) :
    ¬ HasLocal alive n (run old word start) := by
  exact terminal_extinction_blocks alive region n he _
    (invariant_old_word region old hi word start hx)

/-- If a complete interval survives, the successful extended word
must include at least one genuinely fresh alphabet symbol. -/
theorem interval_requires_new_symbol {α σ ι κ : Type*}
    (alive : ℕ → σ → α → Prop) (region : α → Prop)
    (old : ι → α → α) (fresh : κ → α → α)
    (n : ℕ) (start : α)
    (hi : OldInvariant region old) (hx : region start)
    (he : TerminalExtinction alive region n)
    (word : List (Sum ι κ))
    (hlen : word.length = n)
    (hs : IntervalSurvival alive (sumStep old fresh) word start) :
    ∃ j : κ, Sum.inr j ∈ word := by
  classical
  by_contra hnone
  have hn : ∀ j : κ, Sum.inr j ∉ word := by
    intro j hj
    exact hnone ⟨j, hj⟩
  have hp : region (run (sumStep old fresh) word start) :=
    invariant_word_without_new region old fresh hi word start hx hn
  have hend : HasLocal alive n (run (sumStep old fresh) word start) := by
    simpa [hlen] using interval_survival_end alive
      (sumStep old fresh) word start hs
  exact (terminal_extinction_blocks alive region n he _ hp) hend

/-- A viable repair state cannot be obtained by any old operator word. -/
theorem viable_repair_not_old_generated {α σ ι : Type*}
    (alive : ℕ → σ → α → Prop) (region : α → Prop)
    (old : ι → α → α) (n : ℕ) (start : α)
    (hi : OldInvariant region old) (hx : region start)
    (he : TerminalExtinction alive region n)
    (repair : α → α)
    (hr : HasLocal alive n (repair start)) :
    ∀ word : List ι, run old word start ≠ repair start := by
  intro word hEq
  have hp : region (repair start) := by
    simpa [hEq] using invariant_old_word region old hi word start hx
  exact (terminal_extinction_blocks alive region n he _ hp) hr

/-- A one-step repair retains viability on the full two-point interval. -/
theorem one_step_interval {α σ ι : Type*}
    (alive : ℕ → σ → α → Prop) (step : ι → α → α)
    (a : ι) (start : α)
    (hzero : HasLocal alive 0 start)
    (hone : HasLocal alive 1 (step a start)) :
    IntervalSurvival alive step [a] start := by
  intro k hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · simpa [run] using hzero
  · simpa [run] using hone

/-- The verified vocabulary-refinement theorem is compatible with the
separate viability obstruction: the new primitive may also split the
old predictive quotient. -/
theorem viable_and_strict_extension {α σ ω ι κ : Type*}
    (alive : ℕ → σ → α → Prop) (region : α → Prop)
    (K : α → ω) (old : ι → α → α)
    (fresh : κ → α → α) (j : κ) (start u v : α)
    (hi : OldInvariant region old) (hx : region start)
    (he : TerminalExtinction alive region 1)
    (hzero : HasLocal alive 0 start)
    (hone : HasLocal alive 1 (fresh j start))
    (hOld : WordEq K old u v)
    (hBreak : ¬ WordEq K old (fresh j u) (fresh j v)) :
    (∀ word : List ι, run old word start ≠ fresh j start) ∧
    IntervalSurvival alive (sumStep old fresh) [Sum.inr j] start ∧
    ¬ Function.Injective (forget K old fresh) := by
  refine ⟨?_, ?_, ?_⟩
  · exact viable_repair_not_old_generated alive region old 1 start
      hi hx he (fresh j) hone
  · exact one_step_interval alive (sumStep old fresh)
      (Sum.inr j) start hzero hone
  · exact forget_not_injective_of_instability
      K old fresh j u v hOld hBreak

/-- Three states, two local components; the old local component is
extinct at time 1 and the new one accepts only state 2. -/
def witnessAlive (t : ℕ) (loc : Fin 2) (x : Fin 3) : Prop :=
  (t = 0 ∧ loc = 0 ∧ x = 1) ∨
  (t = 1 ∧ loc = 1 ∧ x = 2)

def witnessRegion (x : Fin 3) : Prop := x ≠ 2

theorem witness_old_invariant :
    OldInvariant witnessRegion baseStep := by
  intro i x hx
  exact hx

theorem witness_terminal_extinct :
    TerminalExtinction witnessAlive witnessRegion 1 := by
  intro x hx loc hloc
  rcases hloc with h | h
  · have hz : (1 : ℕ) = 0 := h.1
    omega
  · exact hx h.2.2

theorem witness_start_alive :
    HasLocal witnessAlive 0 (1 : Fin 3) := by
  exact ⟨0, Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem witness_repair_alive :
    HasLocal witnessAlive 1 (witnessFresh () (1 : Fin 3)) := by
  refine ⟨1, Or.inr ⟨rfl, rfl, ?_⟩⟩
  decide

/-- Certified finite witness for novelty, interval survival, and a
strictly larger predictive meaning quotient. -/
theorem witness_forced_interval_and_refinement :
    (∀ word : List Unit,
      run baseStep word (1 : Fin 3) ≠ witnessFresh () 1) ∧
    IntervalSurvival witnessAlive
      (sumStep baseStep witnessFresh) [Sum.inr ()] (1 : Fin 3) ∧
    ¬ Function.Injective (forget exampleK baseStep witnessFresh) := by
  exact viable_and_strict_extension witnessAlive witnessRegion
    exampleK baseStep witnessFresh () 1 0 1
    witness_old_invariant (by decide) witness_terminal_extinct
    witness_start_alive witness_repair_alive
    witness_old_equiv (by
      intro h
      have hObs :
          exampleK (witnessFresh () (0 : Fin 3)) =
            exampleK (witnessFresh () (1 : Fin 3)) := word_now h
      have hNe :
          exampleK (witnessFresh () (0 : Fin 3)) ≠
            exampleK (witnessFresh () (1 : Fin 3)) := by decide
      exact hNe hObs)

/-- Countermodel: local component 0 goes extinct but component 1
accepts the unchanged state, so old identity operations suffice. -/
def replacementAlive (t : ℕ) (loc : Fin 2) (x : Fin 3) : Prop :=
  (t = 0 ∧ loc = 0 ∧ x = 1) ∨
  (t = 1 ∧ loc = 1 ∧ x = 1)

theorem replacement_local_zero_extinct :
    ∀ x : Fin 3, ¬ replacementAlive 1 0 x := by
  intro x h
  rcases h with h | h
  · have hz : (1 : ℕ) = 0 := h.1
    omega
  · have hz : (0 : Fin 2) = 1 := h.2.1
    exact (by decide : (0 : Fin 2) ≠ 1) hz

theorem replacement_survives_with_old_words :
    IntervalSurvival replacementAlive baseStep [()] (1 : Fin 3) := by
  apply one_step_interval
  · exact ⟨0, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨1, Or.inr ⟨rfl, rfl, rfl⟩⟩

end LinearInputSemanticIntervals
