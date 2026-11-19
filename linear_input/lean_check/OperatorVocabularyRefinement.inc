/-!
# Adding operator vocabularies and refining predictive state spaces

We extend a labelled deterministic system with additional primitive actions.
The existing word-observation quotient maps canonically from the enlarged
language to the smaller one.

A new action preserves the old predictive kernel precisely when it cannot
make any formerly hidden distinction observable, even after subsequent
old actions. This characterizes observationally conservative extensions.
-/

noncomputable section

namespace LinearInputOperatorRefinement

open LinearInputOperatorWords

/-- Extend an existing operator alphabet with a new one. -/
def sumStep {α ι κ : Type*}
    (old : ι → α → α) (fresh : κ → α → α) :
    Sum ι κ → α → α
  | Sum.inl i => old i
  | Sum.inr j => fresh j

/-- Running a word of exclusively old letters in the extended language. -/
theorem run_inl {α ι κ : Type*}
    (old : ι → α → α) (fresh : κ → α → α)
    (word : List ι) (x : α) :
    run (sumStep old fresh) (word.map Sum.inl) x = run old word x := by
  induction word generalizing x with
  | nil => rfl
  | cons i word ih =>
      change run (sumStep old fresh) (word.map Sum.inl) (old i x) =
        run old word (old i x)
      exact ih (old i x)

/-- Running a word of exclusively new letters in the extended language. -/
theorem run_inr {α ι κ : Type*}
    (old : ι → α → α) (fresh : κ → α → α)
    (word : List κ) (x : α) :
    run (sumStep old fresh) (word.map Sum.inr) x = run fresh word x := by
  induction word generalizing x with
  | nil => rfl
  | cons j word ih =>
      change run (sumStep old fresh) (word.map Sum.inr) (fresh j x) =
        run fresh word (fresh j x)
      exact ih (fresh j x)

/-- Additional actions can only refine, not coarsen, observational equivalence. -/
theorem extended_implies_old {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α)
    {x y : α} (h : WordEq K (sumStep old fresh) x y) :
    WordEq K old x y := by
  intro word
  have hw := h (word.map Sum.inl)
  simpa only [run_inl] using hw

theorem extended_implies_new {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α)
    {x y : α} (h : WordEq K (sumStep old fresh) x y) :
    WordEq K fresh x y := by
  intro word
  have hw := h (word.map Sum.inr)
  simpa only [run_inr] using hw

/-- The exact condition for every new action to preserve old distinctions. -/
def PreservesOldEq {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α) : Prop :=
  ∀ j x y, WordEq K old x y →
    WordEq K old (fresh j x) (fresh j y)

/-- If new operators preserve the old word kernel, arbitrary mixtures do too. -/
theorem stable_old_implies_extended {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α)
    (hnew : PreservesOldEq K old fresh)
    {x y : α} (hxy : WordEq K old x y) :
    WordEq K (sumStep old fresh) x y := by
  have hrun : ∀ word : List (Sum ι κ), ∀ a b : α,
      WordEq K old a b →
      K (run (sumStep old fresh) word a) =
        K (run (sumStep old fresh) word b) := by
    intro word
    induction word with
    | nil =>
        intro a b hab
        exact word_now hab
    | cons tag rest ih =>
        intro a b hab
        cases tag with
        | inl i =>
            change K (run (sumStep old fresh) rest (old i a)) =
              K (run (sumStep old fresh) rest (old i b))
            exact ih (old i a) (old i b) (word_step hab i)
        | inr j =>
            change K (run (sumStep old fresh) rest (fresh j a)) =
              K (run (sumStep old fresh) rest (fresh j b))
            exact ih (fresh j a) (fresh j b) (hnew j a b hab)
  intro word
  exact hrun word x y hxy

/-- Characterization of conservative operator-language extensions. -/
theorem extension_exact_iff_preserves {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α) :
    (∀ x y, WordEq K (sumStep old fresh) x y ↔ WordEq K old x y) ↔
      PreservesOldEq K old fresh := by
  constructor
  · intro he j x y hxy
    have hExt := (he x y).2 hxy
    exact extended_implies_old K old fresh
      (word_step hExt (Sum.inr j))
  · intro hp x y
    exact ⟨extended_implies_old K old fresh,
      stable_old_implies_extended K old fresh hp⟩

/-- A violation of old-kernel invariance yields a strict new distinction. -/
theorem instability_yields_strict_refinement {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α)
    (j : κ) (x y : α)
    (hxy : WordEq K old x y)
    (hnew : ¬ WordEq K old (fresh j x) (fresh j y)) :
    WordEq K old x y ∧
      ¬ WordEq K (sumStep old fresh) x y := by
  constructor
  · exact hxy
  · intro hExt
    exact hnew (extended_implies_old K old fresh
      (word_step hExt (Sum.inr j)))

/-- Conservativity is equivalent to the absence of any strict kernel refinement. -/
theorem no_strict_refinement_iff_preserves {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α) :
    (∀ x y, WordEq K old x y →
      WordEq K (sumStep old fresh) x y) ↔
      PreservesOldEq K old fresh := by
  constructor
  · intro h j x y hxy
    exact extended_implies_old K old fresh
      (word_step (h x y hxy) (Sum.inr j))
  · intro hp x y hxy
    exact stable_old_implies_extended K old fresh hp hxy

/-- A concrete separating operator word exists precisely when WordEq fails. -/
theorem distinguishes_iff_not_wordEq {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (x y : α) :
    (∃ word : List ι, K (run step word x) ≠
      K (run step word y)) ↔ ¬ WordEq K step x y := by
  classical
  simp only [WordEq, not_forall]

/-- A strict new distinction comes with a finite mixed-language witness. -/
theorem instability_has_explicit_word {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α)
    (j : κ) (x y : α)
    (hnew : ¬ WordEq K old (fresh j x) (fresh j y)) :
    ∃ word : List (Sum ι κ),
      K (run (sumStep old fresh) word x) ≠
        K (run (sumStep old fresh) word y) := by
  obtain ⟨tail, htail⟩ :=
    (distinguishes_iff_not_wordEq K old (fresh j x) (fresh j y)).2 hnew
  refine ⟨Sum.inr j :: tail.map Sum.inl, ?_⟩
  simpa only [run_cons, run_inl, sumStep] using htail

/-- If all new actions are old words, none can refine the old kernel. -/
theorem generated_preserves_old {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (code : κ → List ι) :
    PreservesOldEq K old (generated old code) := by
  intro j x y hxy
  exact word_run hxy (code j)

/-- Adjoining any number of compiled old actions is observation-exact. -/
theorem generated_extension_exact {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (code : κ → List ι) (x y : α) :
    WordEq K (sumStep old (generated old code)) x y ↔
      WordEq K old x y := by
  exact (extension_exact_iff_preserves K old
    (generated old code)).2 (generated_preserves_old K old code) x y

/-- The predictive state of the extended language forgets onto the old one. -/
def forget {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (fresh : κ → α → α) :
    State K (sumStep old fresh) → State K old :=
  Quotient.lift (fun x => encode K old x) (by
    intro x y h
    exact Quotient.sound (extended_implies_old K old fresh h))

theorem forget_encode {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (fresh : κ → α → α) (x : α) :
    forget K old fresh (encode K (sumStep old fresh) x) =
      encode K old x := rfl

/-- The quotient forgetful map is always onto. -/
theorem forget_surjective {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (fresh : κ → α → α) :
    Function.Surjective (forget K old fresh) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
      exact ⟨encode K (sumStep old fresh) x, rfl⟩

/-- The old observer commutes with forgetting the new vocabulary. -/
theorem forget_readout {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (fresh : κ → α → α)
    (q : State K (sumStep old fresh)) :
    readout K old (forget K old fresh q) =
      readout K (sumStep old fresh) q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- Old actions are simulated exactly by the forgetful quotient map. -/
theorem forget_transition {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (fresh : κ → α → α) (i : ι)
    (q : State K (sumStep old fresh)) :
    forget K old fresh
        (transition K (sumStep old fresh) (Sum.inl i) q) =
      transition K old i (forget K old fresh q) := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- A conservative extension does not split any old predictive quotient state. -/
theorem forget_injective_of_preserves {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (fresh : κ → α → α)
    (hnew : PreservesOldEq K old fresh) :
    Function.Injective (forget K old fresh) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
        have hOld : WordEq K old x y :=
          (encode_eq_iff K old x y).1 hqr
        exact (encode_eq_iff K (sumStep old fresh) x y).2
          (stable_old_implies_extended K old fresh hnew hOld)

/-- Failure to preserve one pair produces two distinct extended quotient states
that the old quotient identifies. -/
theorem strict_refinement_splits_quotient {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (fresh : κ → α → α) (x y : α)
    (hOld : WordEq K old x y)
    (hExt : ¬ WordEq K (sumStep old fresh) x y) :
    ∃ q r : State K (sumStep old fresh),
      q ≠ r ∧ forget K old fresh q = forget K old fresh r := by
  refine ⟨encode K (sumStep old fresh) x,
    encode K (sumStep old fresh) y, ?_, ?_⟩
  · intro he
    exact hExt ((encode_eq_iff K (sumStep old fresh) x y).1 he)
  · exact (encode_eq_iff K old x y).2 hOld

/-- A noninjective forgetful map is exactly an informational loss of vocabulary. -/
theorem forget_not_injective_of_instability {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α)
    (fresh : κ → α → α)
    (j : κ) (x y : α)
    (hOld : WordEq K old x y)
    (hnew : ¬ WordEq K old (fresh j x) (fresh j y)) :
    ¬ Function.Injective (forget K old fresh) := by
  obtain ⟨q, r, hne, heq⟩ :=
    strict_refinement_splits_quotient K old fresh x y hOld
      (instability_yields_strict_refinement K old fresh j x y
        hOld hnew).2
  intro hinj
  exact hne (hinj heq)

/-- On the three-state witness, one new primitive strictly refines the quotient. -/
def witnessFresh : Unit → Fin 3 → Fin 3 :=
  fun _ x => if x = 1 then 2 else x

theorem witness_old_equiv :
    WordEq exampleK baseStep (0 : Fin 3) (1 : Fin 3) :=
  base_cannot_distinguish

theorem witness_new_breaks :
    ¬ WordEq exampleK (sumStep baseStep witnessFresh)
      (0 : Fin 3) (1 : Fin 3) := by
  intro h
  have hsep :
      exampleK (run (sumStep baseStep witnessFresh)
        [Sum.inr ()] (0 : Fin 3)) ≠
      exampleK (run (sumStep baseStep witnessFresh)
        [Sum.inr ()] (1 : Fin 3)) := by decide
  exact hsep (h [Sum.inr ()])

theorem witness_forget_not_injective :
    ¬ Function.Injective (forget exampleK baseStep witnessFresh) := by
  obtain ⟨q, r, hne, heq⟩ :=
    strict_refinement_splits_quotient exampleK baseStep witnessFresh
      0 1 witness_old_equiv witness_new_breaks
  intro hinj
  exact hne (hinj heq)

end LinearInputOperatorRefinement
