/-!
# Observer-relative orientation and shortest separating operation words

An observation does not come with an absolute time direction. Two states
(which may encode differently ordered histories) become distinguishable only
relative to a chosen readout and a vocabulary of allowed continuations.

For a fixed primitive operator family, enlarging that vocabulary cannot erase
an observable distinction, nor increase the least length of a separating
continuation if one already exists. The leastDepth measure counts primitive
symbols, not physical time: a newly named macro can shorten it without
changing the predictive quotient.

A reversal-invariant residue cannot carry a nonzero antisymmetric orientation
label. No asynchronous schedule, physical time law, or narrative selection is
derived from these statements.
-/

noncomputable section

namespace LinearInputOperatorOrientationDepth

open LinearInputOperatorWords

/-- All letters of the continuation are available to the observer. -/
def AllowedWord {ι : Type*} (A : Set ι) (word : List ι) : Prop :=
  ∀ i, i ∈ word → i ∈ A

/-- The pair can be distinguished within at most n allowed primitive steps. -/
def SeparatedWithin {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Set ι) (x y : α) (n : ℕ) : Prop :=
  ∃ word : List ι, AllowedWord A word ∧ word.length ≤ n ∧
    K (run step word x) ≠ K (run step word y)

/-- An allowed continuation of finite length distinguishes the pair. -/
def EverSeparated {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Set ι) (x y : α) : Prop :=
  ∃ n : ℕ, SeparatedWithin K step A x y n

/-- Equality under every continuation the observer can perform. -/
def ObservationalEq {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Set ι) (x y : α) : Prop :=
  ∀ word : List ι, AllowedWord A word →
    K (run step word x) = K (run step word y)

theorem allowedWord_mono {ι : Type*} {A B : Set ι}
    (hAB : A ⊆ B) {word : List ι}
    (hw : AllowedWord A word) : AllowedWord B word := by
  intro i hi
  exact hAB (hw i hi)

/-- Vocabulary extension preserves any bounded separating witness. -/
theorem separatedWithin_mono {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    {A B : Set ι} (hAB : A ⊆ B)
    {x y : α} {n : ℕ}
    (hs : SeparatedWithin K step A x y n) :
    SeparatedWithin K step B x y n := by
  obtain ⟨word, hw, hn, hsep⟩ := hs
  exact ⟨word, allowedWord_mono hAB hw, hn, hsep⟩

theorem everSeparated_mono {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    {A B : Set ι} (hAB : A ⊆ B)
    {x y : α} (h : EverSeparated K step A x y) :
    EverSeparated K step B x y := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, separatedWithin_mono K step hAB hn⟩

/-- Removing actions can only coarsen predictive observational equivalence. -/
theorem observationalEq_antitone {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    {A B : Set ι} (hAB : A ⊆ B)
    {x y : α} (hB : ObservationalEq K step B x y) :
    ObservationalEq K step A x y := by
  intro word hw
  exact hB word (allowedWord_mono hAB hw)

/-- An unboundedly separating continuation exists iff full equality fails. -/
theorem everSeparated_iff_not_observationalEq {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Set ι) (x y : α) :
    EverSeparated K step A x y ↔ ¬ ObservationalEq K step A x y := by
  classical
  constructor
  · intro h heq
    obtain ⟨n, word, hw, hn, hsep⟩ := h
    exact hsep (heq word hw)
  · intro h
    by_contra hnone
    apply h
    intro word hw
    by_contra hsep
    exact hnone ⟨word.length, word, hw, le_rfl, hsep⟩

/-- All allowed letters recover the existing full-word observational kernel. -/
theorem observationalEq_univ_iff_wordEq {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (x y : α) :
    ObservationalEq K step Set.univ x y ↔ WordEq K step x y := by
  constructor
  · intro h word
    exact h word (by intro i hi; trivial)
  · intro h word hw
    exact h word

/-- Shortest separating word length, only defined for separable state pairs. -/
noncomputable def leastDepth {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Set ι) (x y : α)
    (h : EverSeparated K step A x y) : ℕ := by
  classical
  exact Nat.find h

theorem leastDepth_spec {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Set ι) (x y : α)
    (h : EverSeparated K step A x y) :
    SeparatedWithin K step A x y (leastDepth K step A x y h) := by
  classical
  exact Nat.find_spec h

theorem leastDepth_le {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Set ι) (x y : α)
    (h : EverSeparated K step A x y) (n : ℕ)
    (hn : SeparatedWithin K step A x y n) :
    leastDepth K step A x y h ≤ n := by
  classical
  unfold leastDepth
  exact Nat.find_le hn

/-- Increasing the available operations cannot increase minimum depth. -/
theorem leastDepth_antitone {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    {A B : Set ι} (hAB : A ⊆ B)
    (x y : α) (hA : EverSeparated K step A x y) :
    leastDepth K step B x y (everSeparated_mono K step hAB hA) ≤
      leastDepth K step A x y hA := by
  classical
  unfold leastDepth
  exact Nat.find_le (separatedWithin_mono K step hAB (Nat.find_spec hA))

/-- Present observational equality rules out a zero-step separator. -/
theorem not_separated_at_zero {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (A : Set ι) (x y : α) (hxy : K x = K y) :
    ¬ SeparatedWithin K step A x y 0 := by
  rintro ⟨word, _, hlen, hsep⟩
  have hnil : word = [] := by
    cases word with
    | nil => rfl
    | cons i rest => simp at hlen
  subst word
  exact hsep (by simpa [run] using hxy)

/-- The original observer has access only to the inert action false. -/
def oldAllowed : Set Bool := {false}

/-- Every word in the old vocabulary leaves the retained three-state model fixed. -/
theorem old_word_identity (word : List Bool) :
    AllowedWord oldAllowed word → ∀ x : Fin 3,
      run extendedStep word x = x := by
  induction word with
  | nil =>
      intro _ x
      rfl
  | cons op rest ih =>
      intro hw x
      have hop : op = false := by
        have hmem : op ∈ oldAllowed := hw op (by simp)
        simpa [oldAllowed] using hmem
      have hrest : AllowedWord oldAllowed rest := by
        intro i hi
        exact hw i (by simp [hi])
      subst op
      change run extendedStep rest x = x
      exact ih hrest x

theorem old_observationalEq :
    ObservationalEq exampleK extendedStep oldAllowed
      (0 : Fin 3) (1 : Fin 3) := by
  intro word hw
  rw [old_word_identity word hw 0, old_word_identity word hw 1]
  decide

theorem old_not_everSeparated :
    ¬ EverSeparated exampleK extendedStep oldAllowed
      (0 : Fin 3) (1 : Fin 3) := by
  intro h
  exact ((everSeparated_iff_not_observationalEq exampleK extendedStep
    oldAllowed 0 1).mp h) old_observationalEq

/-- One genuine new action exposes the hidden difference. -/
theorem full_separated_in_one :
    SeparatedWithin exampleK extendedStep Set.univ
      (0 : Fin 3) (1 : Fin 3) 1 := by
  refine ⟨[true], ?_, by decide, by decide⟩
  intro i hi
  trivial

theorem full_everSeparated :
    EverSeparated exampleK extendedStep Set.univ
      (0 : Fin 3) (1 : Fin 3) :=
  ⟨1, full_separated_in_one⟩

/-- The new separator requires exactly one primitive step, not zero. -/
theorem full_leastDepth_one :
    leastDepth exampleK extendedStep Set.univ
      (0 : Fin 3) (1 : Fin 3) full_everSeparated = 1 := by
  have hle : leastDepth exampleK extendedStep Set.univ
      (0 : Fin 3) (1 : Fin 3) full_everSeparated ≤ 1 :=
    leastDepth_le exampleK extendedStep Set.univ 0 1
      full_everSeparated 1 full_separated_in_one
  have hzero : ¬ SeparatedWithin exampleK extendedStep Set.univ
      (0 : Fin 3) (1 : Fin 3) 0 :=
    not_separated_at_zero exampleK extendedStep Set.univ 0 1 (by decide)
  have hspec := leastDepth_spec exampleK extendedStep Set.univ 0 1
    full_everSeparated
  have hpos : leastDepth exampleK extendedStep Set.univ
      (0 : Fin 3) (1 : Fin 3) full_everSeparated ≠ 0 := by
    intro h
    exact hzero (by simpa only [h] using hspec)
  omega

/-- No nonzero antisymmetric direction label descends through a
reversal-invariant residue observation. -/
theorem invariant_residue_forces_zero_orientation {α ω : Type*}
    (R : α → ω) (reverse : α → α) (sign : ω → ℤ)
    (hR : ∀ x, R (reverse x) = R x)
    (hsign : ∀ x, sign (R (reverse x)) = -sign (R x)) :
    ∀ x, sign (R x) = 0 := by
  intro x
  have hx := hsign x
  rw [hR x] at hx
  omega

end LinearInputOperatorOrientationDepth
