/-!
# Greatest observational bisimulation for a family of operators

A labelled deterministic transition system is given by an alphabet of
operators, one total transition per letter, and an observable readout.

An observational bisimulation is an arbitrary binary relation that agrees
on current outputs and is preserved by every labelled transition.
The full finite-word observational kernel is the greatest such relation.

No finiteness of either the state or action space is required here.
-/

noncomputable section

namespace LinearInputOperatorBisimulation

open LinearInputOperatorWords

/-- An observational bisimulation respects both readout and each action. -/
def Bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (R : α → α → Prop) : Prop :=
  ∀ x y, R x y →
    K x = K y ∧ (∀ i, R (step i x) (step i y))

/-- The complete word-equivalence relation is itself a bisimulation. -/
theorem wordEq_bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Bisimulation K step (WordEq K step) := by
  intro x y h
  exact ⟨word_now h, fun i => word_step h i⟩

/-- Every finite word preserves an observational bisimulation. -/
theorem bisimulation_run {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (R : α → α → Prop)
    (hR : Bisimulation K step R)
    (word : List ι) {x y : α} (hxy : R x y) :
    R (run step word x) (run step word y) := by
  induction word generalizing x y with
  | nil => simpa [run] using hxy
  | cons i word ih =>
      exact ih ((hR x y hxy).2 i)

/-- Every bisimulation is contained in finite-word equivalence. -/
theorem bisimulation_sub_wordEq {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (R : α → α → Prop)
    (hR : Bisimulation K step R) {x y : α} (hxy : R x y) :
    WordEq K step x y := by
  intro word
  exact (hR _ _ (bisimulation_run K step R hR word hxy)).1

/-- Finite-word indistinguishability is the greatest observational bisimulation. -/
theorem greatest_bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (x y : α) :
    WordEq K step x y ↔
      ∃ R : α → α → Prop, Bisimulation K step R ∧ R x y := by
  constructor
  · intro h
    exact ⟨WordEq K step, wordEq_bisimulation K step, h⟩
  · rintro ⟨R, hR, hxy⟩
    exact bisimulation_sub_wordEq K step R hR hxy

/-- Equality of states is always a bisimulation. -/
theorem diagonal_bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Bisimulation K step (fun x y => x = y) := by
  intro x y h
  subst y
  exact ⟨rfl, fun _ => rfl⟩

/-- Converse bisimulations remain bisimulations. -/
theorem converse_bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (R : α → α → Prop) (hR : Bisimulation K step R) :
    Bisimulation K step (fun x y => R y x) := by
  intro x y h
  obtain ⟨hK, hs⟩ := hR y x h
  exact ⟨hK.symm, fun i => hs i⟩

/-- Intersection of two observational bisimulations. -/
theorem intersection_bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (R S : α → α → Prop)
    (hR : Bisimulation K step R) (hS : Bisimulation K step S) :
    Bisimulation K step (fun x y => R x y ∧ S x y) := by
  intro x y h
  obtain ⟨hK, hRs⟩ := hR x y h.1
  obtain ⟨_, hSs⟩ := hS x y h.2
  exact ⟨hK, fun i => ⟨hRs i, hSs i⟩⟩

/-- Union of two observational bisimulations. -/
theorem union_bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (R S : α → α → Prop)
    (hR : Bisimulation K step R) (hS : Bisimulation K step S) :
    Bisimulation K step (fun x y => R x y ∨ S x y) := by
  intro x y h
  rcases h with hr | hs
  · obtain ⟨hK, hstep⟩ := hR x y hr
    exact ⟨hK, fun i => Or.inl (hstep i)⟩
  · obtain ⟨hK, hstep⟩ := hS x y hs
    exact ⟨hK, fun i => Or.inr (hstep i)⟩

/-- Relational composition of bisimulations is again a bisimulation. -/
theorem composition_bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (R S : α → α → Prop)
    (hR : Bisimulation K step R) (hS : Bisimulation K step S) :
    Bisimulation K step
      (fun x y => ∃ z, R x z ∧ S z y) := by
  intro x y h
  obtain ⟨z, hxz, hzy⟩ := h
  obtain ⟨hK1, hRstep⟩ := hR x z hxz
  obtain ⟨hK2, hSstep⟩ := hS z y hzy
  exact ⟨hK1.trans hK2,
    fun i => ⟨step i z, hRstep i, hSstep i⟩⟩

/-- Arbitrary unions (indexed by a family) of bisimulations remain bisimulations. -/
theorem indexed_union_bisimulation {α ω ι δ : Type*}
    (K : α → ω) (step : ι → α → α)
    (R : δ → α → α → Prop)
    (hR : ∀ d, Bisimulation K step (R d)) :
    Bisimulation K step (fun x y => ∃ d, R d x y) := by
  intro x y h
  obtain ⟨d, hxy⟩ := h
  obtain ⟨hK, hstep⟩ := hR d x y hxy
  exact ⟨hK, fun i => ⟨d, hstep i⟩⟩

/-- Arbitrary intersections of bisimulations remain bisimulations. -/
theorem indexed_intersection_bisimulation {α ω ι δ : Type*}
    (K : α → ω) (step : ι → α → α)
    (R : δ → α → α → Prop)
    (hR : ∀ d, Bisimulation K step (R d))
    [Nonempty δ] :
    Bisimulation K step (fun x y => ∀ d, R d x y) := by
  intro x y h
  obtain ⟨d⟩ := ‹Nonempty δ›
  have hK := ((hR d) x y (h d)).1
  exact ⟨hK, fun i d' => ((hR d') x y (h d')).2 i⟩

/-- Restricting the observable data via postprocessing preserves bisimulations. -/
theorem postprocess_bisimulation {α ω ν ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (f : ω → ν) (R : α → α → Prop)
    (hR : Bisimulation K step R) :
    Bisimulation (fun x => f (K x)) step R := by
  intro x y h
  obtain ⟨hK, hs⟩ := hR x y h
  exact ⟨congrArg f hK, hs⟩

/-- A correct state encoding induces an observational bisimulation on its fibers. -/
theorem representation_fiber_bisimulation {α β ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (f : α → β) (update : ι → β → β) (out : β → ω)
    (hout : ∀ x, out (f x) = K x)
    (hf : ∀ i x, f (step i x) = update i (f x)) :
    Bisimulation K step (fun x y => f x = f y) := by
  intro x y hxy
  constructor
  · calc
      K x = out (f x) := (hout x).symm
      _ = out (f y) := congrArg out hxy
      _ = K y := hout y
  · intro i
    calc
      f (step i x) = update i (f x) := hf i x
      _ = update i (f y) := congrArg (update i) hxy
      _ = f (step i y) := (hf i y).symm

/-- The kernel of every exact state encoding is contained in the word kernel. -/
theorem representation_fiber_sub_wordEq {α β ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (f : α → β) (update : ι → β → β) (out : β → ω)
    (hout : ∀ x, out (f x) = K x)
    (hf : ∀ i x, f (step i x) = update i (f x))
    {x y : α} (hxy : f x = f y) :
    WordEq K step x y :=
  bisimulation_sub_wordEq K step (fun x y => f x = f y)
    (representation_fiber_bisimulation K step f update out hout hf) hxy

/-- Every commuting, observation-invisible state map gives a bisimulation graph. -/
theorem symmetry_graph_bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (M : α → α)
    (hK : ∀ x, K (M x) = K x)
    (hM : ∀ i x, M (step i x) = step i (M x)) :
    Bisimulation K step (fun x y => M x = y) := by
  intro x y hxy
  constructor
  · calc
      K x = K (M x) := (hK x).symm
      _ = K y := congrArg K hxy
  · intro i
    calc
      M (step i x) = step i (M x) := hM i x
      _ = step i y := congrArg (step i) hxy

/-- The entire future cannot detect an observation-invisible symmetry. -/
theorem symmetry_invisible_all_words {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (M : α → α)
    (hK : ∀ x, K (M x) = K x)
    (hM : ∀ i x, M (step i x) = step i (M x)) (x : α) :
    WordEq K step (M x) x := by
  exact bisimulation_sub_wordEq K step
    (fun a b => M a = b)
    (symmetry_graph_bisimulation K step M hK hM)
    (by rfl)

/-- A bisimulation is stable under any newly named composite operator. -/
theorem generated_bisimulation {α ω ι κ : Type*}
    (K : α → ω) (step : ι → α → α)
    (R : α → α → Prop)
    (hR : Bisimulation K step R)
    (code : κ → List ι) :
    Bisimulation K (generated step code) R := by
  intro x y hxy
  exact ⟨(hR x y hxy).1,
    fun j => bisimulation_run K step R hR (code j) hxy⟩

/-- Existing bisimulations remain valid for any finite nesting of composites. -/
theorem generated_word_preserves_relation {α ω ι κ : Type*}
    (K : α → ω) (step : ι → α → α)
    (R : α → α → Prop)
    (hR : Bisimulation K step R)
    (code : κ → List ι) (word : List κ)
    {x y : α} (hxy : R x y) :
    R (run (generated step code) word x)
      (run (generated step code) word y) := by
  exact bisimulation_run K (generated step code) R
    (generated_bisimulation K step R hR code) word hxy

/-- Combining observer channels makes bisimulation exactly their intersection. -/
theorem pair_bisimulation_iff {α ω ν ι : Type*}
    (K : α → ω) (L : α → ν) (step : ι → α → α)
    (R : α → α → Prop) :
    Bisimulation (fun x => (K x, L x)) step R ↔
      Bisimulation K step R ∧ Bisimulation L step R := by
  constructor
  · intro h
    constructor
    · intro x y hxy
      obtain ⟨hp, hs⟩ := h x y hxy
      exact ⟨congrArg Prod.fst hp, hs⟩
    · intro x y hxy
      obtain ⟨hp, hs⟩ := h x y hxy
      exact ⟨congrArg Prod.snd hp, hs⟩
  · rintro ⟨hK, hL⟩ x y hxy
    obtain ⟨heK, hs⟩ := hK x y hxy
    obtain ⟨heL, _⟩ := hL x y hxy
    exact ⟨Prod.ext heK heL, hs⟩

/-- If an observer is already action-stable, its fibers form a bisimulation. -/
theorem respects_to_bisimulation {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (h : Respects K step) :
    Bisimulation K step (fun x y => K x = K y) := by
  intro x y hxy
  exact ⟨hxy, fun i => h i x y hxy⟩

/-- Conversely the observational fibers being a bisimulation forces stability. -/
theorem bisimulation_fibers_iff_respects {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Bisimulation K step (fun x y => K x = K y) ↔ Respects K step := by
  constructor
  · intro h i x y hxy
    exact (h x y hxy).2 i
  · exact respects_to_bisimulation K step

end LinearInputOperatorBisimulation
