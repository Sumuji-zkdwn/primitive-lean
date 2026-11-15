/-!
# Laakso void bridge: sound relational observation of non-descending updates

This module is assembled with the EXACT repository-owned
FutureObservations.inc, LaaksoFiniteGraph.inc, and
LaaksoNonlinearObstruction.inc sources. No original file is modified.

A deterministic update on raw states always induces a smallest sound
set-valued readout transition. It induces a singleton transition precisely
when it respects observation fibers. Abstracting intermediate states produces
a lax (possibly strictly overapproximating) compositional law.

On the first true binary-sheet / ternary-subdivision Laakso graph, a chosen
rightward edge step exposes a hidden sheet after one or two updates. Its
relational observation is nondeterministic but composes EXACTLY because images
of whole fibers are again unions of whole fibers.

The separately chosen cubic reaction/Euler map of the existing Laakso module
provides a second, real-valued obstruction to deterministic descent.

This is finite graph and discrete observation algebra, NOT a dynamics on the
continuous inverse-limit Laakso space or a theorem about physical black holes.
-/

namespace VoidLaaksoBridge

universe u v

variable {α : Type u} {β : Type v}

/-- The possible observed outputs after one concrete update from a label. -/
def relStep (π : α → β) (U : α → α) (q : β) : Set β :=
  {r | ∃ x, π x = q ∧ π (U x) = r}

/-- Extend the relational update to a set of observed labels. -/
def relSet (π : α → β) (U : α → α) (B : Set β) : Set β :=
  {r | ∃ x, π x ∈ B ∧ π (U x) = r}

/-- Exact outputs from a specified concrete uncertainty set. -/
def exactSet (π : α → β) (U : α → α) (A : Set α) : Set β :=
  {r | ∃ x ∈ A, π (U x) = r}

/-- The deterministic observer's kernel is stable under the update. -/
def FiberStable (π : α → β) (U : α → α) : Prop :=
  ∀ x y, π x = π y → π (U x) = π (U y)

/-- The image of every observation fiber under U is a union of complete
    observation fibers (no singleton-valuedness requirement). -/
def FiberImageClosed (π : α → β) (U : α → α) : Prop :=
  ∀ q x, (∃ y, π y = q ∧ π (U y) = π x) →
    ∃ y, π y = q ∧ U y = x

theorem relStep_sound (π : α → β) (U : α → α) (x : α) :
    π (U x) ∈ relStep π U (π x) :=
  ⟨x, rfl, rfl⟩

/-- Any sound nondeterministic model contains this canonical relational one. -/
theorem relStep_minimal (π : α → β) (U : α → α)
    (F : β → Set β) (hF : ∀ x, π (U x) ∈ F (π x)) (q : β) :
    relStep π U q ⊆ F q := by
  rintro r ⟨x, hx, hr⟩
  simpa only [hx, hr] using hF x

/-- Single-valuedness on actual observed fibers is equivalent to exact descent. -/
theorem relStep_singleton_iff (π : α → β) (U : α → α) :
    (∀ x, relStep π U (π x) = ({π (U x)} : Set β)) ↔
      FiberStable π U := by
  constructor
  · intro h x y hxy
    have hy : π (U y) ∈ relStep π U (π x) :=
      ⟨y, hxy.symm, rfl⟩
    rw [h x] at hy
    exact (Set.mem_singleton_iff.mp hy).symm
  · intro h x
    ext r
    constructor
    · rintro ⟨y, hxy, hy⟩
      change r = π (U x)
      exact hy.symm.trans (h y x hxy)
    · intro hr
      have hr' : r = π (U x) := by simpa using hr
      subst r
      exact ⟨x, rfl, rfl⟩

theorem exactSet_subset_relSet (π : α → β) (U : α → α) (A : Set α) :
    exactSet π U A ⊆ relSet π U (π '' A) := by
  rintro r ⟨x, hx, hr⟩
  exact ⟨x, ⟨x, hx, rfl⟩, hr⟩

/-- Exact abstraction of EVERY concrete uncertainty set is no weaker than
    deterministic descent: it is precisely fiber stability. -/
theorem relSet_global_exact_iff (π : α → β) (U : α → α) :
    (∀ A : Set α, relSet π U (π '' A) = exactSet π U A) ↔
      FiberStable π U := by
  constructor
  · intro h x y hxy
    have hy : π (U y) ∈ relSet π U (π '' ({x} : Set α)) :=
      ⟨y, ⟨x, by simp, hxy⟩, rfl⟩
    rw [h {x}] at hy
    rcases hy with ⟨z, hz, hzout⟩
    have hzx : z = x := by simpa only [Set.mem_singleton_iff] using hz
    subst z
    exact hzout
  · intro h A
    ext r
    constructor
    · rintro ⟨x, ⟨y, hy, hxy⟩, hr⟩
      exact ⟨y, hy, (h y x hxy).trans hr⟩
    · exact (exactSet_subset_relSet π U A) r

/-- Coarse-graining between two updates can only add possible outputs. -/
theorem relSet_comp_subset (π : α → β) (U V : α → α) (B : Set β) :
    relSet π (fun x => V (U x)) B ⊆
      relSet π V (relSet π U B) := by
  rintro r ⟨x, hx, hr⟩
  exact ⟨U x, ⟨x, hx, rfl⟩, hr⟩

/-- A fiber-respecting SECOND operator removes any spurious intermediate
    alternatives introduced by the FIRST operator. -/
theorem relSet_comp_eq_of_second_stable
    (π : α → β) (U V : α → α) (hV : FiberStable π V) (B : Set β) :
    relSet π V (relSet π U B) =
      relSet π (fun x => V (U x)) B := by
  apply Set.Subset.antisymm
  · rintro r ⟨y, ⟨x, hx, hxy⟩, hr⟩
    exact ⟨x, hx, (hV (U x) y hxy).trans hr⟩
  · exact relSet_comp_subset π U V B

/-- A fiber-image-closed update sends every saturated uncertainty set to
    another saturated set.  It need NOT descend as a deterministic update. -/
theorem fiberImageClosed_sets (π : α → β) (U : α → α)
    (h : FiberImageClosed π U) (B : Set β) :
    U '' (π ⁻¹' B) = π ⁻¹' (relSet π U B) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, congrArg π hxy⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨z, hz, hzout⟩ := h (π y) x ⟨y, rfl, hxy⟩
    have hzB : π z ∈ B := by rw [hz]; exact hy
    exact ⟨z, hzB, hzout⟩

/-- A fiber-image-closed FIRST operator also makes relational composition
    exact for EVERY second operator, even if both are nondeterministic after
    observation.  This is a distinct route from deterministic descent. -/
theorem relSet_comp_eq_of_first_closed
    (π : α → β) (U V : α → α) (hU : FiberImageClosed π U)
    (B : Set β) :
    relSet π V (relSet π U B) =
      relSet π (fun x => V (U x)) B := by
  apply Set.Subset.antisymm
  · rintro r ⟨y, hy, hr⟩
    have hy' : y ∈ U '' (π ⁻¹' B) := by
      rw [fiberImageClosed_sets π U hU B]
      exact hy
    rcases hy' with ⟨x, hx, hxy⟩
    exact ⟨x, hx, by simpa only [hxy] using hr⟩
  · exact relSet_comp_subset π U V B

section FiniteLaakso

open LinearInputLaaksoFiniteGraph

/-- Exactly the RawVertex and RefinedVertex types of LaaksoFiniteGraph.inc. -/
abbrev Raw1 := RawVertex (Fin 2) (Fin 1)
abbrev Obs1 := RefinedVertex (Fin 2) (Fin 1)

def firstRead : Raw1 → Obs1 := rawProjection

/-- A selected right-moving step along existing labelled edges.
    A new first junction travels along a middle edge to the second junction,
    then leaves on its same-sheet right edge. Old endpoints are absorbing.
    The behavior is a CHOICE, not forced by the Laakso graph. -/
def advanceRight : Raw1 → Raw1
  | (.inl v, b) => (.inl v, b)
  | (.inr (e, k), b) =>
      if k = 0 then (.inr (e, 1), b) else (.inl 1, b)

def w1 (b : Bool) : Raw1 := (.inr (0, 0), b)
def w2 (b : Bool) : Raw1 := (.inr (0, 1), b)

/-- The first step really follows one of the graph's two labelled
    parallel middle edges, not an invented abstract join. -/
theorem middle_edge_incidence (b : Bool) :
    firstRead (w1 b) = refineSource base (0, b, (1 : Fin 3)) ∧
    firstRead (advanceRight (w1 b)) =
      refineTarget base (0, b, (1 : Fin 3)) := by
  cases b <;> decide

/-- The second step follows the labelled right outgoing edge. -/
theorem right_edge_incidence (b : Bool) :
    firstRead (w2 b) = refineSource base (0, b, (2 : Fin 3)) ∧
    firstRead (advanceRight (w2 b)) =
      refineTarget base (0, b, (2 : Fin 3)) := by
  cases b <;> decide

/-- The new junction looks the same from either sheet, until exiting. -/
theorem w2_one_step_split :
    firstRead (w2 false) = firstRead (w2 true) ∧
      firstRead (advanceRight (w2 false)) ≠
        firstRead (advanceRight (w2 true)) := by
  decide

/-- A first junction hides the sheet for one step but not two. -/
theorem w1_two_step_split :
    firstRead (w1 false) = firstRead (w1 true) ∧
      firstRead (advanceRight (w1 false)) =
        firstRead (advanceRight (w1 true)) ∧
      firstRead (advanceRight (advanceRight (w1 false))) ≠
        firstRead (advanceRight (advanceRight (w1 true))) := by
  decide

/-- All 8 raw states are separated by observations at times 0,1,2.
    The present readout has only six values; the t≤1 readout has seven. -/
theorem depth_two_separates :
    ∀ x y : Raw1,
      firstRead x = firstRead y →
      firstRead (advanceRight x) = firstRead (advanceRight y) →
      firstRead (advanceRight (advanceRight x)) =
        firstRead (advanceRight (advanceRight y)) → x = y := by
  classical
  decide

theorem depth_one_not_enough :
    ∃ x y : Raw1,
      x ≠ y ∧
      firstRead x = firstRead y ∧
      firstRead (advanceRight x) = firstRead (advanceRight y) := by
  exact ⟨w1 false, w1 true, by decide, by decide, by decide⟩

/-- Despite non-descending behavior, whole fibers have whole-fiber images. -/
theorem first_fiber_images_closed :
    FiberImageClosed firstRead advanceRight := by
  classical
  decide

/-- This non-deterministic quotient step composes EXACTLY. -/
theorem first_relational_composition_exact (V : Raw1 → Raw1) (B : Set Obs1) :
    relSet firstRead V (relSet firstRead advanceRight B) =
      relSet firstRead (fun x => V (advanceRight x)) B :=
  relSet_comp_eq_of_first_closed firstRead advanceRight V
    first_fiber_images_closed B

theorem first_not_fiber_stable :
    ¬ FiberStable firstRead advanceRight := by
  intro h
  exact w2_one_step_split.2
    (h (w2 false) (w2 true) w2_one_step_split.1)

theorem first_no_deterministic_quotient :
    ¬ ∃ V : Obs1 → Obs1,
        ∀ x : Raw1, firstRead (advanceRight x) = V (firstRead x) := by
  rintro ⟨V, hV⟩
  apply w2_one_step_split.2
  calc
    firstRead (advanceRight (w2 false)) = V (firstRead (w2 false)) :=
      hV _
    _ = V (firstRead (w2 true)) :=
      congrArg V w2_one_step_split.1
    _ = firstRead (advanceRight (w2 true)) := (hV _).symm

theorem first_not_globally_exact :
    ¬ ∀ A : Set Raw1,
      relSet firstRead advanceRight (firstRead '' A) =
        exactSet firstRead advanceRight A := by
  intro h
  exact first_not_fiber_stable
    ((relSet_global_exact_iff firstRead advanceRight).mp h)

/-- At the second junction both outgoing observed states are necessary. -/
theorem w2_two_relational_outputs :
    firstRead (advanceRight (w2 false)) ∈
        relStep firstRead advanceRight (firstRead (w2 false)) ∧
    firstRead (advanceRight (w2 true)) ∈
        relStep firstRead advanceRight (firstRead (w2 false)) := by
  constructor
  · exact ⟨w2 false, rfl, rfl⟩
  · exact ⟨w2 true, rfl, rfl⟩

theorem w2_relational_not_singleton :
    ¬ ∃ q : Obs1,
      relStep firstRead advanceRight (firstRead (w2 false)) = {q} := by
  rintro ⟨q, hq⟩
  have h1 : firstRead (advanceRight (w2 false)) = q := by
    have hm := w2_two_relational_outputs.1
    rw [hq] at hm
    simpa only [Set.mem_singleton_iff] using hm
  have h2 : firstRead (advanceRight (w2 true)) = q := by
    have hm := w2_two_relational_outputs.2
    rw [hq] at hm
    simpa only [Set.mem_singleton_iff] using hm
  exact w2_one_step_split.2 (h1.trans h2.symm)

end FiniteLaakso

section NonlinearLaakso

open LinearInputLaaksoNonlinear

/-- The previously formalized two real-valued Laakso state witnesses
    force two different outputs in the relational observation map. -/
theorem nonlinear_two_outputs (coupling step : ℝ) (hstep : step ≠ 0) :
    ∃ a b : ℝ × ℝ,
      a ≠ b ∧
      a ∈ relStep pairMean (fineStep coupling step) (pairMean uniformWitness) ∧
      b ∈ relStep pairMean (fineStep coupling step) (pairMean uniformWitness) := by
  refine ⟨pairMean (fineStep coupling step uniformWitness),
    pairMean (fineStep coupling step splitWitness), ?_, ?_, ?_⟩
  · exact witnesses_different_next_mean coupling step hstep
  · exact relStep_sound pairMean (fineStep coupling step) uniformWitness
  · exact ⟨splitWitness, witnesses_same_mean.symm, rfl⟩

/-- A canonical sound relational update exists, but a globally exact
    single-step abstraction from ARBITRARY fine-state subsets does not.
    This is the general criterion applied to the existing nonlinear witness. -/
theorem nonlinear_no_global_exactness (coupling step : ℝ) (hstep : step ≠ 0) :
    ¬ ∀ A : Set FineState,
        relSet pairMean (fineStep coupling step) (pairMean '' A) =
          exactSet pairMean (fineStep coupling step) A := by
  intro h
  have hstable : FiberStable pairMean (fineStep coupling step) :=
    (relSet_global_exact_iff pairMean (fineStep coupling step)).mp h
  exact witnesses_different_next_mean coupling step hstep
    (hstable uniformWitness splitWitness witnesses_same_mean)

end NonlinearLaakso

end VoidLaaksoBridge
