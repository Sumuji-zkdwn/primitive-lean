/-!
Finite counting for singleton Stops closures.

For a prescribed finite fixed set A, an arbitrary operator is specified by
one non-self output choice at every point outside A. Idempotent operators
with fixed set A are exactly the existing supported retractions onto A.
The closure count uses the already proved fixed-set characterization only
when A is nonempty and proper. At either boundary the closure is universal.
-/

noncomputable section

namespace LinearInputStrangeCounting

open LinearInputF0Counting
open LinearInputStrangeFixedSets
open LinearInputF0

universe u

attribute [local instance] Classical.propDecidable

abbrev MapsWithFixedSet {α : Type u} [Fintype α] (A : Finset α) :=
  {U : α → α // LinearInputF0Counting.fixedSet U = A}

abbrev OutsideSet {α : Type u} (A : Finset α) := {x : α // x ∉ A}

/-- The product of choices: each nonfixed state chooses an output other than itself. -/
abbrev FixedSetChoices {α : Type u} (A : Finset α) :=
  ∀ x : OutsideSet A, {y : α // y ≠ x.1}

/-- Turn independent non-self choices into an operator that fixes A. -/
def realizeChoices {α : Type u} [Fintype α] (A : Finset α)
    (f : FixedSetChoices A) : α → α :=
  fun x => if hx : x ∈ A then x else (f ⟨x, hx⟩).1

theorem fixedSet_realizeChoices {α : Type u} [Fintype α]
    (A : Finset α) (f : FixedSetChoices A) :
    LinearInputF0Counting.fixedSet (realizeChoices A f) = A := by
  classical
  ext x
  rw [LinearInputF0Counting.mem_fixedSet]
  constructor
  · intro hfix
    by_contra hxA
    have hout : (f ⟨x, hxA⟩).1 = x := by
      simpa [realizeChoices, hxA] using hfix
    exact (f ⟨x, hxA⟩).property hout
  · intro hxA
    simp [realizeChoices, hxA]

/-- Operators with fixed set A are equivalent to the independent choice product. -/
noncomputable def mapsWithFixedSetEquivChoices {α : Type u} [Fintype α]
    (A : Finset α) : MapsWithFixedSet A ≃ FixedSetChoices A := by
  classical
  refine
    { toFun := fun U x =>
        ⟨U.1 x.1, ?_⟩
      invFun := fun f => ⟨realizeChoices A f, fixedSet_realizeChoices A f⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro hfix
    have hxFix : x.1 ∈ LinearInputF0Counting.fixedSet U.1 :=
      (LinearInputF0Counting.mem_fixedSet U.1 x.1).mpr hfix
    rw [U.2] at hxFix
    exact x.2 hxFix
  · intro U
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ A
    · have hfix : U.1 x = x := by
        apply (LinearInputF0Counting.mem_fixedSet U.1 x).mp
        rw [U.2]
        exact hx
      simp [realizeChoices, hx, hfix]
    · simp [realizeChoices, hx]
  · intro f
    funext x
    apply Subtype.ext
    simp only [realizeChoices, dite_eq_right x.2]

private theorem card_nonself_choices {α : Type u} [Fintype α] (x : α) :
    Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 := by
  classical
  rw [Fintype.card_subtype_compl (p := fun y : α => y = x)]
  simp

private noncomputable def fixedChoicesEquivFin {α : Type u} [Fintype α]
    (A : Finset α) :
    FixedSetChoices A ≃ (OutsideSet A → Fin (Fintype.card α - 1)) := by
  classical
  exact Equiv.piCongrRight fun x =>
    Fintype.equivOfCardEq (by
      simpa only [Fintype.card_fin] using card_nonself_choices x.1)

/-- The exact number of arbitrary maps with prescribed fixed set A. -/
theorem fixed_set_map_count {α : Type u} [Fintype α] (A : Finset α) :
    Nat.card (MapsWithFixedSet A) =
      (Fintype.card α - 1) ^ (Fintype.card α - A.card) := by
  classical
  rw [Nat.card_congr (mapsWithFixedSetEquivChoices A),
      Nat.card_congr (fixedChoicesEquivFin A), Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_subtype_compl, Fintype.card_coe]

abbrev IdempotentsWithFixedSet {α : Type u} [Fintype α] (A : Finset α) :=
  {K : α → α // LinearInputF0.Idempotent K ∧
    LinearInputF0Counting.fixedSet K = A}

/-- A retraction onto A is exactly an idempotent whose fixed set is A. -/
noncomputable def idempotentsWithFixedSetEquivRetractions {α : Type u}
    [Fintype α] (A : Finset α) :
    IdempotentsWithFixedSet A ≃ LinearInputF0Counting.SupportedRetraction A := by
  classical
  refine
    { toFun := fun K => ⟨K.1, ?_⟩
      invFun := fun R =>
        ⟨R.1, LinearInputF0Counting.supported_idempotent R,
          LinearInputF0Counting.fixedSet_supported R⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro x hxA
      have hxFix : x ∈ LinearInputF0Counting.fixedSet K.1 := by
        rw [K.2.2]
        exact hxA
      exact (LinearInputF0Counting.mem_fixedSet K.1 x).mp hxFix
    · intro x
      have hxFix : K.1 x ∈ LinearInputF0Counting.fixedSet K.1 :=
        (LinearInputF0Counting.mem_fixedSet K.1 (K.1 x)).mpr (K.2.1 x)
      rw [K.2.2] at hxFix
      exact hxFix
  · intro K
    apply Subtype.ext
    rfl
  · intro R
    apply Subtype.ext
    rfl

/-- The exact number of idempotent maps with prescribed fixed set A. -/
theorem fixed_set_idempotent_count {α : Type u} [Fintype α]
    (A : Finset α) :
    Nat.card (IdempotentsWithFixedSet A) =
      A.card ^ (Fintype.card α - A.card) := by
  classical
  rw [Nat.card_congr (idempotentsWithFixedSetEquivRetractions A),
    LinearInputF0Counting.supported_retraction_count]

/-- The Set-valued and Finset-valued fixed-point representations agree. -/
theorem fixedStates_eq_iff_fixedSet_eq {α : Type u} [Fintype α]
    (U S : α → α) :
    LinearInputStrangeFixedSets.FixedStates U =
      LinearInputStrangeFixedSets.FixedStates S ↔
    LinearInputF0Counting.fixedSet U = LinearInputF0Counting.fixedSet S := by
  constructor
  · intro h
    ext x
    simpa [LinearInputStrangeFixedSets.FixedStates,
      LinearInputF0Counting.fixedSet] using (Set.ext_iff.mp h x)
  · intro h
    ext x
    simpa [LinearInputStrangeFixedSets.FixedStates,
      LinearInputF0Counting.fixedSet] using (Finset.ext_iff.mp h x)

noncomputable def sameFixedSetMapsEquivFinset {α : Type u} [Fintype α]
    (S : α → α) :
    {U : α → α // LinearInputStrangeFixedSets.FixedStates U =
      LinearInputStrangeFixedSets.FixedStates S} ≃
      MapsWithFixedSet (LinearInputF0Counting.fixedSet S) := by
  classical
  refine
    { toFun := fun U =>
        ⟨U.1, (fixedStates_eq_iff_fixedSet_eq U.1 S).mp U.2⟩
      invFun := fun U =>
        ⟨U.1, (fixedStates_eq_iff_fixedSet_eq U.1 S).mpr U.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro U
    apply Subtype.ext
    rfl
  · intro U
    apply Subtype.ext
    rfl

noncomputable def sameFixedSetIdempotentsEquivFinset {α : Type u}
    [Fintype α] (S : α → α) :
    {U : α → α // LinearInputF0.Idempotent U ∧
      LinearInputStrangeFixedSets.FixedStates U =
        LinearInputStrangeFixedSets.FixedStates S} ≃
      IdempotentsWithFixedSet (LinearInputF0Counting.fixedSet S) := by
  classical
  refine
    { toFun := fun U =>
        ⟨U.1, U.2.1, (fixedStates_eq_iff_fixedSet_eq U.1 S).mp U.2.2⟩
      invFun := fun U =>
        ⟨U.1, U.2.1, (fixedStates_eq_iff_fixedSet_eq U.1 S).mpr U.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro U
    apply Subtype.ext
    rfl
  · intro U
    apply Subtype.ext
    rfl

/-- In the nonempty proper case, the closure characterization gives its map count. -/
theorem close_singleton_map_count {α : Type u} [Fintype α]
    (S : α → α)
    (hFixed : ∃ a : α, S a = a)
    (hActive : ∃ b : α, S b ≠ b) :
    Nat.card {U : α → α // U ∈
      LinearInputStrangeGalois.Close (LinearInputStrangeGalois.Stops (α := α))
        ({S} : Set (α → α))} =
      (Fintype.card α - 1) ^
        (Fintype.card α - (LinearInputF0Counting.fixedSet S).card) := by
  classical
  rw [LinearInputStrangeFixedSets.close_singleton_exact_fixed_set S hFixed hActive]
  simp only [Set.mem_ofPred_eq]
  rw [Nat.card_congr (sameFixedSetMapsEquivFinset S)]
  exact fixed_set_map_count (LinearInputF0Counting.fixedSet S)

/-- In the nonempty proper case, the closure's idempotents have the predicted count. -/
theorem close_singleton_idempotent_count {α : Type u} [Fintype α]
    (S : α → α)
    (hFixed : ∃ a : α, S a = a)
    (hActive : ∃ b : α, S b ≠ b) :
    Nat.card {U : α → α // LinearInputF0.Idempotent U ∧ U ∈
      LinearInputStrangeGalois.Close (LinearInputStrangeGalois.Stops (α := α))
        ({S} : Set (α → α))} =
      (LinearInputF0Counting.fixedSet S).card ^
        (Fintype.card α - (LinearInputF0Counting.fixedSet S).card) := by
  classical
  rw [LinearInputStrangeFixedSets.close_singleton_exact_fixed_set S hFixed hActive]
  simp only [Set.mem_ofPred_eq]
  rw [Nat.card_congr (sameFixedSetIdempotentsEquivFinset S)]
  exact fixed_set_idempotent_count (LinearInputF0Counting.fixedSet S)

private def univSubtypeEquiv {β : Type*} :
    {x : β // x ∈ Set.univ} ≃ β where
  toFun x := x.1
  invFun x := ⟨x, Set.mem_univ x⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def univIdempotentSubtypeEquiv {α : Type u} :
    {U : α → α // LinearInputF0.Idempotent U ∧ U ∈ Set.univ} ≃
      {U : α → α // LinearInputF0.Idempotent U} where
  toFun U := ⟨U.1, U.2.1⟩
  invFun U := ⟨U.1, U.2, Set.mem_univ U.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The empty fixed-set boundary has no stopping tests, hence universal closure. -/
theorem close_singleton_map_count_of_no_fixed {α : Type u} [Fintype α]
    (S : α → α) (hNone : ∀ x : α, S x ≠ x) :
    Nat.card {U : α → α // U ∈
      LinearInputStrangeGalois.Close (LinearInputStrangeGalois.Stops (α := α))
        ({S} : Set (α → α))} =
      (Fintype.card α) ^ (Fintype.card α) := by
  classical
  rw [LinearInputStrangeFixedSets.close_singleton_top_of_no_fixed S hNone]
  calc
    Nat.card {U : α → α // U ∈ Set.univ} = Nat.card (α → α) :=
      Nat.card_congr univSubtypeEquiv
    _ = (Fintype.card α) ^ (Fintype.card α) := by
      rw [Nat.card_fun]
      simp only [Nat.card_eq_fintype_card]

/-- The full fixed-set boundary also has universal closure. -/
theorem close_singleton_map_count_of_all_fixed {α : Type u} [Fintype α]
    (S : α → α) (hAll : ∀ x : α, S x = x) :
    Nat.card {U : α → α // U ∈
      LinearInputStrangeGalois.Close (LinearInputStrangeGalois.Stops (α := α))
        ({S} : Set (α → α))} =
      (Fintype.card α) ^ (Fintype.card α) := by
  classical
  rw [LinearInputStrangeFixedSets.close_singleton_top_of_all_fixed S hAll]
  calc
    Nat.card {U : α → α // U ∈ Set.univ} = Nat.card (α → α) :=
      Nat.card_congr univSubtypeEquiv
    _ = (Fintype.card α) ^ (Fintype.card α) := by
      rw [Nat.card_fun]
      simp only [Nat.card_eq_fintype_card]

/-- With no fixed states the closure is universal, so it counts all idempotents. -/
theorem close_singleton_idempotent_count_of_no_fixed {α : Type u}
    [Fintype α] (S : α → α) (hNone : ∀ x : α, S x ≠ x) :
    Nat.card {U : α → α // LinearInputF0.Idempotent U ∧ U ∈
      LinearInputStrangeGalois.Close (LinearInputStrangeGalois.Stops (α := α))
        ({S} : Set (α → α))} =
      ∑ r : Fin (Fintype.card α + 1),
        (Fintype.card α).choose r.val * r.val ^ (Fintype.card α - r.val) := by
  classical
  rw [LinearInputStrangeFixedSets.close_singleton_top_of_no_fixed S hNone]
  calc
    Nat.card {U : α → α // LinearInputF0.Idempotent U ∧ U ∈ Set.univ} =
        Nat.card {U : α → α // LinearInputF0.Idempotent U} :=
      Nat.card_congr univIdempotentSubtypeEquiv
    _ = _ := LinearInputF0Counting.idempotent_count_sum α

/-- With every state fixed the closure is universal, so it counts all idempotents. -/
theorem close_singleton_idempotent_count_of_all_fixed {α : Type u}
    [Fintype α] (S : α → α) (hAll : ∀ x : α, S x = x) :
    Nat.card {U : α → α // LinearInputF0.Idempotent U ∧ U ∈
      LinearInputStrangeGalois.Close (LinearInputStrangeGalois.Stops (α := α))
        ({S} : Set (α → α))} =
      ∑ r : Fin (Fintype.card α + 1),
        (Fintype.card α).choose r.val * r.val ^ (Fintype.card α - r.val) := by
  classical
  rw [LinearInputStrangeFixedSets.close_singleton_top_of_all_fixed S hAll]
  calc
    Nat.card {U : α → α // LinearInputF0.Idempotent U ∧ U ∈ Set.univ} =
        Nat.card {U : α → α // LinearInputF0.Idempotent U} :=
      Nat.card_congr univIdempotentSubtypeEquiv
    _ = _ := LinearInputF0Counting.idempotent_count_sum α

end LinearInputStrangeCounting
