/-! Counting actual finite idempotent maps by their fixed-point sets. -/

noncomputable section
open Finset

namespace LinearInputF0Counting

open LinearInputF0
attribute [local instance] Classical.propDecidable

def RetractionOn {α : Type*} (A : Finset α) (K : α → α) : Prop :=
  (∀ x ∈ A, K x = x) ∧ ∀ x, K x ∈ A

abbrev SupportedRetraction {α : Type*} (A : Finset α) := {K : α → α // RetractionOn A K}

def extendRetraction {α : Type*} (A : Finset α) (f : {x : α // x ∉ A} → {x : α // x ∈ A})
    (x : α) : α := if h : x ∈ A then x else (f ⟨x, h⟩).val

theorem extend_retracts {α : Type*} (A : Finset α)
    (f : {x : α // x ∉ A} → {x : α // x ∈ A}) : RetractionOn A (extendRetraction A f) := by
  constructor
  · intro x hx; simp [extendRetraction, hx]
  · intro x
    unfold extendRetraction
    split_ifs with hx
    · exact hx
    · exact (f ⟨x, hx⟩).property

def supportedChoicesEquiv {α : Type*} (A : Finset α) :
    SupportedRetraction A ≃ ({x : α // x ∉ A} → {x : α // x ∈ A}) where
  toFun K x := ⟨K.val x.val, K.property.2 x.val⟩
  invFun f := ⟨extendRetraction A f, extend_retracts A f⟩
  left_inv K := by
    apply Subtype.ext
    funext x
    change (if x ∈ A then x else K.val x) = K.val x
    split_ifs with hx
    · exact (K.property.1 x hx).symm
    · rfl
  right_inv f := by
    funext x
    apply Subtype.ext
    simp only [extendRetraction, dif_neg x.property]

theorem supported_retraction_count {α : Type*} [Fintype α] (A : Finset α) :
    Nat.card (SupportedRetraction A) = A.card ^ (Fintype.card α - A.card) := by
  classical
  rw [Nat.card_congr (supportedChoicesEquiv A), Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]

theorem supported_idempotent {α : Type*} {A : Finset α} (K : SupportedRetraction A) :
    Idempotent K.val := by intro x; exact K.property.1 (K.val x) (K.property.2 x)

def fixedSet {α : Type*} [Fintype α] (K : α → α) : Finset α :=
  Finset.univ.filter (fun x => K x = x)

theorem mem_fixedSet {α : Type*} [Fintype α] (K : α → α) (x : α) :
    x ∈ fixedSet K ↔ K x = x := by simp [fixedSet]

theorem fixedSet_supported {α : Type*} [Fintype α] {A : Finset α}
    (K : SupportedRetraction A) : fixedSet K.val = A := by
  ext x
  rw [mem_fixedSet]
  constructor
  · intro h; rw [← h]; exact K.property.2 x
  · exact K.property.1 x

theorem idempotent_supported {α : Type*} [Fintype α] {K : α → α}
    (hK : Idempotent K) : RetractionOn (fixedSet K) K := by
  constructor
  · intro x hx; exact (mem_fixedSet K x).mp hx
  · intro x; exact (mem_fixedSet K (K x)).mpr (hK x)

abbrev RankedIdempotent (α : Type*) [Fintype α] (r : ℕ) :=
  {K : α → α // Idempotent K ∧ (fixedSet K).card = r}

def rankedChoicesEquiv (α : Type*) [Fintype α] (r : ℕ) :
    RankedIdempotent α r ≃ (Σ A : {s : Finset α // s.card = r}, SupportedRetraction A.val) where
  toFun K := ⟨⟨fixedSet K.val, K.property.2⟩, ⟨K.val, idempotent_supported K.property.1⟩⟩
  invFun v := ⟨v.2.val, supported_idempotent v.2, by rw [fixedSet_supported v.2]; exact v.1.property⟩
  left_inv _ := rfl
  right_inv v := by
    have hA := fixedSet_supported v.2
    apply Sigma.ext (Subtype.ext hA)
    exact subtype_heq (congrArg (fun A => RetractionOn A) hA) rfl

/-- Rank-r idempotents on a labelled finite set: choose roots, then attach all other points. -/
theorem idempotent_rank_count (α : Type*) [Fintype α] (r : ℕ) :
    Nat.card (RankedIdempotent α r) =
      (Fintype.card α).choose r * r ^ (Fintype.card α - r) := by
  classical
  rw [Nat.card_congr (rankedChoicesEquiv α r), Nat.card_sigma]
  calc
    (∑ A : {s : Finset α // s.card = r}, Nat.card (SupportedRetraction A.val)) =
        ∑ _A : {s : Finset α // s.card = r}, r ^ (Fintype.card α - r) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [supported_retraction_count, A.property]
    _ = _ := by simp [Fintype.card_finset_len]

def allRanksEquiv (α : Type*) [Fintype α] :
    {K : α → α // Idempotent K} ≃
      (Σ r : Fin (Fintype.card α + 1), RankedIdempotent α r.val) where
  toFun K := ⟨⟨(fixedSet K.val).card, by
    have h := Finset.card_le_card (Finset.subset_univ (fixedSet K.val))
    simp only [Finset.card_univ] at h
    omega⟩, ⟨K.val, K.property, rfl⟩⟩
  invFun v := ⟨v.2.val, v.2.property.1⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨r, hr⟩, ⟨K, hK, hc⟩⟩
    change (fixedSet K).card = r at hc
    subst r
    rfl

theorem idempotent_count_sum (α : Type*) [Fintype α] :
    Nat.card {K : α → α // Idempotent K} =
      ∑ r : Fin (Fintype.card α + 1),
        (Fintype.card α).choose r.val * r.val ^ (Fintype.card α - r.val) := by
  classical
  rw [Nat.card_congr (allRanksEquiv α), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  exact idempotent_rank_count α r.val

theorem seven_point_idempotents : Nat.card {K : Fin 7 → Fin 7 // Idempotent K} = 6322 := by
  rw [idempotent_count_sum]
  change (∑ r : Fin 8, Nat.choose 7 r.val * r.val ^ (7 - r.val)) = 6322
  norm_num [Fin.sum_univ_succ, Nat.choose]

theorem eight_point_idempotents : Nat.card {K : Fin 8 → Fin 8 // Idempotent K} = 41393 := by
  rw [idempotent_count_sum]
  change (∑ r : Fin 9, Nat.choose 8 r.val * r.val ^ (8 - r.val)) = 41393
  norm_num [Fin.sum_univ_succ, Nat.choose]

end LinearInputF0Counting
