/-!
# Independent product operator systems

Two deterministic labelled systems can be combined without assuming any
interaction between their state coordinates. We show that arbitrary
interleavings of left/right actions are observationally indistinguishable
exactly when the corresponding component systems are indistinguishable.

This gives a composition theorem for the predictive kernel, a proof
of independence/commutation of actions, and exact state reconstruction
when both component observation languages separate states.
-/

noncomputable section

namespace LinearInputOperatorProducts

open LinearInputOperatorWords

/-- Product action language: each letter touches exactly one coordinate. -/
def productStep {α β ι κ : Type*}
    (step : ι → α → α) (update : κ → β → β) :
    Sum ι κ → (α × β) → (α × β)
  | Sum.inl i, (x,y) => (step i x,y)
  | Sum.inr j, (x,y) => (x,update j y)

/-- Extract the left actions from a mixed product-program word. -/
def leftWord {ι κ : Type*} : List (Sum ι κ) → List ι
  | [] => []
  | Sum.inl i :: word => i :: leftWord word
  | Sum.inr _ :: word => leftWord word

/-- Extract the right actions from a mixed product-program word. -/
def rightWord {ι κ : Type*} : List (Sum ι κ) → List κ
  | [] => []
  | Sum.inl _ :: word => rightWord word
  | Sum.inr j :: word => j :: rightWord word

theorem leftWord_nil {ι κ : Type*} :
    leftWord ([] : List (Sum ι κ)) = [] := rfl

theorem rightWord_nil {ι κ : Type*} :
    rightWord ([] : List (Sum ι κ)) = [] := rfl

theorem leftWord_cons_inl {ι κ : Type*} (i : ι)
    (w : List (Sum ι κ)) :
    leftWord (Sum.inl i :: w) = i :: leftWord w := rfl

theorem leftWord_cons_inr {ι κ : Type*} (j : κ)
    (w : List (Sum ι κ)) :
    leftWord (Sum.inr j :: w) = leftWord w := rfl

theorem rightWord_cons_inl {ι κ : Type*} (i : ι)
    (w : List (Sum ι κ)) :
    rightWord (Sum.inl i :: w) = rightWord w := rfl

theorem rightWord_cons_inr {ι κ : Type*} (j : κ)
    (w : List (Sum ι κ)) :
    rightWord (Sum.inr j :: w) = j :: rightWord w := rfl

/-- Arbitrary mixed programs project onto their left component program. -/
theorem run_fst {α β ι κ : Type*}
    (step : ι → α → α) (update : κ → β → β)
    (word : List (Sum ι κ)) (x : α) (y : β) :
    (run (productStep step update) word (x,y)).1 =
      run step (leftWord word) x := by
  induction word generalizing x y with
  | nil => rfl
  | cons tag tail ih =>
      cases tag with
      | inl i =>
          change (run (productStep step update) tail (step i x,y)).1 =
            run step (leftWord tail) (step i x)
          exact ih (step i x) y
      | inr j =>
          change (run (productStep step update) tail (x,update j y)).1 =
            run step (leftWord tail) x
          exact ih x (update j y)

/-- Arbitrary mixed programs project onto their right component program. -/
theorem run_snd {α β ι κ : Type*}
    (step : ι → α → α) (update : κ → β → β)
    (word : List (Sum ι κ)) (x : α) (y : β) :
    (run (productStep step update) word (x,y)).2 =
      run update (rightWord word) y := by
  induction word generalizing x y with
  | nil => rfl
  | cons tag tail ih =>
      cases tag with
      | inl i =>
          change (run (productStep step update) tail (step i x,y)).2 =
            run update (rightWord tail) y
          exact ih (step i x) y
      | inr j =>
          change (run (productStep step update) tail (x,update j y)).2 =
            run update (rightWord tail) (update j y)
          exact ih x (update j y)

theorem run_product {α β ι κ : Type*}
    (step : ι → α → α) (update : κ → β → β)
    (word : List (Sum ι κ)) (x : α) (y : β) :
    run (productStep step update) word (x,y) =
      (run step (leftWord word) x, run update (rightWord word) y) := by
  apply Prod.ext
  · exact run_fst step update word x y
  · exact run_snd step update word x y

theorem leftWord_map {ι κ : Type*} (word : List ι) :
    leftWord (word.map (Sum.inl : ι → Sum ι κ)) = word := by
  induction word with
  | nil => rfl
  | cons i tail ih =>
      simpa [leftWord] using congrArg (List.cons i) ih

theorem rightWord_map {ι κ : Type*} (word : List κ) :
    rightWord (word.map (Sum.inr : κ → Sum ι κ)) = word := by
  induction word with
  | nil => rfl
  | cons j tail ih =>
      simpa [rightWord] using congrArg (List.cons j) ih

theorem rightWord_left_map {ι κ : Type*} (word : List ι) :
    rightWord (word.map (Sum.inl : ι → Sum ι κ)) = [] := by
  induction word with
  | nil => rfl
  | cons i tail ih =>
      simpa [rightWord] using ih

theorem leftWord_right_map {ι κ : Type*} (word : List κ) :
    leftWord (word.map (Sum.inr : κ → Sum ι κ)) = [] := by
  induction word with
  | nil => rfl
  | cons j tail ih =>
      simpa [leftWord] using ih

/-- Product observational equivalence is precisely component equivalence. -/
theorem product_wordEq_iff {α β ω ν ι κ : Type*}
    (K : α → ω) (L : β → ν)
    (step : ι → α → α) (update : κ → β → β)
    (x x' : α) (y y' : β) :
    WordEq (fun p : α × β => (K p.1, L p.2))
      (productStep step update) (x,y) (x',y') ↔
      WordEq K step x x' ∧ WordEq L update y y' := by
  constructor
  · intro h
    constructor
    · intro word
      have h0 := h (word.map (Sum.inl : ι → Sum ι κ))
      have h1 := congrArg Prod.fst h0
      simpa only [run_fst, leftWord_map] using h1
    · intro word
      have h0 := h (word.map (Sum.inr : κ → Sum ι κ))
      have h1 := congrArg Prod.snd h0
      simpa only [run_snd, rightWord_map] using h1
  · rintro ⟨hK, hL⟩ word
    apply Prod.ext
    · simpa only [run_fst] using hK (leftWord word)
    · simpa only [run_snd] using hL (rightWord word)

/-- No product program can distinguish old component-equivalent states. -/
theorem product_preserves_left {α β ω ν ι κ : Type*}
    (K : α → ω) (L : β → ν)
    (step : ι → α → α) (update : κ → β → β)
    {x x' : α} {y y' : β}
    (hx : WordEq K step x x') (hy : WordEq L update y y') :
    WordEq (fun p : α × β => (K p.1, L p.2))
      (productStep step update) (x,y) (x',y') :=
  (product_wordEq_iff K L step update x x' y y').2 ⟨hx,hy⟩

/-- A product program can distinguish a pair only if one component can. -/
theorem product_neq_implies_component_neq {α β ω ν ι κ : Type*}
    (K : α → ω) (L : β → ν)
    (step : ι → α → α) (update : κ → β → β)
    (x x' : α) (y y' : β)
    (h : ¬ WordEq (fun p : α × β => (K p.1, L p.2))
       (productStep step update) (x,y) (x',y')) :
    ¬ WordEq K step x x' ∨ ¬ WordEq L update y y' := by
  classical
  by_contra hnot
  push Not at hnot
  exact h ((product_wordEq_iff K L step update x x' y y').2
    ⟨hnot.1, hnot.2⟩)

/-- Orthogonal component actions commute exactly on the product space. -/
theorem independent_actions_commute {α β ι κ : Type*}
    (step : ι → α → α) (update : κ → β → β)
    (i : ι) (j : κ) (p : α × β) :
    productStep step update (Sum.inl i)
      (productStep step update (Sum.inr j) p) =
    productStep step update (Sum.inr j)
      (productStep step update (Sum.inl i) p) := by
  cases p
  rfl

/-- Either execution order of independent actions has identical semantics. -/
theorem independent_two_letter_words {α β ι κ : Type*}
    (step : ι → α → α) (update : κ → β → β)
    (i : ι) (j : κ) (p : α × β) :
    run (productStep step update) [Sum.inl i, Sum.inr j] p =
      run (productStep step update) [Sum.inr j, Sum.inl i] p := by
  cases p
  rfl

/-- Product observational equivalence is equality when both component
observation languages fully separate their original states. -/
theorem product_wordEq_implies_eq {α β ω ν ι κ : Type*}
    (K : α → ω) (L : β → ν)
    (step : ι → α → α) (update : κ → β → β)
    (hK : ∀ x x', WordEq K step x x' → x = x')
    (hL : ∀ y y', WordEq L update y y' → y = y')
    {p q : α × β}
    (h : WordEq (fun a : α × β => (K a.1, L a.2))
      (productStep step update) p q) : p = q := by
  cases p with
  | mk x y =>
    cases q with
    | mk x' y' =>
      obtain ⟨hx,hy⟩ :=
        (product_wordEq_iff K L step update x x' y y').1 h
      exact Prod.ext (hK x x' hx) (hL y y' hy)

/-- The canonical product predictive quotient identifies precisely pairs
of componentwise equivalent states. -/
theorem product_encode_eq_iff {α β ω ν ι κ : Type*}
    (K : α → ω) (L : β → ν)
    (step : ι → α → α) (update : κ → β → β)
    (x x' : α) (y y' : β) :
    encode (fun p : α × β => (K p.1,L p.2))
      (productStep step update) (x,y) =
    encode (fun p : α × β => (K p.1,L p.2))
      (productStep step update) (x',y') ↔
      encode K step x = encode K step x' ∧
        encode L update y = encode L update y' := by
  constructor
  · intro h
    have hp : WordEq (fun p : α × β => (K p.1,L p.2))
        (productStep step update) (x,y) (x',y') :=
      (encode_eq_iff _ _ _ _).1 h
    obtain ⟨hK,hL⟩ := (product_wordEq_iff K L step update x x' y y').1 hp
    exact ⟨(encode_eq_iff K step x x').2 hK,
      (encode_eq_iff L update y y').2 hL⟩
  · rintro ⟨hK,hL⟩
    apply (encode_eq_iff _ _ _ _).2
    exact (product_wordEq_iff K L step update x x' y y').2
      ⟨(encode_eq_iff K step x x').1 hK,
        (encode_eq_iff L update y y').1 hL⟩

end LinearInputOperatorProducts
