/-!
# Finite distinguishability horizon for arbitrary operator words

This is the multi-action counterpart of FutureFiniteHorizon.
For a finite original state space, finitely many levels of operator words
suffice to identify exactly the full observational kernel, even with
infinitely many named actions (the resulting profiles still form a finite
image of the state space).

Let N be the number of original states, r the number of distinct
immediate readouts. All words of length at most N-r suffice to distinguish
every pair distinguishable by an arbitrary finite word.

No fixed transition, commutativity, reversibility, or probabilistic
assumptions are imposed.
-/

noncomputable section

namespace LinearInputOperatorHorizon

open LinearInputOperatorWords

/-- Output equality for all operator words of length at most n. -/
def HorizonEq {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (n : ℕ) (x y : α) : Prop :=
  ∀ word : List ι, word.length ≤ n →
    K (run step word x) = K (run step word y)

/-- An observation profile indexed by all words of length at most n. -/
def profile {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (n : ℕ) (x : α) :
    {word : List ι // word.length ≤ n} → ω :=
  fun word => K (run step word.val x)

theorem profile_eq_iff_horizon {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (n : ℕ) (x y : α) :
    profile K step n x = profile K step n y ↔
      HorizonEq K step n x y := by
  constructor
  · intro h word hw
    exact congrFun h ⟨word, hw⟩
  · intro h
    funext word
    exact h word.val word.property

/-- Equality of the complete language always implies a bounded horizon. -/
theorem word_implies_horizon {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    {x y : α} (h : WordEq K step x y) (n : ℕ) :
    HorizonEq K step n x y := by
  intro word _
  exact h word

theorem horizon_mono {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    {m n : ℕ} (hmn : m ≤ n) {x y : α}
    (h : HorizonEq K step n x y) :
    HorizonEq K step m x y := by
  intro word hw
  exact h word (by omega)

/-- A horizon of length zero is exactly one immediate readout. -/
theorem horizon_zero_iff_now {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (x y : α) :
    HorizonEq K step 0 x y ↔ K x = K y := by
  constructor
  · intro h
    simpa [run] using h [] (by simp)
  · intro h word hw
    have he : word = [] := by
      cases word with
      | nil => rfl
      | cons i rest => simp at hw
    subst word
    simpa [run] using h

/-- A one-longer trace controls every one-action successor trace. -/
theorem horizon_step {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (n : ℕ) {x y : α} (h : HorizonEq K step (n+1) x y)
    (i : ι) :
    HorizonEq K step n (step i x) (step i y) := by
  intro word hw
  have hcons := h (i :: word) (by simp only [List.length_cons]; omega)
  simpa only [run_cons] using hcons

/-- If adjacent horizon equivalences coincide, the bounded relation is
already preserved by every action, hence by every finite word. -/
theorem stable_implies_word {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (n : ℕ)
    (hstable : ∀ x y, HorizonEq K step n x y →
      HorizonEq K step (n+1) x y)
    {x y : α} (hxy : HorizonEq K step n x y) :
    WordEq K step x y := by
  have hstep : ∀ i a b, HorizonEq K step n a b →
      HorizonEq K step n (step i a) (step i b) := by
    intro i a b hab
    exact horizon_step K step n (hstable a b hab) i
  have hAll : ∀ word : List ι, ∀ a b : α,
      HorizonEq K step n a b →
        K (run step word a) = K (run step word b) := by
    intro word
    induction word with
    | nil =>
        intro a b hab
        simpa [run] using hab [] (by simp)
    | cons i rest ih =>
        intro a b hab
        change K (run step rest (step i a)) =
          K (run step rest (step i b))
        exact ih (step i a) (step i b) (hstep i a b hab)
  intro word
  exact hAll word x y hxy

/-- Inclusion of horizons does not decrease the number of distinct profiles. -/
def truncate {ι ω : Type*} (n : ℕ)
    (v : {w : List ι // w.length ≤ n+1} → ω) :
    {w : List ι // w.length ≤ n} → ω :=
  fun w => v ⟨w.val, by omega⟩

noncomputable def profiles {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (n : ℕ) :
    Finset ({word : List ι // word.length ≤ n} → ω) := by
  classical
  exact (Finset.univ : Finset α).image (profile K step n)

/-- Number of distinct state signatures for words up to length n. -/
noncomputable def rank {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (n : ℕ) : ℕ :=
  (profiles K step n).card

theorem profiles_succ_image {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (n : ℕ) :
    (profiles K step (n+1)).image (truncate n) =
      profiles K step n := by
  classical
  unfold profiles
  rw [Finset.image_image]
  congr 1

theorem rank_le_card {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (n : ℕ) :
    rank K step n ≤ Fintype.card α := by
  classical
  change ((Finset.univ : Finset α).image (profile K step n)).card ≤
    (Finset.univ : Finset α).card
  exact Finset.card_image_le

theorem rank_mono {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (n : ℕ) :
    rank K step n ≤ rank K step (n+1) := by
  classical
  change (profiles K step n).card ≤ (profiles K step (n+1)).card
  rw [← profiles_succ_image K step n]
  exact Finset.card_image_le

/-- If signature counts stop increasing, the new horizon has no more classes. -/
theorem rank_eq_refines {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (n : ℕ)
    (heq : rank K step n = rank K step (n+1))
    (x y : α) (hxy : HorizonEq K step n x y) :
    HorizonEq K step (n+1) x y := by
  classical
  have hcard :
      ((profiles K step (n+1)).image (truncate n)).card =
        (profiles K step (n+1)).card := by
    rw [profiles_succ_image]
    exact heq
  have hinj := Finset.injOn_of_card_image_eq hcard
  have hx : profile K step (n+1) x ∈ profiles K step (n+1) := by
    unfold profiles
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hy : profile K step (n+1) y ∈ profiles K step (n+1) := by
    unfold profiles
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩
  have ht :
      truncate n (profile K step (n+1) x) =
        truncate n (profile K step (n+1) y) := by
    change profile K step n x = profile K step n y
    exact (profile_eq_iff_horizon K step n x y).2 hxy
  exact (profile_eq_iff_horizon K step (n+1) x y).1
    (hinj hx hy ht)

/-- A plateau in signature counts certifies all future word distinctions. -/
theorem rank_plateau_complete {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (n : ℕ)
    (heq : rank K step n = rank K step (n+1))
    {x y : α} (hxy : HorizonEq K step n x y) :
    WordEq K step x y := by
  exact stable_implies_word K step n
    (fun a b hab => rank_eq_refines K step n heq a b hab) hxy

/-- While the horizon is incomplete, the partition must strictly refine. -/
theorem rank_grows_if_incomplete {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (n : ℕ)
    (hbad : ¬ ∀ x y, HorizonEq K step n x y → WordEq K step x y) :
    rank K step n < rank K step (n+1) := by
  have hle := rank_mono K step n
  by_contra hnot
  have heq : rank K step n = rank K step (n+1) := by omega
  exact hbad (fun x y hxy => rank_plateau_complete K step n heq hxy)

/-- Either the current signatures are sufficient, or their rank has grown
by at least one at each preceding horizon refinement. -/
theorem horizon_or_rank_growth {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (n : ℕ) :
    (∀ x y, HorizonEq K step n x y → WordEq K step x y) ∨
      rank K step 0 + n ≤ rank K step n := by
  induction n with
  | zero =>
      right
      omega
  | succ n ih =>
      by_cases hs : ∀ x y, HorizonEq K step (n+1) x y →
          WordEq K step x y
      · exact Or.inl hs
      · right
        have hprev : ¬ ∀ x y, HorizonEq K step n x y →
            WordEq K step x y := by
          intro hp
          apply hs
          intro x y hxy
          exact hp x y (horizon_mono K step (Nat.le_succ n) hxy)
        rcases ih with hp | hg
        · exact False.elim (hprev hp)
        · have hstrict := rank_grows_if_incomplete K step n hprev
          omega

/-- For a finite state space, length N-r always suffices, where N is the
number of states and r is the number of distinct immediate outputs. -/
theorem finite_horizon_complete {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) {x y : α}
    (hxy : HorizonEq K step (Fintype.card α - rank K step 0) x y) :
    WordEq K step x y := by
  classical
  let n := Fintype.card α - rank K step 0
  have h0 : rank K step 0 ≤ Fintype.card α := rank_le_card K step 0
  rcases horizon_or_rank_growth K step n with hs | hg
  · exact hs x y hxy
  · by_contra hnot
    have hbad : ¬ ∀ a b, HorizonEq K step n a b →
        WordEq K step a b := by
      intro hp
      exact hnot (hp x y hxy)
    have hstrict := rank_grows_if_incomplete K step n hbad
    have hu := rank_le_card K step (n+1)
    dsimp [n] at hg hstrict hu
    omega

/-- Finite certificates characterize full observational equivalence exactly. -/
theorem wordEq_iff_finite_horizon {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (x y : α) :
    WordEq K step x y ↔
      HorizonEq K step (Fintype.card α - rank K step 0) x y := by
  constructor
  · intro h
    exact word_implies_horizon K step h _
  · exact finite_horizon_complete K step

/-- A pair of states separated by any word is separated by a short word. -/
theorem separating_short_word {α ω ι : Type*} [Fintype α]
    (K : α → ω) (step : ι → α → α) (x y : α)
    (h : ¬ WordEq K step x y) :
    ∃ word : List ι,
      word.length ≤ Fintype.card α - rank K step 0 ∧
      K (run step word x) ≠ K (run step word y) := by
  classical
  have hs : ¬ HorizonEq K step
      (Fintype.card α - rank K step 0) x y := by
    intro hh
    exact h (finite_horizon_complete K step hh)
  simp only [HorizonEq, not_forall, not_imp] at hs
  exact hs

end LinearInputOperatorHorizon
