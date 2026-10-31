/-!
# Finite-horizon discovery of all future-observable distinctions

With N finite states and r distinct initial observations, the complete
future-equivalence is determined by the first N-r+1 observations
(at indices 0,1,...,N-r).  The proof counts distinct trace profiles.

This uses the fixed deterministic transition U and observer K.
It does not assume a self-adapting observer or nonstationary transitions.
-/

noncomputable section

namespace LinearInputFutureHorizon

open LinearInputFutureObservation
attribute [local instance] Classical.decEq

/-- The same observations through every instant 0,...,n. -/
def HorizonEq {α ω : Type*} (K : α → ω) (U : α → α)
    (n : ℕ) (x y : α) : Prop :=
  ∀ t : ℕ, t ≤ n → K (U^[t] x) = K (U^[t] y)

theorem future_implies_horizon {α ω : Type*} {K : α → ω} {U : α → α}
    {x y : α} (h : FutureEq K U x y) (n : ℕ) :
    HorizonEq K U n x y := by
  intro t ht
  exact h t

theorem horizon_mono {α ω : Type*} {K : α → ω} {U : α → α}
    {x y : α} {m n : ℕ} (hmn : m ≤ n)
    (h : HorizonEq K U n x y) : HorizonEq K U m x y := by
  intro t ht
  exact h t (by omega)

/-- A one-step longer horizon covers the old horizon after one update. -/
theorem horizon_shift {α ω : Type*} {K : α → ω} {U : α → α}
    {x y : α} {n : ℕ} (h : HorizonEq K U (n + 1) x y) :
    HorizonEq K U n (U x) (U y) := by
  intro t ht
  simpa only [Function.iterate_succ_apply] using h (t + 1) (by omega)

/-- Once a horizon partition is update-stable, no future observation
can distinguish any pair it has merged. -/
theorem stable_implies_future {α ω : Type*} {K : α → ω} {U : α → α}
    (n : ℕ)
    (hst : ∀ x y, HorizonEq K U n x y → HorizonEq K U (n + 1) x y)
    {x y : α} (hxy : HorizonEq K U n x y) :
    FutureEq K U x y := by
  have hstep : ∀ a b, HorizonEq K U n a b → HorizonEq K U n (U a) (U b) := by
    intro a b hab
    exact horizon_shift (hst a b hab)
  have hiter : ∀ t : ℕ, HorizonEq K U n (U^[t] x) (U^[t] y) := by
    intro t
    induction t with
    | zero => simpa only [Function.iterate_zero, id_eq] using hxy
    | succ t ih =>
        simpa only [Function.iterate_succ_apply'] using hstep _ _ ih
  intro t
  have ht := hiter t 0 (Nat.zero_le n)
  simpa only [Function.iterate_zero, id_eq] using ht

/-- The observation profile has n+1 entries. -/
def profile {α ω : Type*} (K : α → ω) (U : α → α)
    (n : ℕ) (x : α) : Fin (n + 1) → ω :=
  fun t => K (U^[t.val] x)

theorem profile_eq_iff_horizon {α ω : Type*}
    (K : α → ω) (U : α → α) (n : ℕ) (x y : α) :
    profile K U n x = profile K U n y ↔ HorizonEq K U n x y := by
  constructor
  · intro h t ht
    have hi : t < n + 1 := by omega
    exact congrFun h ⟨t, hi⟩
  · intro h
    funext i
    exact h i.val (by omega)

/-- Forget the last component of a finite trace. -/
def truncate {ω : Type*} (n : ℕ) (v : Fin (n + 2) → ω) :
    Fin (n + 1) → ω :=
  fun i => v ⟨i.val, by omega⟩

/-- The finite set of possible observation profiles. -/
noncomputable def profiles {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (n : ℕ) :
    Finset (Fin (n + 1) → ω) := by
  classical
  exact (Finset.univ : Finset α).image (profile K U n)

/-- Number of distinct observable histories up to horizon n. -/
noncomputable def rank {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (n : ℕ) : ℕ :=
  (profiles K U n).card

theorem profiles_succ_image {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (n : ℕ) :
    (profiles K U (n + 1)).image (truncate n) = profiles K U n := by
  classical
  unfold profiles
  rw [Finset.image_image]
  congr 1
  funext x i
  rfl

theorem rank_le_card {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (n : ℕ) :
    rank K U n ≤ Fintype.card α := by
  classical
  change ((Finset.univ : Finset α).image (profile K U n)).card ≤
    (Finset.univ : Finset α).card
  exact Finset.card_image_le

theorem rank_mono {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (n : ℕ) :
    rank K U n ≤ rank K U (n + 1) := by
  classical
  change (profiles K U n).card ≤ (profiles K U (n + 1)).card
  rw [← profiles_succ_image K U n]
  exact Finset.card_image_le

/-- If the number of observable profiles did not increase, every pair
indistinguishable through n remains so through n+1. -/
theorem rank_eq_refines {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (n : ℕ)
    (heq : rank K U n = rank K U (n + 1))
    (x y : α) (hxy : HorizonEq K U n x y) :
    HorizonEq K U (n + 1) x y := by
  classical
  have hcard :
      ((profiles K U (n + 1)).image (truncate n)).card =
        (profiles K U (n + 1)).card := by
    rw [profiles_succ_image]
    exact heq
  have hinj : Set.InjOn (truncate n) ↑(profiles K U (n + 1)) :=
    Finset.injOn_of_card_image_eq hcard
  have hx : profile K U (n + 1) x ∈ profiles K U (n + 1) := by
    unfold profiles
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hy : profile K U (n + 1) y ∈ profiles K U (n + 1) := by
    unfold profiles
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩
  have ht :
      truncate n (profile K U (n + 1) x) =
      truncate n (profile K U (n + 1) y) := by
    change profile K U n x = profile K U n y
    exact (profile_eq_iff_horizon K U n x y).2 hxy
  exact (profile_eq_iff_horizon K U (n + 1) x y).1 (hinj hx hy ht)

/-- Equality of profile counts at adjacent horizons implies full stability. -/
theorem rank_eq_implies_future {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (n : ℕ)
    (heq : rank K U n = rank K U (n + 1))
    {x y : α} (hxy : HorizonEq K U n x y) :
    FutureEq K U x y := by
  apply stable_implies_future n (fun a b hab => rank_eq_refines K U n heq a b hab)
  exact hxy

/-- Absent a complete horizon, the number of distinct profiles must grow. -/
theorem rank_grows_if_incomplete {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (n : ℕ)
    (hbad : ¬ ∀ x y, HorizonEq K U n x y → FutureEq K U x y) :
    rank K U n < rank K U (n + 1) := by
  have hle := rank_mono K U n
  by_contra hnot
  have heq : rank K U n = rank K U (n + 1) := by omega
  exact hbad (fun x y hxy => rank_eq_implies_future K U n heq hxy)

/-- Either the horizon is already complete, or at least n new profile
classes have been distinguished since time zero. -/
theorem horizon_or_rank_growth {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (n : ℕ) :
    (∀ x y, HorizonEq K U n x y → FutureEq K U x y) ∨
    rank K U 0 + n ≤ rank K U n := by
  induction n with
  | zero =>
      right
      omega
  | succ n ih =>
      by_cases hs : ∀ x y, HorizonEq K U (n + 1) x y → FutureEq K U x y
      · exact Or.inl hs
      · right
        have hprev : ¬ ∀ x y, HorizonEq K U n x y → FutureEq K U x y := by
          intro hp
          apply hs
          intro x y hxy
          exact hp x y (horizon_mono (Nat.le_succ n) hxy)
        rcases ih with hp | hg
        · exact False.elim (hprev hp)
        · have hstrict := rank_grows_if_incomplete K U n hprev
          omega

/-- Main finite bound. Let N be the original number of states and let
r = rank K U 0 be the number of distinct current observations.
No distinction first visible after time N-r can exist. -/
theorem finite_horizon_complete {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) {x y : α}
    (hxy : HorizonEq K U (Fintype.card α - rank K U 0) x y) :
    FutureEq K U x y := by
  classical
  let n := Fintype.card α - rank K U 0
  have h0 : rank K U 0 ≤ Fintype.card α := rank_le_card K U 0
  rcases horizon_or_rank_growth K U n with hs | hg
  · exact hs x y hxy
  · by_contra hnot
    have hbad : ¬ ∀ a b, HorizonEq K U n a b → FutureEq K U a b := by
      intro hp
      exact hnot (hp x y hxy)
    have hstrict := rank_grows_if_incomplete K U n hbad
    have hu := rank_le_card K U (n + 1)
    dsimp [n] at hg hstrict hu
    omega

/-- Explicit finite characterization of the canonical predictive kernel. -/
theorem future_iff_finite_horizon {α ω : Type*} [Fintype α]
    (K : α → ω) (U : α → α) (x y : α) :
    FutureEq K U x y ↔
    HorizonEq K U (Fintype.card α - rank K U 0) x y := by
  constructor
  · intro h
    exact future_implies_horizon h _
  · exact finite_horizon_complete K U

end LinearInputFutureHorizon
