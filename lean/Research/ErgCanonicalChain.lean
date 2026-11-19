import Mathlib.Tactic

/-!
# ERG `extends_main`: when the validator's checks describe a single linear chain

ERG-Aout's `docs/FORMALIZATION.md` requires the accepted-layer relation
`extends_main` to be acyclic and "a single linear canonical chain", and
`tool/validate_r001_kernel.py` enforces this by separate checks: acyclicity,
in-degree and out-degree at most one, exactly one start and one end, and every
main node reachable from the start along successor edges.

Here the main nodes form a finite type `V` and the edges are given by a partial
successor `next : V → Option V` (out-degree ≤ 1 is built in). We assume only

* `Injective`: in-degree ≤ 1 (`next x = some z → next y = some z → x = y`),
* a start `s` with no predecessor,
* every node is reached from `s` by iterating `next`,

and prove (`canonical_chain`) that the chain from `s` is an exact enumeration
`Fin |V| ≃ V` with `next (w i) = w (i+1)` and `next (w last) = none`. As
consequences, the remaining validator checks are implied: there is no cycle
(`no_cycle`), the start is unique (`start_unique`) and so is the end
(`end_unique`). Conversely an enumerated path satisfies the three assumptions
(`path_satisfies`).

This is a statement about the finite graph semantics of the validator, not a
verification of the Python code itself.
-/

namespace ErgCanonicalChain

variable {V : Type*}

/-- Iterating the partial successor from `x`. -/
def iter (next : V → Option V) : ℕ → V → Option V
  | 0, x => some x
  | k + 1, x => (iter next k x).bind next

/-- In-degree at most one. -/
def Injective (next : V → Option V) : Prop :=
  ∀ x y z, next x = some z → next y = some z → x = y

theorem iter_succ_left (next : V → Option V) (k : ℕ) (x : V) :
    iter next (k + 1) x = (next x).bind (iter next k) := by
  induction k generalizing x with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter, ih]
    cases next x <;> simp [iter]

theorem iter_add (next : V → Option V) (i j : ℕ) (x : V) :
    iter next (i + j) x = (iter next i x).bind (iter next j) := by
  induction j with
  | zero => cases iter next i x <;> simp [iter]
  | succ j ih =>
    rw [← Nat.add_assoc, iter, ih]
    cases iter next i x <;> simp [iter]

theorem iter_none_of_le (next : V → Option V) {x : V} {i j : ℕ} (hij : i ≤ j)
    (h : iter next i x = none) : iter next j x = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [iter_add, h]
  rfl

/-- Predecessors are unique along the chain: if two iterates agree, so do the previous ones. -/
theorem iter_pred_eq (next : V → Option V) (hinj : Injective next) {x : V} {i j : ℕ}
    {z : V} (hi : iter next (i + 1) x = some z) (hj : iter next (j + 1) x = some z) :
    iter next i x = iter next j x := by
  rw [iter] at hi hj
  cases hxi : iter next i x with
  | none => rw [hxi] at hi; cases hi
  | some u =>
    cases hxj : iter next j x with
    | none => rw [hxj] at hj; cases hj
    | some w =>
      rw [hxi] at hi; rw [hxj] at hj
      exact congrArg some (hinj u w z hi hj)

/-- From a start without predecessor, the chain never revisits a node. -/
theorem iter_injective (next : V → Option V) (hinj : Injective next) {s : V}
    (hs : ∀ x, next x ≠ some s) {i j : ℕ} {z : V} (hi : iter next i s = some z)
    (hj : iter next j s = some z) : i = j := by
  induction i generalizing j z with
  | zero =>
    rcases j with _ | j
    · rfl
    · exfalso
      simp only [iter] at hi
      cases hi
      rw [iter] at hj
      cases hk : iter next j s with
      | none => rw [hk] at hj; cases hj
      | some u => rw [hk] at hj; exact hs u hj
  | succ i ih =>
    rcases j with _ | j
    · exfalso
      simp only [iter] at hj
      cases hj
      rw [iter] at hi
      cases hk : iter next i s with
      | none => rw [hk] at hi; cases hi
      | some u => rw [hk] at hi; exact hs u hi
    · have hpred := iter_pred_eq next hinj hi hj
      cases hk : iter next i s with
      | none => simp [iter, hk] at hi
      | some u => rw [hk] at hpred; exact congrArg (· + 1) (ih hk hpred.symm)

/-- **No cycle** through the chain from the start: in particular `extends_main` is acyclic. -/
theorem no_cycle (next : V → Option V) (hinj : Injective next) {s : V}
    (hs : ∀ x, next x ≠ some s) (hreach : ∀ x, ∃ k, iter next k s = some x)
    (x : V) (k : ℕ) : iter next (k + 1) x ≠ some x := by
  intro hcyc
  obtain ⟨i, hi⟩ := hreach x
  have h2 : iter next (i + (k + 1)) s = some x := by
    rw [iter_add, hi]
    exact hcyc
  have := iter_injective next hinj hs hi h2
  omega

variable [Fintype V]

/-- The chain stops after at most `|V|` steps. -/
theorem iter_card_eq_none (next : V → Option V) (hinj : Injective next) {s : V}
    (hs : ∀ x, next x ≠ some s) : iter next (Fintype.card V) s = none := by
  by_contra hne
  have hall : ∀ k ≤ Fintype.card V, (iter next k s).isSome := by
    intro k hk
    by_contra hk'
    simp only [Option.not_isSome_iff_eq_none] at hk'
    exact hne (iter_none_of_le next hk hk')
  let f : Fin (Fintype.card V + 1) → V := fun k => (iter next k s).get (hall k (by omega))
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have ha : iter next a s = some (f a) := by simp [f]
  have hb : iter next b s = some (f b) := by simp [f]
  rw [heq] at ha
  exact hab (Fin.ext (iter_injective next hinj hs ha hb))

/-- **Canonical chain**: in-degree ≤ 1, a start without predecessor and reachability give an
exact enumeration of `V` along `next`, ending in `none`. -/
theorem canonical_chain (next : V → Option V) (hinj : Injective next) {s : V}
    (hs : ∀ x, next x ≠ some s) (hreach : ∀ x, ∃ k, iter next k s = some x) :
    (∀ k < Fintype.card V, (iter next k s).isSome) ∧ iter next (Fintype.card V) s = none ∧
      ∀ x, ∃! k, k < Fintype.card V ∧ iter next k s = some x := by
  have hend := iter_card_eq_none next hinj hs
  -- every reachable index is below |V|
  have hlt : ∀ x k, iter next k s = some x → k < Fintype.card V := by
    intro x k hk
    by_contra hge
    rw [iter_none_of_le next (not_lt.mp hge) hend] at hk
    cases hk
  -- the reached indices are exactly 0, …, |V|-1
  have hfirst : ∀ k < Fintype.card V, (iter next k s).isSome := by
    intro k hk
    by_contra hnone
    simp only [Option.not_isSome_iff_eq_none] at hnone
    -- then only indices < k are reached, an injection V → Fin k
    have hbound : ∀ x, ∃ i, i < k ∧ iter next i s = some x := by
      intro x
      obtain ⟨i, hi⟩ := hreach x
      refine ⟨i, ?_, hi⟩
      by_contra hge
      rw [iter_none_of_le next (not_lt.mp hge) hnone] at hi
      cases hi
    choose g hg using hbound
    have ginj : Function.Injective fun x => (⟨g x, (hg x).1⟩ : Fin k) := by
      intro x y hxy
      simp only [Fin.mk.injEq] at hxy
      have hx := (hg x).2
      have hy := (hg y).2
      rw [hxy, hy] at hx
      exact (Option.some.inj hx).symm
    have := Fintype.card_le_of_injective _ ginj
    simp at this
    omega
  refine ⟨hfirst, hend, fun x => ?_⟩
  obtain ⟨k, hk⟩ := hreach x
  exact ⟨k, ⟨hlt x k hk, hk⟩, fun j hj => iter_injective next hinj hs hj.2 hk⟩

omit [Fintype V] in
/-- The start is unique: any node without predecessor is `s`. -/
theorem start_unique (next : V → Option V) {s : V}
    (hreach : ∀ x, ∃ k, iter next k s = some x) (t : V) (ht : ∀ x, next x ≠ some t) :
    t = s := by
  obtain ⟨k, hk⟩ := hreach t
  rcases k with _ | k
  · exact (Option.some.inj hk).symm
  · rw [iter] at hk
    cases hm : iter next k s with
    | none => rw [hm] at hk; cases hk
    | some u => rw [hm] at hk; exact absurd hk (ht u)

/-- The end is unique: exactly one node has no successor, the last one of the chain. -/
theorem end_unique (next : V → Option V) (hinj : Injective next) {s : V}
    (hs : ∀ x, next x ≠ some s) (hreach : ∀ x, ∃ k, iter next k s = some x)
    (e₁ e₂ : V) (h₁ : next e₁ = none) (h₂ : next e₂ = none) : e₁ = e₂ := by
  obtain ⟨-, -, huniq⟩ := canonical_chain next hinj hs hreach
  obtain ⟨i, hi⟩ := hreach e₁
  obtain ⟨j, hj⟩ := hreach e₂
  -- the chain ends right after each of them
  have hi' : iter next (i + 1) s = none := by rw [iter, hi]; exact h₁
  have hj' : iter next (j + 1) s = none := by rw [iter, hj]; exact h₂
  have hcard := iter_card_eq_none next hinj hs
  obtain ⟨hfirst, -, -⟩ := canonical_chain next hinj hs hreach
  -- `i + 1 = |V| = j + 1`
  have key : ∀ m, iter next m s ≠ none → iter next (m + 1) s = none → m + 1 = Fintype.card V := by
    intro m hm hm1
    rcases lt_trichotomy (m + 1) (Fintype.card V) with h | h | h
    · have := hfirst (m + 1) h
      rw [hm1] at this
      cases this
    · exact h
    · exfalso
      exact hm (iter_none_of_le next (by omega) hcard)
  have ei := key i (by rw [hi]; simp) hi'
  have ej := key j (by rw [hj]; simp) hj'
  have : i = j := by omega
  subst this
  rw [hi] at hj
  exact Option.some.inj hj

/-! ## Converse: an enumerated path satisfies the assumptions -/

/-- The successor of an injective enumeration `w : Fin n → V`. -/
noncomputable def pathNext {n : ℕ} (w : Fin n ≃ V) (x : V) : Option V :=
  if h : (w.symm x).val + 1 < n then some (w ⟨(w.symm x).val + 1, h⟩) else none

omit [Fintype V] in
theorem path_satisfies {n : ℕ} (w : Fin (n + 1) ≃ V) :
    Injective (pathNext w) ∧ (∀ x, pathNext w x ≠ some (w 0)) ∧
      ∀ x, ∃ k, iter (pathNext w) k (w 0) = some x := by
  have step : ∀ (i : ℕ) (h : i < n + 1), iter (pathNext w) i (w 0) = some (w ⟨i, h⟩) := by
    intro i
    induction i with
    | zero => intro h; rfl
    | succ i ih =>
      intro h
      rw [iter, ih (by omega)]
      simp [pathNext, h]
  refine ⟨?_, ?_, ?_⟩
  · intro x y z hx hy
    unfold pathNext at hx hy
    split_ifs at hx hy with h1 h2
    have := w.injective (Option.some.inj (hx.trans hy.symm))
    simp only [Fin.mk.injEq, Nat.add_right_cancel_iff] at this
    exact w.symm.injective (Fin.ext this)
  · intro x hx
    unfold pathNext at hx
    split_ifs at hx with h
    have := congrArg Fin.val (w.injective (Option.some.inj hx))
    simp at this
  · intro x
    exact ⟨(w.symm x).val, by rw [step _ (w.symm x).isLt]; simp⟩

end ErgCanonicalChain

#print axioms ErgCanonicalChain.canonical_chain
#print axioms ErgCanonicalChain.no_cycle
#print axioms ErgCanonicalChain.end_unique
#print axioms ErgCanonicalChain.path_satisfies
