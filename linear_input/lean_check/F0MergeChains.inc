/-! Integer-partition types as multisets, and exact-length binary-merge chains. -/

noncomputable section

namespace LinearInputF0Merge

def Merge (p q : Multiset ℕ) : Prop :=
  ∃ a b : ℕ, ∃ rest : Multiset ℕ,
    0 < a ∧ 0 < b ∧ p = a ::ₘ b ::ₘ rest ∧ q = (a + b) ::ₘ rest

def Chain : ℕ → Multiset ℕ → Multiset ℕ → Prop
  | 0, p, q => p = q
  | n + 1, p, q => ∃ r, Merge p r ∧ Chain n r q

theorem merge_sum {p q : Multiset ℕ} (h : Merge p q) : p.sum = q.sum := by
  obtain ⟨a, b, rest, _, _, rfl, rfl⟩ := h
  simp [add_assoc]

theorem merge_card {p q : Multiset ℕ} (h : Merge p q) : q.card + 1 = p.card := by
  obtain ⟨a, b, rest, _, _, rfl, rfl⟩ := h
  simp

theorem merge_preserves_positive {p q : Multiset ℕ} (h : Merge p q)
    (hp : ∀ a ∈ p, 0 < a) : ∀ a ∈ q, 0 < a := by
  obtain ⟨a, b, rest, ha, hb, rfl, rfl⟩ := h
  intro x hx
  simp only [Multiset.mem_cons] at hx
  rcases hx with rfl | hx
  · omega
  · exact hp x (by simp [hx])

theorem chain_card {n : ℕ} {p q : Multiset ℕ} (h : Chain n p q) :
    q.card + n = p.card := by
  induction n generalizing p with
  | zero => simp only [Chain] at h; subst q; omega
  | succ n ih =>
    obtain ⟨r, hpr, hrq⟩ := h
    have := merge_card hpr
    have := ih hrq
    omega

theorem chain_sum {n : ℕ} {p q : Multiset ℕ} (h : Chain n p q) : p.sum = q.sum := by
  induction n generalizing p with
  | zero => exact congrArg Multiset.sum h
  | succ n ih =>
    obtain ⟨r, hpr, hrq⟩ := h
    exact (merge_sum hpr).trans (ih hrq)

theorem no_nonempty_cycle {n : ℕ} (hn : 0 < n) (p : Multiset ℕ) : ¬ Chain n p p := by
  intro h
  have := chain_card h
  omega

theorem merge_head_to_sum (rest : Multiset ℕ) (a : ℕ) (ha : 0 < a)
    (hp : ∀ b ∈ rest, 0 < b) : Chain rest.card (a ::ₘ rest) {a + rest.sum} := by
  induction rest using Multiset.induction_on generalizing a with
  | empty => simp [Chain]
  | @cons b rest ih =>
    have hb := hp b (by simp)
    have hr : ∀ c ∈ rest, 0 < c := fun c hc => hp c (by simp [hc])
    rw [Multiset.card_cons]
    change ∃ r, Merge (a ::ₘ b ::ₘ rest) r ∧ Chain rest.card r {a + (b ::ₘ rest).sum}
    refine ⟨(a + b) ::ₘ rest, ⟨a, b, rest, ha, hb, rfl, rfl⟩, ?_⟩
    simpa [add_assoc] using ih (a + b) (by omega) hr

theorem reaches_singleton {p : Multiset ℕ} (hne : p ≠ 0)
    (hp : ∀ a ∈ p, 0 < a) : Chain (p.card - 1) p {p.sum} := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem ha
  have ha := hp a (by simp)
  have hr : ∀ b ∈ rest, 0 < b := fun b hb => hp b (by simp [hb])
  simpa using merge_head_to_sum rest a ha hr

theorem chain_to_singleton_length {n N : ℕ} {p : Multiset ℕ} (h : Chain n p {N}) :
    n = p.card - 1 := by
  have hc := chain_card h
  simp only [Multiset.card_singleton] at hc
  omega

theorem all_ones_to_singleton {N : ℕ} (hN : 0 < N) :
    Chain (N - 1) (Multiset.replicate N 1) {N} := by
  have hne : Multiset.replicate N 1 ≠ 0 := by
    intro h
    have hc := congrArg Multiset.card h
    simp only [Multiset.card_replicate, Multiset.card_zero] at hc
    omega
  have hp : ∀ a ∈ Multiset.replicate N 1, 0 < a := by
    intro a ha
    have : a = 1 := (Multiset.mem_replicate.mp ha).2
    omega
  simpa using reaches_singleton hne hp

/-!
A concrete five-state realization of the merge chain.  The multiset of
fiber cardinalities records the integer partition represented by each map.
Each elementary map is an idempotent K and is a K-S-C step for the
identity split/reconstruction pair; the K changes from one stage to the next.
-/

def stateMergeAt (j x : Fin 5) : Fin 5 := if x = j then 0 else x

theorem stateMergeAt_idempotent (j : Fin 5) :
    LinearInputF0.Idempotent (stateMergeAt j) := by
  intro x
  by_cases h : x = j <;> simp [stateMergeAt, h]

def stateSplit (x : Fin 5) (_ : Fin 1) : Fin 5 := x

def stateCollect (v : Fin 1 → Fin 5) : Fin 5 := v 0

theorem stateSplit_reconstructs :
    LinearInputF0.Reconstructs stateSplit stateCollect := by
  intro x
  rfl

theorem stateSplit_compatible (K : Fin 5 → Fin 5) :
    LinearInputF0.Compatible K stateSplit := by
  intro x i
  rfl

theorem stateMergeAt_is_KSC (j x : Fin 5) :
    LinearInputF0.step (stateMergeAt j) stateSplit stateCollect x = stateMergeAt j x := by
  exact congrFun
    (LinearInputF0.A_B_collapse (stateMergeAt_idempotent j)
      stateSplit_reconstructs (stateSplit_compatible (stateMergeAt j))) x

def fiveQ0 : Fin 5 → Fin 5 := id

def fiveQ1 : Fin 5 → Fin 5 := stateMergeAt 1

def fiveQ2 (x : Fin 5) : Fin 5 := stateMergeAt 2 (fiveQ1 x)

def fiveQ3 (x : Fin 5) : Fin 5 := stateMergeAt 3 (fiveQ2 x)

def fiveQ4 (x : Fin 5) : Fin 5 := stateMergeAt 4 (fiveQ3 x)

/-- The integer partition represented by the nonempty fibers of a map. -/
def fiberMasses (q : Fin 5 → Fin 5) : Multiset ℕ :=
  (Finset.univ.image q).val.map
    (fun y => (Finset.univ.filter (fun x => q x = y)).card)

theorem fiberMasses_fiveQ0 :
    fiberMasses fiveQ0 = Multiset.replicate 5 1 := by
  classical
  decide

theorem fiberMasses_fiveQ1 :
    fiberMasses fiveQ1 = 2 ::ₘ Multiset.replicate 3 1 := by
  classical
  decide

theorem fiberMasses_fiveQ2 :
    fiberMasses fiveQ2 = 3 ::ₘ Multiset.replicate 2 1 := by
  classical
  decide

theorem fiberMasses_fiveQ3 :
    fiberMasses fiveQ3 = 4 ::ₘ Multiset.replicate 1 1 := by
  classical
  decide

theorem fiberMasses_fiveQ4 :
    fiberMasses fiveQ4 = {5} := by
  classical
  decide

theorem fiveStateMerge01 :
    Merge (fiberMasses fiveQ0) (fiberMasses fiveQ1) := by
  rw [fiberMasses_fiveQ0, fiberMasses_fiveQ1]
  refine ⟨1, 1, Multiset.replicate 3 1, by norm_num, by norm_num, ?_, ?_⟩
  · simp [Multiset.replicate_succ]
  · simp

theorem fiveStateMerge12 :
    Merge (fiberMasses fiveQ1) (fiberMasses fiveQ2) := by
  rw [fiberMasses_fiveQ1, fiberMasses_fiveQ2]
  refine ⟨2, 1, Multiset.replicate 2 1, by norm_num, by norm_num, ?_, ?_⟩
  · simp [Multiset.replicate_succ]
  · simp

theorem fiveStateMerge23 :
    Merge (fiberMasses fiveQ2) (fiberMasses fiveQ3) := by
  rw [fiberMasses_fiveQ2, fiberMasses_fiveQ3]
  refine ⟨3, 1, Multiset.replicate 1 1, by norm_num, by norm_num, ?_, ?_⟩
  · simp [Multiset.replicate_succ]
  · simp

theorem fiveStateMerge34 :
    Merge (fiberMasses fiveQ3) (fiberMasses fiveQ4) := by
  rw [fiberMasses_fiveQ3, fiberMasses_fiveQ4]
  refine ⟨4, 1, 0, by norm_num, by norm_num, ?_, ?_⟩
  · simp [Multiset.replicate_succ]
  · simp

theorem fiveState_merge_chain :
    Chain 4 (fiberMasses fiveQ0) (fiberMasses fiveQ4) := by
  change ∃ r, Merge (fiberMasses fiveQ0) r ∧ Chain 3 r (fiberMasses fiveQ4)
  refine ⟨fiberMasses fiveQ1, fiveStateMerge01, ?_⟩
  change ∃ r, Merge (fiberMasses fiveQ1) r ∧ Chain 2 r (fiberMasses fiveQ4)
  refine ⟨fiberMasses fiveQ2, fiveStateMerge12, ?_⟩
  change ∃ r, Merge (fiberMasses fiveQ2) r ∧ Chain 1 r (fiberMasses fiveQ4)
  refine ⟨fiberMasses fiveQ3, fiveStateMerge23, ?_⟩
  change ∃ r, Merge (fiberMasses fiveQ3) r ∧ Chain 0 r (fiberMasses fiveQ4)
  refine ⟨fiberMasses fiveQ4, fiveStateMerge34, ?_⟩
  rfl

theorem fiveQ4_constant : fiveQ4 = fun _ => (0 : Fin 5) := by
  funext x
  fin_cases x <;> decide

/-- No deterministic post-map can reconstruct the original five-state label. -/
theorem fiveQ4_no_left_inverse (D : Fin 5 → Fin 5) :
    ¬ Function.LeftInverse D fiveQ4 := by
  intro h
  have h0 : D (0 : Fin 5) = 0 := by simpa only [fiveQ4_constant] using h 0
  have h1 : D (0 : Fin 5) = 1 := by simpa only [fiveQ4_constant] using h 1
  have h01 : (0 : Fin 5) = 1 := h0.symm.trans h1
  have hv := congrArg Fin.val h01
  norm_num at hv

end LinearInputF0Merge
