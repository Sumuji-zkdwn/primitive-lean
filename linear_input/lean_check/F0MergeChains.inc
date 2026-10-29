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

end LinearInputF0Merge
