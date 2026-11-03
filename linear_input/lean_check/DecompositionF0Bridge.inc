/-!
Bridge between general terminating rewrite theory and the retained F0 positive
integer-partition merge chain. The existing Merge and Chain declarations are
reused unchanged. Positive parts and a nonempty starting multiset are required
for the singleton normal form result; no uniqueness is asserted for arbitrary
zero-containing multisets.
-/

namespace LinearInputDecompositionF0Bridge

open LinearInputDecompositionIdentification

/-- Existing F0 merge is an evaluation-preserving one-step rewrite. -/
theorem merge_preserves_sum {p q : Multiset ℕ}
    (h : LinearInputF0Merge.Merge p q) : p.sum = q.sum :=
  LinearInputF0Merge.merge_sum h

/-- The number of parts decreases strictly on every genuine merge. -/
theorem merge_decreases_card {p q : Multiset ℕ}
    (h : LinearInputF0Merge.Merge p q) : q.card < p.card := by
  have hc := LinearInputF0Merge.merge_card h
  omega

/-- Every multiset has at least one terminal form under finite F0 merges. -/
theorem merge_normal_form_exists (p : Multiset ℕ) :
    ∃ q, Steps LinearInputF0Merge.Merge p q ∧
      Terminal LinearInputF0Merge.Merge q :=
  terminating_normal_form LinearInputF0Merge.Merge Multiset.card
    (fun h => merge_decreases_card h) p

/-- The existing exact-length F0 merge chains instantiate generic paths. -/
theorem chain_is_path {n : ℕ} {p q : Multiset ℕ}
    (h : LinearInputF0Merge.Chain n p q) :
    Steps LinearInputF0Merge.Merge p q := by
  induction n generalizing p with
  | zero =>
      change p = q at h
      subst q
      exact Steps.refl p
  | succ n ih =>
      obtain ⟨r, hpr, hrq⟩ := h
      exact Steps.cons hpr (ih hrq)

/-- Positive nonempty partitions reach the singleton `{sum}`. -/
theorem positive_reaches_singleton {p : Multiset ℕ}
    (hne : p ≠ 0) (hp : ∀ a ∈ p, 0 < a) :
    Steps LinearInputF0Merge.Merge p {p.sum} :=
  chain_is_path (LinearInputF0Merge.reaches_singleton hne hp)

/-- The one-part configuration is a terminal form. -/
theorem singleton_terminal (n : ℕ) :
    Terminal LinearInputF0Merge.Merge ({n} : Multiset ℕ) := by
  intro q h
  have hc := LinearInputF0Merge.merge_card h
  simp only [Multiset.card_singleton] at hc
  omega

/-- Every F0 merge outputs at least one part. -/
theorem merge_output_nonempty {p q : Multiset ℕ}
    (h : LinearInputF0Merge.Merge p q) : q ≠ 0 := by
  obtain ⟨a, b, rest, _, _, _, hq⟩ := h
  rw [hq]
  simp

theorem path_preserves_nonempty {p q : Multiset ℕ}
    (h : Steps LinearInputF0Merge.Merge p q) :
    p ≠ 0 → q ≠ 0 := by
  induction h with
  | refl _ => intro hp; exact hp
  | cons hab _ ih =>
      intro _
      exact ih (merge_output_nonempty hab)

theorem path_preserves_positive {p q : Multiset ℕ}
    (h : Steps LinearInputF0Merge.Merge p q) :
    (∀ a ∈ p, 0 < a) → ∀ a ∈ q, 0 < a := by
  induction h with
  | refl _ => intro hp; exact hp
  | cons hab _ ih =>
      intro hp
      exact ih (LinearInputF0Merge.merge_preserves_positive hab hp)

/-- The only terminal form of a positive, nonempty partition is its
singleton sum, independently of the order in which merges were applied. -/
theorem positive_terminal_is_singleton {p : Multiset ℕ}
    (hne : p ≠ 0) (hp : ∀ a ∈ p, 0 < a)
    (ht : Terminal LinearInputF0Merge.Merge p) :
    p = {p.sum} := by
  exact terminal_path_eq ht (positive_reaches_singleton hne hp)

/-- A general endpoint from a positive, nonempty starting partition is
forced to be the same singleton: this is explicit normal-form uniqueness. -/
theorem positive_unique_normal_form {p q : Multiset ℕ}
    (hne : p ≠ 0) (hp : ∀ a ∈ p, 0 < a)
    (hpath : Steps LinearInputF0Merge.Merge p q)
    (ht : Terminal LinearInputF0Merge.Merge q) :
    q = {p.sum} := by
  have hneQ := path_preserves_nonempty hpath hne
  have hpQ := path_preserves_positive hpath hp
  have heval : p.sum = q.sum :=
    steps_preserve LinearInputF0Merge.Merge (fun m : Multiset ℕ => m.sum)
      (fun _ _ h => merge_preserves_sum h) hpath
  calc
    q = {q.sum} := positive_terminal_is_singleton hneQ hpQ ht
    _ = {p.sum} := congrArg (fun n : ℕ => ({n} : Multiset ℕ)) heval.symm

/-- Two positive nonempty terminal forms are distinguished by their
evaluation alone; no additional observation is required in this subdomain. -/
theorem positive_terminal_value_identifies {p q : Multiset ℕ}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : ∀ a ∈ p, 0 < a) (hq : ∀ a ∈ q, 0 < a)
    (htp : Terminal LinearInputF0Merge.Merge p)
    (htq : Terminal LinearInputF0Merge.Merge q)
    (heval : p.sum = q.sum) : p = q := by
  calc
    p = {p.sum} := positive_terminal_is_singleton hp0 hp htp
    _ = {q.sum} := congrArg (fun n : ℕ => ({n} : Multiset ℕ)) heval
    _ = q := (positive_terminal_is_singleton hq0 hq htq).symm

end LinearInputDecompositionF0Bridge
