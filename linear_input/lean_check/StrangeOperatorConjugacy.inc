/-!
Conjugacy and exact one-point forgetting closures.

This is an additive extension of StrangeOperatorGalois.inc and F0Retractions.inc.
The relation Stops is the explicit chosen operational semantics. No physical
identification of a strange quark phase is asserted.
-/

namespace LinearInputStrangeConjugacy

open LinearInputStrangeGalois

universe u v

/-- Relabel the input/output states of an endomorphism by a bijection. -/
def Conjugate {α : Type u} (e : α ≃ α) (S : α → α) : α → α :=
  fun x => e (S (e.symm x))

/-- Conjugation acts invertibly on the space of all state operations. -/
def conjugateEquiv {α : Type u} (e : α ≃ α) :
    (α → α) ≃ (α → α) where
  toFun := Conjugate e
  invFun := Conjugate e.symm
  left_inv S := by
    funext x
    simp [Conjugate]
  right_inv S := by
    funext x
    simp [Conjugate]

/-- The Stops relation is invariant under simultaneous state relabeling. -/
theorem stops_conjugate_iff {α : Type u}
    (e : α ≃ α) (T S : α → α) :
    Stops (Conjugate e T) (Conjugate e S) ↔ Stops T S := by
  constructor
  · rintro ⟨x, hx, hfixed⟩
    refine ⟨e.symm x, ?_, ?_⟩
    · intro hs
      apply hx
      simp [Conjugate, hs]
    · have h := congrArg e.symm hfixed
      simpa [Conjugate] using h
  · rintro ⟨x, hx, hfixed⟩
    refine ⟨e x, ?_, ?_⟩
    · intro h
      apply hx
      have h' := congrArg e.symm h
      simpa [Conjugate] using h'
    · simpa [Conjugate] using congrArg e hfixed

/-- Antitone left polar commutes with any equivariant pair of bijections. -/
theorem left_polar_image {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (f : ι ≃ ι) (g : κ ≃ κ)
    (hR : ∀ t s, R (f t) (g s) ↔ R t s) (A : Set κ) :
    LeftPolar R (g '' A) = f '' LeftPolar R A := by
  apply Set.ext
  intro t
  constructor
  · intro ht
    refine ⟨f.symm t, ?_, f.apply_symm_apply t⟩
    intro s hs
    have hs' : g s ∈ g '' A := ⟨s, hs, rfl⟩
    have hts : R t (g s) := ht (g s) hs'
    exact (hR (f.symm t) s).mp (by simpa using hts)
  · rintro ⟨t0, ht0, rfl⟩
    intro s hs
    obtain ⟨s0, hs0, rfl⟩ := hs
    exact (hR t0 s0).mpr (ht0 s0 hs0)

/-- Antitone right polar commutes with the same pair of bijections. -/
theorem right_polar_image {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (f : ι ≃ ι) (g : κ ≃ κ)
    (hR : ∀ t s, R (f t) (g s) ↔ R t s) (B : Set ι) :
    RightPolar R (f '' B) = g '' RightPolar R B := by
  apply Set.ext
  intro s
  constructor
  · intro hs
    refine ⟨g.symm s, ?_, g.apply_symm_apply s⟩
    intro t ht
    have ht' : f t ∈ f '' B := ⟨t, ht, rfl⟩
    have hts : R (f t) s := hs (f t) ht'
    exact (hR t (g.symm s)).mp (by simpa using hts)
  · rintro ⟨s0, hs0, rfl⟩
    intro t ht
    obtain ⟨t0, ht0, rfl⟩ := ht
    exact (hR t0 s0).mpr (hs0 t0 ht0)

/-- General naturality of the double-polar Galois closure. -/
theorem close_image {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (f : ι ≃ ι) (g : κ ≃ κ)
    (hR : ∀ t s, R (f t) (g s) ↔ R t s) (A : Set κ) :
    Close R (g '' A) = g '' Close R A := by
  change RightPolar R (LeftPolar R (g '' A)) =
    g '' RightPolar R (LeftPolar R A)
  rw [left_polar_image R f g hR A,
      right_polar_image R f g hR (LeftPolar R A)]

/-- Conjugation is a symmetry of the F0-derived strange closure itself. -/
theorem close_conjugate {α : Type u}
    (e : α ≃ α) (A : Set (α → α)) :
    Close (Stops (α := α)) (conjugateEquiv e '' A) =
      conjugateEquiv e '' Close (Stops (α := α)) A := by
  apply close_image (Stops (α := α)) (conjugateEquiv e)
    (conjugateEquiv e) ?_ A
  intro T S
  exact stops_conjugate_iff e T S

/-- One-point forgetting: move c to a, fixing every other state. -/
noncomputable def Spike {α : Type u} (c a : α) : α → α := by
  classical
  exact fun x => if x = c then a else x

theorem spike_changes_iff {α : Type u} {c a : α} (ha : a ≠ c) (x : α) :
    Spike c a x ≠ x ↔ x = c := by
  classical
  by_cases hx : x = c
  · subst x
    simp [Spike, ha]
  · simp [Spike, hx]

/-- The entire left polar of a spike depends only on the forgotten input c. -/
theorem stops_spike_iff {α : Type u} {c a : α} (ha : a ≠ c)
    (T : α → α) : Stops T (Spike c a) ↔ T c ≠ c := by
  constructor
  · rintro ⟨x, hx, hfixed⟩
    have hxc : x = c := (spike_changes_iff ha x).mp hx
    subst x
    intro htc
    have he : T c = c := by simpa using htc
    have hbad : a = c := by
      simpa [Spike, he] using hfixed
    exact ha hbad
  · intro htc
    refine ⟨c, (spike_changes_iff ha c).mpr rfl, ?_⟩
    classical
    simp [Spike, htc]

/--
Exactly classifies the closure of an arbitrary one-point F0 retraction.
No cardinality or finiteness assumption is needed.
-/
theorem close_spike_singleton {α : Type u} (c a : α) (ha : a ≠ c) :
    Close (Stops (α := α)) ({Spike c a} : Set (α → α)) =
      {S | ∃ b : α, b ≠ c ∧ S = Spike c b} := by
  classical
  apply Set.ext
  intro S
  constructor
  · intro hS
    have htest : ∀ T : α → α, T c ≠ c →
        T ∈ LeftPolar (Stops (α := α)) ({Spike c a} : Set (α → α)) := by
      intro T htc s hs
      have hs' : s = Spike c a := Set.mem_singleton_iff.mp hs
      subst s
      exact (stops_spike_iff ha T).mpr htc
    have hfix : ∀ b : α, b ≠ c → S b = b := by
      intro b hb
      obtain ⟨x, hx, hSb⟩ := hS (fun _ : α => b) (htest (fun _ => b) hb)
      exact hSb
    have hc : S c ≠ c := by
      intro hscc
      obtain ⟨x, hx, _⟩ := hS (Spike c a)
        (htest (Spike c a) (by simpa [Spike] using ha))
      apply hx
      by_cases hxc : x = c
      · simpa [hxc] using hscc
      · exact hfix x hxc
    refine ⟨S c, hc, ?_⟩
    funext x
    by_cases hxc : x = c
    · subst x
      simp [Spike]
    · simpa [Spike, hxc] using hfix x hxc
  · rintro ⟨b, hb, rfl⟩
    intro T ht
    have htc : T c ≠ c := by
      apply (stops_spike_iff ha T).mp
      exact ht (Spike c a) rfl
    exact (stops_spike_iff hb T).mpr htc

/-- Conjugating a spike simply relabels its source and destination. -/
theorem conjugate_spike {α : Type u}
    (e : α ≃ α) (c a : α) :
    Conjugate e (Spike c a) = Spike (e c) (e a) := by
  classical
  funext x
  by_cases hx : x = e c
  · subst x
    simp [Conjugate, Spike]
  · have hx' : e.symm x ≠ c := by
      intro h
      apply hx
      calc
        x = e (e.symm x) := (e.apply_symm_apply x).symm
        _ = e c := congrArg e h
    simp [Conjugate, Spike, hx, hx']

/--
The closed spike family is exactly the conjugacy orbit under permutations
fixing the forgotten input c. In particular, every target is reachable via
one transposition a <-> b, even when the state type is infinite.
-/
theorem close_spike_is_conjugacy_orbit {α : Type u}
    (c a : α) (ha : a ≠ c) :
    Close (Stops (α := α)) ({Spike c a} : Set (α → α)) =
      {S | ∃ e : α ≃ α, e c = c ∧ S = Conjugate e (Spike c a)} := by
  classical
  rw [close_spike_singleton c a ha]
  apply Set.ext
  intro S
  constructor
  · rintro ⟨b, hb, rfl⟩
    let e : α ≃ α := Equiv.swap a b
    have hec : e c = c :=
      Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm
    have hea : e a = b := Equiv.swap_apply_left a b
    refine ⟨e, hec, ?_⟩
    rw [conjugate_spike, hec, hea]
  · rintro ⟨e, hec, hS⟩
    refine ⟨e a, ?_, ?_⟩
    · intro h
      apply ha
      apply e.injective
      exact h.trans hec.symm
    · rw [hS, conjugate_spike, hec]

/-- The concrete primitive-lean Fin-3 forgetting map is a one-point spike. -/
theorem exampleK_is_spike :
    LinearInputF0.exampleK = Spike (1 : Fin 3) 0 := by
  funext x
  fin_cases x <;> norm_num [LinearInputF0.exampleK, Spike, Fin.ext_iff]

/-- The previous two-element numerical closure becomes an exact Lean theorem. -/
theorem exampleK_closed_pair :
    Close (Stops (α := Fin 3))
      ({LinearInputF0.exampleK} : Set (Fin 3 → Fin 3)) =
      {LinearInputF0.exampleK, Spike (1 : Fin 3) 2} := by
  rw [exampleK_is_spike, close_spike_singleton (1 : Fin 3) (0 : Fin 3) (by decide)]
  apply Set.ext
  intro S
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, hb, hs⟩
    fin_cases b
    · exact Or.inl hs
    · exact False.elim (hb rfl)
    · exact Or.inr hs
  · rintro (h | h)
    · exact ⟨0, by decide, h⟩
    · exact ⟨2, by decide, h⟩

/-- The two actual F0-related operators are related by swapping labels 0,2. -/
theorem exampleK_pair_conjugate :
    Conjugate (Equiv.swap (0 : Fin 3) 2) LinearInputF0.exampleK =
      Spike (1 : Fin 3) 2 := by
  rw [exampleK_is_spike, conjugate_spike]
  simp [Equiv.swap_apply_def]

end LinearInputStrangeConjugacy
