import Mathlib.Tactic

/-!
# Actual finite gate constraints are closed and nested

For each bit label k let W_k be a FINITE set of allowed heights. A pair
(l,u) of sweep endpoints is admissible at stage m when it contains the
original endpoints and one W_k gate for each differing bit k<m.

These theorems prepare the hypotheses of LaaksoNestedGateCompactness.
They do not claim the finite graph shortest path equals the infimum over
this family: that path-normalization statement is a separate obligation.
-/

namespace LaaksoGateConstraint

open Set

/-- A closed interval [l,u] has a witness in the specified gate set. -/
def Hit (W : Set ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ w : ℝ, w ∈ W ∧ p.1 ≤ w ∧ w ≤ p.2

def HitSet (W : Set ℝ) : Set (ℝ × ℝ) :=
  {p | Hit W p}

/-- Gate hit by a finite set is a closed condition on interval endpoints. -/
theorem isClosed_hitSet (W : Set ℝ) (hW : W.Finite) :
    IsClosed (HitSet W) := by
  have hfixed (w : ℝ) :
      IsClosed {p : ℝ × ℝ | p.1 ≤ w ∧ w ≤ p.2} := by
    have hleft : IsClosed {p : ℝ × ℝ | p.1 ≤ w} :=
      isClosed_Iic.preimage continuous_fst
    have hright : IsClosed {p : ℝ × ℝ | w ≤ p.2} :=
      isClosed_Ici.preimage continuous_snd
    simpa only [setOf_and] using hleft.inter hright
  have hrewrite :
      HitSet W = ⋃ w ∈ W, {p : ℝ × ℝ | p.1 ≤ w ∧ w ≤ p.2} := by
    ext p
    simp only [HitSet, Hit, mem_setOf_eq, mem_iUnion] <;> aesop
  rw [hrewrite]
  exact hW.isClosed_biUnion (fun w hw => hfixed w)

/-- The endpoints must enclose s,t and remain within [0,1]. -/
def Endpoints (s t : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
    p.1 ≤ s ∧ p.1 ≤ t ∧ s ≤ p.2 ∧ t ≤ p.2}

theorem isClosed_endpoints (s t : ℝ) : IsClosed (Endpoints s t) := by
  have hK : IsClosed (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    isClosed_Icc.prod isClosed_Icc
  have h₁ : IsClosed {p : ℝ × ℝ | p.1 ≤ s} :=
    isClosed_Iic.preimage continuous_fst
  have h₂ : IsClosed {p : ℝ × ℝ | p.1 ≤ t} :=
    isClosed_Iic.preimage continuous_fst
  have h₃ : IsClosed {p : ℝ × ℝ | s ≤ p.2} :=
    isClosed_Ici.preimage continuous_snd
  have h₄ : IsClosed {p : ℝ × ℝ | t ≤ p.2} :=
    isClosed_Ici.preimage continuous_snd
  simpa only [Endpoints, setOf_and] using
    (hK.inter (h₁.inter (h₂.inter (h₃.inter h₄))))

def Required (G : ℕ → Set ℝ) (a b : ℕ → Bool) (k : ℕ) :
    Set (ℝ × ℝ) :=
  if a k = b k then Set.univ else HitSet (G k)

theorem isClosed_required (G : ℕ → Set ℝ) (hfinite : ∀ k, (G k).Finite)
    (a b : ℕ → Bool) (k : ℕ) :
    IsClosed (Required G a b k) := by
  by_cases h : a k = b k
  · simp [Required, h]
  · simpa [Required, h] using isClosed_hitSet (G k) (hfinite k)

/-- All constraints up to (but not including) stage m. -/
def Prefix (G : ℕ → Set ℝ) (a b : ℕ → Bool)
    (s t : ℝ) (m : ℕ) : Set (ℝ × ℝ) :=
  Endpoints s t ∩
    ⋂ k : ℕ, if k < m then Required G a b k else Set.univ

theorem prefix_isClosed (G : ℕ → Set ℝ) (hfinite : ∀ k, (G k).Finite)
    (a b : ℕ → Bool) (s t : ℝ) (m : ℕ) :
    IsClosed (Prefix G a b s t m) := by
  apply (isClosed_endpoints s t).inter
  apply isClosed_iInter
  intro k
  by_cases h : k < m
  · simpa [h] using isClosed_required G hfinite a b k
  · simp [h]

theorem prefix_decreasing (G : ℕ → Set ℝ) (a b : ℕ → Bool)
    (s t : ℝ) (m : ℕ) :
    Prefix G a b s t (m + 1) ⊆ Prefix G a b s t m := by
  rintro p ⟨hp, hreq⟩
  refine ⟨hp, Set.mem_iInter.mpr ?_⟩
  intro k
  by_cases hk : k < m
  · have hks : k < m + 1 := Nat.lt_succ_of_lt hk
    have h := (Set.mem_iInter.mp hreq) k
    simpa [hk, hks] using h
  · simp [hk]

/-- Every finite-prefix gate constraint is a compact subset of the
unit square in (lower,upper) interval coordinates. -/
theorem prefix_isCompact (G : ℕ → Set ℝ) (hfinite : ∀ k, (G k).Finite)
    (a b : ℕ → Bool) (s t : ℝ) (m : ℕ) :
    IsCompact (Prefix G a b s t m) := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  apply hK.of_isClosed_subset (prefix_isClosed G hfinite a b s t m)
  intro p hp
  exact hp.1.1

#print axioms prefix_isCompact

#print axioms isClosed_hitSet
#print axioms prefix_isClosed
#print axioms prefix_decreasing

end LaaksoGateConstraint
