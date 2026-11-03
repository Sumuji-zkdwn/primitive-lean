/-!
# Decomposition rewrite, normal-form identification, and finite probe cost

An evaluation can be preserved by every rewrite while distinct terminal
decompositions have identical evaluation. Termination, unique normal forms,
and the ability to identify terminal forms are logically distinct.

Only explicit hypotheses are used for termination or normal-form
identifiability. A concrete branching rewrite exhibits the obstruction.
A commutative generator multiset exhibits 4*9 = 6*6; its generator words
are distinct even though evaluation uses just one commutative product.
-/

namespace LinearInputDecompositionIdentification

/-- A zero-or-more-step rewrite derivation. -/
inductive Steps {α : Type*} (R : α → α → Prop) : α → α → Prop where
  | refl (x : α) : Steps R x x
  | cons {x y z : α} : R x y → Steps R y z → Steps R x z

/-- A terminal expression has no legal outgoing rewrite. -/
def Terminal {α : Type*} (R : α → α → Prop) (x : α) : Prop :=
  ∀ y, ¬ R x y

theorem steps_trans {α : Type*} {R : α → α → Prop}
    {x y z : α} (hxy : Steps R x y) (hyz : Steps R y z) :
    Steps R x z := by
  induction hxy with
  | refl _ => exact hyz
  | cons h _ ih => exact Steps.cons h ih

/-- Rewrite-invariance extends from one step to every finite derivation. -/
theorem steps_preserve {α β : Type*} (R : α → α → Prop)
    (f : α → β) (hstep : ∀ x y, R x y → f x = f y)
    {x y : α} (hxy : Steps R x y) : f x = f y := by
  induction hxy with
  | refl _ => rfl
  | cons h _ ih => exact (hstep _ _ h).trans ih

/-- A terminal input admits no nontrivial rewrite path. -/
theorem terminal_path_eq {α : Type*} {R : α → α → Prop}
    {x y : α} (hterm : Terminal R x) (hxy : Steps R x y) :
    x = y := by
  cases hxy with
  | refl _ => rfl
  | cons h _ => exact False.elim (hterm _ h)

/-- A natural-number rank decreasing on all one-step rewrites ensures that
every starting object reaches some terminal object. -/
theorem terminating_normal_form {α : Type*} (R : α → α → Prop)
    (rank : α → ℕ)
    (hdec : ∀ {x y}, R x y → rank y < rank x)
    (x : α) : ∃ n, Steps R x n ∧ Terminal R n := by
  classical
  have aux : ∀ k : ℕ, ∀ a : α, rank a = k →
      ∃ n, Steps R a n ∧ Terminal R n := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro a ha
        by_cases hterm : Terminal R a
        · exact ⟨a, Steps.refl a, hterm⟩
        · have hnext : ∃ b : α, R a b := by
            by_contra hno
            apply hterm
            intro b hab
            exact hno ⟨b, hab⟩
          obtain ⟨b, hab⟩ := hnext
          have hb : rank b < k := by
            rw [← ha]
            exact hdec hab
          obtain ⟨n, hbn, htn⟩ := ih (rank b) hb b rfl
          exact ⟨n, Steps.cons hab hbn, htn⟩
  exact aux (rank x) x rfl

/-- Evaluation separates all terminal normal forms, not necessarily all
intermediate expressions. -/
def TerminalValueInjective {α β : Type*}
    (R : α → α → Prop) (value : α → β) : Prop :=
  ∀ u v, Terminal R u → Terminal R v → value u = value v → u = v

/-- Two normal forms reached from one input agree when terminal evaluation
is injective and evaluation is invariant along the rewrite path. -/
theorem normal_forms_unique_of_value {α β : Type*}
    (R : α → α → Prop) (value : α → β)
    (hstep : ∀ x y, R x y → value x = value y)
    (hval : TerminalValueInjective R value)
    {x u v : α} (hu : Steps R x u) (hv : Steps R x v)
    (htu : Terminal R u) (htv : Terminal R v) : u = v := by
  apply hval u v htu htv
  exact (steps_preserve R value hstep hu).symm.trans
    (steps_preserve R value hstep hv)

/-- Uniqueness of normal forms from common ancestors need not imply that
evaluation is injective on unrelated terminal objects. A common-ancestor
hypothesis makes the converse valid. -/
theorem terminal_value_injective_of_common_ancestor {α β : Type*}
    (R : α → α → Prop) (value : α → β)
    (hcommon : ∀ u v, Terminal R u → Terminal R v →
      value u = value v → ∃ x, Steps R x u ∧ Steps R x v)
    (hunique : ∀ x u v, Steps R x u → Steps R x v →
      Terminal R u → Terminal R v → u = v) :
    TerminalValueInjective R value := by
  intro u v hu hv he
  obtain ⟨x, hxu, hxv⟩ := hcommon u v hu hv he
  exact hunique x u v hxu hxv hu hv

/-- Extra observation can remove residual ambiguities among terminal
representatives without changing the evaluation or the rewrite relation. -/
def IdentifiesTerminals {α β γ : Type*}
    (R : α → α → Prop) (value : α → β) (probe : α → γ) : Prop :=
  ∀ u v, Terminal R u → Terminal R v →
    value u = value v → probe u = probe v → u = v

theorem joint_identifies_terminals_iff {α β γ : Type*}
    (R : α → α → Prop) (value : α → β) (probe : α → γ) :
    IdentifiesTerminals R value probe ↔
      TerminalValueInjective R
        (LinearInputFiniteObservation.joint value probe) := by
  constructor
  · intro h u v hu hv he
    have hh := (LinearInputFiniteObservation.joint_eq_iff value probe u v).1 he
    exact h u v hu hv hh.1 hh.2
  · intro h u v hu hv he hp
    exact h u v hu hv
      ((LinearInputFiniteObservation.joint_eq_iff value probe u v).2 ⟨he, hp⟩)

/-- If each probe is stable under rewriting, identical initial joint
observations determine the same terminal result whenever terminal joint
observations are injective. -/
theorem same_final_of_invariant_probe {α β γ : Type*}
    (R : α → α → Prop) (value : α → β) (probe : α → γ)
    (hvalue : ∀ x y, R x y → value x = value y)
    (hprobe : ∀ x y, R x y → probe x = probe y)
    (hidentify : IdentifiesTerminals R value probe)
    {x y u v : α} (hxu : Steps R x u) (hyv : Steps R y v)
    (hu : Terminal R u) (hv : Terminal R v)
    (he : value x = value y) (hp : probe x = probe y) :
    u = v := by
  apply hidentify u v hu hv
  · exact (steps_preserve R value hvalue hxu).symm.trans
      (he.trans (steps_preserve R value hvalue hyv))
  · exact (steps_preserve R probe hprobe hxu).symm.trans
      (hp.trans (steps_preserve R probe hprobe hyv))

/-- A permitted finite family of additional probes separates every pair
of terminal forms with the same evaluation. -/
def IdentifiesWith {α β γ ι : Type*} [DecidableEq ι]
    (R : α → α → Prop) (value : α → β)
    (probe : ι → α → γ) (chosen : Finset ι) : Prop :=
  ∀ u v, Terminal R u → Terminal R v → value u = value v →
    (∀ i ∈ chosen, probe i u = probe i v) → u = v

theorem identifies_with_mono {α β γ ι : Type*} [DecidableEq ι]
    (R : α → α → Prop) (value : α → β) (probe : ι → α → γ)
    {s t : Finset ι} (hst : s ⊆ t)
    (hs : IdentifiesWith R value probe s) :
    IdentifiesWith R value probe t := by
  intro u v hu hv he ht
  exact hs u v hu hv he (by
    intro i hi
    exact ht i (hst hi))

theorem zero_extra_probes_iff {α β γ ι : Type*} [DecidableEq ι]
    (R : α → α → Prop) (value : α → β) (probe : ι → α → γ) :
    IdentifiesWith R value probe ∅ ↔ TerminalValueInjective R value := by
  constructor
  · intro h u v hu hv he
    exact h u v hu hv he (by simp)
  · intro h u v hu hv he _
    exact h u v hu hv he

/-- Identifying probes are exactly a hitting set for all pairs of distinct
terminal forms which collide under the old evaluation. This is the explicit
finite-probe optimization constraint; no efficiency bound is assumed. -/
theorem identifies_with_iff_hits_collisions {α β γ ι : Type*}
    [DecidableEq ι] (R : α → α → Prop) (value : α → β)
    (probe : ι → α → γ) (chosen : Finset ι) :
    IdentifiesWith R value probe chosen ↔
      ∀ u v, Terminal R u → Terminal R v →
        value u = value v → u ≠ v →
          ∃ i ∈ chosen, probe i u ≠ probe i v := by
  classical
  constructor
  · intro h u v hu hv he hne
    by_contra hn
    have hall : ∀ i ∈ chosen, probe i u = probe i v := by
      intro i hi
      by_contra hd
      exact hn ⟨i, hi, hd⟩
    exact hne (h u v hu hv he hall)
  · intro h u v hu hv he hall
    by_contra hne
    obtain ⟨i, hi, hd⟩ := h u v hu hv he hne
    exact hd (hall i hi)

/-- Explicit nonconfluent branching example with a fixed final value. -/
def branchStep (x y : Fin 3) : Prop :=
  x = 0 ∧ (y = 1 ∨ y = 2)

def branchRank (x : Fin 3) : ℕ :=
  if x = 0 then 1 else 0

def branchValue (_ : Fin 3) : ℕ := 36

def branchProbe (x : Fin 3) : Bool := decide (x = 2)

theorem branch_step_preserves (x y : Fin 3) (h : branchStep x y) :
    branchValue x = branchValue y := rfl

theorem branch_rank_decreases {x y : Fin 3} (h : branchStep x y) :
    branchRank y < branchRank x := by
  rcases h with ⟨rfl, rfl | rfl⟩ <;> decide

theorem branch_terminates (x : Fin 3) :
    ∃ n, Steps branchStep x n ∧ Terminal branchStep n :=
  terminating_normal_form branchStep branchRank (fun h => branch_rank_decreases h) x

theorem branch_terminal_one : Terminal branchStep 1 := by
  intro y h
  exact (by decide : (1 : Fin 3) ≠ 0) h.1

theorem branch_terminal_two : Terminal branchStep 2 := by
  intro y h
  exact (by decide : (2 : Fin 3) ≠ 0) h.1

theorem branch_root_reaches_one : Steps branchStep 0 1 :=
  Steps.cons ⟨rfl, Or.inl rfl⟩ (Steps.refl 1)

theorem branch_root_reaches_two : Steps branchStep 0 2 :=
  Steps.cons ⟨rfl, Or.inr rfl⟩ (Steps.refl 2)

theorem branch_nonconfluent :
    ¬ ∀ x u v, Steps branchStep x u → Steps branchStep x v →
      Terminal branchStep u → Terminal branchStep v → u = v := by
  intro h
  have hh := h 0 1 2 branch_root_reaches_one branch_root_reaches_two
    branch_terminal_one branch_terminal_two
  exact (by decide : (1 : Fin 3) ≠ 2) hh

theorem branch_value_not_identifying :
    ¬ TerminalValueInjective branchStep branchValue := by
  intro h
  have hh := h 1 2 branch_terminal_one branch_terminal_two rfl
  exact (by decide : (1 : Fin 3) ≠ 2) hh

/-- One Bool probe separates the terminal branches, but does not turn
this branching rewrite into a confluent rewrite system. -/
theorem branch_probe_identifies :
    IdentifiesTerminals branchStep branchValue branchProbe := by
  intro u v hu hv he hp
  have hu0 : u ≠ 0 := by
    intro h0
    subst u
    exact (hu 1 ⟨rfl, Or.inl rfl⟩).elim
  have hv0 : v ≠ 0 := by
    intro h0
    subst v
    exact (hv 1 ⟨rfl, Or.inl rfl⟩).elim
  fin_cases u <;> fin_cases v <;> simp_all [branchProbe]

/-- The permitted library contains exactly one extra observation. -/
def allowedProbe (_ : Fin 1) : Fin 3 → Bool := branchProbe

theorem zero_probes_insufficient :
    ¬ IdentifiesWith branchStep branchValue allowedProbe ∅ := by
  intro h
  have hval : TerminalValueInjective branchStep branchValue :=
    (zero_extra_probes_iff branchStep branchValue allowedProbe).1 h
  exact branch_value_not_identifying hval

theorem one_probe_suffices :
    IdentifiesWith branchStep branchValue allowedProbe ({0} : Finset (Fin 1)) := by
  intro u v hu hv he hp
  apply branch_probe_identifies u v hu hv he
  exact hp 0 (by simp)

/-- Under the fixed one-element probe library, exactly one additional
measurement is necessary and sufficient to identify terminal branches. -/
theorem one_probe_is_minimal :
    IdentifiesWith branchStep branchValue allowedProbe ({0} : Finset (Fin 1)) ∧
      ∀ s : Finset (Fin 1),
        IdentifiesWith branchStep branchValue allowedProbe s →
          1 ≤ s.card := by
  constructor
  · exact one_probe_suffices
  · intro s hs
    by_contra hlt
    have hz : s.card = 0 := by omega
    have hempty : s = ∅ := Finset.card_eq_zero.mp hz
    subst s
    exact zero_probes_insufficient hs

/-- One commutative multiplication, two distinct generator multisets. -/
def generatorValue (i : Fin 3) : ℕ :=
  if i = 0 then 4 else if i = 1 then 6 else 9

def evaluateFactors (m : Multiset (Fin 3)) : ℕ :=
  (m.map generatorValue).prod

def factorsFourNine : Multiset (Fin 3) :=
  (0 : Fin 3) ::ₘ 2 ::ₘ 0

def factorsSixSix : Multiset (Fin 3) :=
  (1 : Fin 3) ::ₘ 1 ::ₘ 0

def countFour (m : Multiset (Fin 3)) : ℕ := m.count 0

theorem generator_collision :
    evaluateFactors factorsFourNine = 36 ∧
    evaluateFactors factorsSixSix = 36 ∧
    factorsFourNine ≠ factorsSixSix ∧
    countFour factorsFourNine ≠ countFour factorsSixSix := by
  decide

end LinearInputDecompositionIdentification
