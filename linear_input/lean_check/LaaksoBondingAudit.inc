
/-!
Independent additive audit of PR #142, pinned to
983fa7cffe88463e63fdacdcff1d6f989118a76e.
No source definitions are replaced. `realizeRaw` connects raw vertices to
the repository's actual geometric quotient; `bonding` is the actual tower map.
-/

namespace PR142BondingAudit

open LinearInputLaaksoFiniteGraph LinearInputLaaksoRealization
open LinearInputLaaksoGeometricProjection LinearInputLaaksoGeometricTower
open VoidLaaksoBridge

abbrev RawAt (n : ℕ) := RawVertex (VertexType n) (EdgeType n)

noncomputable def realizeRaw (n : ℕ) (x : RawAt n) : Space (n + 1) :=
  vertexPoint (level (n + 1)) (rawProjection x)

/-- A parent observed vertex becomes an OLD raw vertex at the next stage.
The old raw sheet may already have been forgotten by rawProjection. -/
def oldCopy (n : ℕ) (x : RawAt n) (b : Bool) : RawAt (n + 1) :=
  (.inl (rawProjection x), b)

theorem bonding_oldCopy (n : ℕ) (x : RawAt n) (b : Bool) :
    bonding (n + 1) (realizeRaw (n + 1) (oldCopy n x b)) = realizeRaw n x :=
  bond_vertexPoint_old (level (n + 1)) (rawProjection x) b

/-- New vertices project to parent edge interiors, not parent vertex labels. -/
theorem bonding_newRaw (n : ℕ) (e : EdgeType n) (k : Fin 2) (b : Bool) :
    bonding n (realizeRaw n (.inr (e, k), b)) =
      edgePoint (level n) e (newParam k) :=
  bond_vertexPoint_new (level n) e k

theorem oldCopy_fixed (n : ℕ) (x : RawAt n) (b : Bool) :
    advanceRightGeneral (level (n + 1)) (oldCopy n x b) = oldCopy n x b := rfl

theorem bonding_updated_oldCopy (n : ℕ) (x : RawAt n) (b : Bool) :
    bonding (n + 1)
      (realizeRaw (n + 1) (advanceRightGeneral (level (n + 1)) (oldCopy n x b))) =
      realizeRaw n x := bonding_oldCopy n x b

/-- This is a geometric inequality for the ACTUAL bonding map, at every finite
level where an edge is chosen. It asserts no update on geometric interiors. -/
theorem inherited_w1_noncommutes (n : ℕ) (e : EdgeType n) (b c : Bool) :
    bonding (n + 1)
      (realizeRaw (n + 1)
        (advanceRightGeneral (level (n + 1)) (oldCopy n (rawW1 e b) c))) ≠
      realizeRaw n (advanceRightGeneral (level n) (rawW1 e b)) := by
  rw [bonding_updated_oldCopy]
  intro h
  have hv := vertexPoint_injective (level (n + 1)) h
  change (Sum.inr (e, (0 : Fin 2)) : RefinedVertex (VertexType n) (EdgeType n)) =
    Sum.inr (e, 1) at hv
  have hk : (0 : Fin 2) = 1 := congrArg Prod.snd (Sum.inr.inj hv)
  exact (by decide : (0 : Fin 2) ≠ 1) hk

theorem first_second_noncommutes (b c : Bool) :
    bonding 1
      (realizeRaw 1 (advanceRightGeneral (level 1) (oldCopy 0 (w1 b) c))) ≠
      realizeRaw 0 (advanceRightGeneral (level 0) (w1 b)) :=
  inherited_w1_noncommutes 0 (0 : Fin 1) b c

theorem first_general_eq_selected : advanceRightGeneral base = advanceRight := by
  funext x
  fin_cases x <;> rfl

theorem first_labels (b : Bool) :
    firstVertexEncode (rawProjection (w1 b)) = 4 ∧
    firstVertexEncode (rawProjection (advanceRightGeneral base (w1 b))) = 5 := by
  cases b <;> decide

/-- On the old-copy subspace, the two ordered routes have labels 4 and 5. -/
theorem old_copy_labels (b c : Bool) :
    advanceRightGeneral (level 1) (oldCopy 0 (w1 b) c) = oldCopy 0 (w1 b) c ∧
    firstVertexEncode (rawProjection (w1 b)) ≠
      firstVertexEncode (rawProjection (advanceRightGeneral base (w1 b))) := by
  constructor
  · rfl
  · cases b <;> decide

/-- Vertex-supported relation on geometric points. At nonvertex inputs its
value is empty; no total geometric dynamics is being defined. -/
noncomputable def vertexStep (n : ℕ) : Space (n + 1) → Set (Space (n + 1)) :=
  relStep (realizeRaw n) (advanceRightGeneral (level n))

theorem old_read_fiber {V E : Type} (v : V) (b : Bool) (x : RawVertex V E)
    (h : rawProjection x = rawProjection (E := E) (.inl v, b)) :
    x = (.inl v, b) := by
  rcases x with ⟨a, c⟩
  cases a with
  | inl w =>
      have hp : (w, c) = (v, b) := Sum.inl.inj h
      cases hp
      rfl
  | inr w => simp [rawProjection] at h

theorem w1_read_fiber (x : Raw1) (b : Bool) :
    rawProjection x = rawProjection (w1 b) ↔ ∃ c, x = w1 c := by
  fin_cases x <;> cases b <;> decide

theorem first_w1_outputs (b : Bool) :
    vertexStep 0 (realizeRaw 0 (w1 b)) = {realizeRaw 0 (w2 b)} := by
  ext y
  constructor
  · rintro ⟨x, hx, hout⟩
    have hr : rawProjection x = rawProjection (w1 b) :=
      vertexPoint_injective (level 1) hx
    rcases (w1_read_fiber x b).mp hr with ⟨c, rfl⟩
    change y = realizeRaw 0 (w2 b)
    exact hout.symm.trans rfl
  · intro hy
    change y = realizeRaw 0 (w2 b) at hy
    subst y
    exact ⟨w1 b, rfl, rfl⟩

theorem second_old_outputs (v : VertexType 1) (b : Bool) :
    vertexStep 1 (realizeRaw 1 (.inl v, b)) = {realizeRaw 1 (.inl v, b)} := by
  ext y
  constructor
  · rintro ⟨x, hx, hout⟩
    have hr : rawProjection x = rawProjection (E := EdgeType 1) (.inl v, b) :=
      vertexPoint_injective (level 2) hx
    have he := old_read_fiber v b x hr
    subst x
    exact hout.symm
  · intro hy
    change y = realizeRaw 1 (.inl v, b) at hy
    subst y
    exact ⟨(.inl v, b), rfl, rfl⟩

theorem projected_second_w1_outputs (b c : Bool) :
    bonding 1 '' vertexStep 1 (realizeRaw 1 (oldCopy 0 (w1 b) c)) =
      {realizeRaw 0 (w1 b)} := by
  rw [show oldCopy 0 (w1 b) c = (.inl (rawProjection (w1 b)), c) from rfl]
  rw [second_old_outputs (rawProjection (w1 b)) c, Set.image_singleton]
  exact congrArg (fun x => ({x} : Set (Space 1))) (bonding_oldCopy 0 (w1 b) c)

theorem w1_ne_w2 (b : Bool) : realizeRaw 0 (w1 b) ≠ realizeRaw 0 (w2 b) := by
  intro h
  have hv := vertexPoint_injective (level 1) h
  change (Sum.inr ((0 : Fin 1), (0 : Fin 2)) : Obs1) = Sum.inr (0, 1) at hv
  have hk : (0 : Fin 2) = 1 := congrArg Prod.snd (Sum.inr.inj hv)
  exact (by decide : (0 : Fin 2) ≠ 1) hk

/-- Even FORWARD relational soundness fails, not merely exact equality. -/
theorem canonical_relations_not_forward_sound (b c : Bool) :
    ¬ bonding 1 '' vertexStep 1 (realizeRaw 1 (oldCopy 0 (w1 b) c)) ⊆
      vertexStep 0 (bonding 1 (realizeRaw 1 (oldCopy 0 (w1 b) c))) := by
  rw [projected_second_w1_outputs b c, bonding_oldCopy 0 (w1 b) c, first_w1_outputs b]
  intro h
  exact w1_ne_w2 b (h (by rfl))

/-- Keeping the old fixed-point transition and merely adding alternatives
cannot repair forward soundness relative to the unchanged lower relation. -/
theorem cannot_keep_old_stop (F : Space 2 → Set (Space 2)) (b c : Bool)
    (hkeep : realizeRaw 1 (oldCopy 0 (w1 b) c) ∈
      F (realizeRaw 1 (oldCopy 0 (w1 b) c))) :
    ¬ bonding 1 '' F (realizeRaw 1 (oldCopy 0 (w1 b) c)) ⊆
      vertexStep 0 (bonding 1 (realizeRaw 1 (oldCopy 0 (w1 b) c))) := by
  intro h
  have hm := h ⟨_, hkeep, rfl⟩
  rw [bonding_oldCopy 0 (w1 b) c, first_w1_outputs b] at hm
  exact w1_ne_w2 b hm

/-- A replacement relation, constrained by its projected successor. -/
def pullbackStep {X Y : Type*} (p : X → Y) (R : Y → Set Y) (x : X) : Set X :=
  {y | p y ∈ R (p x)}

/-- Exact one-step relational compatibility is recovered under surjectivity.
This changes the fine relation; it does not validate the original update. -/
theorem pullbackStep_exact {X Y : Type*} (p : X → Y)
    (hp : Function.Surjective p) (R : Y → Set Y) (x : X) :
    p '' pullbackStep p R x = R (p x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    rcases hp y with ⟨z, rfl⟩
    exact ⟨z, hy, rfl⟩

/-- Complete finite repair on all 12 inherited observed vertex copies. -/
theorem inherited_relation_repair (x : Obs1 × Bool) :
    Prod.fst '' pullbackStep Prod.fst (relStep firstRead advanceRight) x =
      relStep firstRead advanceRight x.1 := by
  exact pullbackStep_exact Prod.fst (fun y => ⟨(y, false), rfl⟩)
    (relStep firstRead advanceRight) x

/-- One-step set equality for the actual bonding map. The chosen R may be
partial; this asserts neither continuity nor an infinite compatible dynamics. -/
theorem bonding_relation_repair (R : Space 1 → Set (Space 1)) (x : Space 2) :
    bonding 1 '' pullbackStep (bonding 1) R x = R (bonding 1 x) :=
  pullbackStep_exact (bonding 1) (bonding_surjective 1) R x

end PR142BondingAudit

#print axioms PR142BondingAudit.inherited_w1_noncommutes
#print axioms PR142BondingAudit.first_second_noncommutes
#print axioms PR142BondingAudit.first_labels
#print axioms PR142BondingAudit.first_w1_outputs
#print axioms PR142BondingAudit.projected_second_w1_outputs
#print axioms PR142BondingAudit.canonical_relations_not_forward_sound
#print axioms PR142BondingAudit.cannot_keep_old_stop
#print axioms PR142BondingAudit.inherited_relation_repair
#print axioms PR142BondingAudit.bonding_relation_repair
