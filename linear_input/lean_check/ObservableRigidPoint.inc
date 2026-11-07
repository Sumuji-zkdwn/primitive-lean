/-!
# Observable rigid point from F0 retractions

A "rigid point" here means a common fixed observable representative of
two projected phase-update operations. It does NOT mean an infinitely stiff
physical solid, an equilibrium of a continuum model, or a critical point.

The commuting hypothesis is essential for the general construction.
A four-state example distinguishes microscopic order dependence from
order independence after a specified observation. This does not establish
equivalence under arbitrary future contexts.
-/

noncomputable section

namespace LinearInputRigidPoint

open LinearInputF0

/-- Project a microscopic update through a retained F0 observation. -/
def projected {α : Type*} (K F : α → α) : α → α :=
  fun x => K (F x)

/-- Two commuting idempotent updates have a common fixed state.
No order, metric, stiffness, or physical phase label is assumed. -/
theorem common_fixed_of_commuting {α : Type*} (M C : α → α)
    (hM : Idempotent M) (hC : Idempotent C)
    (hcomm : ∀ x, M (C x) = C (M x)) (x : α) :
    ∃ q : α, M q = q ∧ C q = q := by
  refine ⟨M (C x), ?_, ?_⟩
  · exact hM (C x)
  · calc
      C (M (C x)) = M (C (C x)) := (hcomm (C x)).symm
      _ = M (C x) := congrArg M (hC x)

/-- A point fixed by both projected updates exists whenever these
projected updates are idempotent and commute. The underlying updates
M and C need not commute or be idempotent. -/
theorem observed_rigid_exists {α : Type*} (K M C : α → α)
    (hK : Idempotent K)
    (hM : Idempotent (projected K M))
    (hC : Idempotent (projected K C))
    (hcomm : ∀ x, projected K M (projected K C x) =
        projected K C (projected K M x))
    (x : α) :
    ∃ q : α, K q = q ∧
      projected K M q = q ∧ projected K C q = q := by
  let U := projected K M
  let V := projected K C
  refine ⟨U (V x), ?_, ?_, ?_⟩
  · change K (K (M (V x))) = K (M (V x))
    exact hK (M (V x))
  · exact hM (V x)
  · calc
      V (U (V x)) = U (V (V x)) := (hcomm (V x)).symm
      _ = U (V x) := congrArg U (hC x)

/-- Reuse the existing F0 fixed/range theorem:
the observable common fixed point is a K-representative. -/
theorem observed_rigid_in_Krange {α : Type*} (K M C : α → α)
    (hK : Idempotent K)
    (hM : Idempotent (projected K M))
    (hC : Idempotent (projected K C))
    (hcomm : ∀ x, projected K M (projected K C x) =
        projected K C (projected K M x))
    (x : α) :
    ∃ q : α, q ∈ Set.range K ∧
      projected K M q = q ∧ projected K C q = q := by
  obtain ⟨q, hk, hm, hc⟩ :=
    observed_rigid_exists K M C hK hM hC hcomm x
  exact ⟨q, (fixed_iff_in_range hK q).mp hk, hm, hc⟩

/-- Two idempotents need not share any fixed point. -/
def incompatibleM (_ : Bool) : Bool := false
def incompatibleC (_ : Bool) : Bool := true

theorem no_common_without_commutation :
    Idempotent incompatibleM ∧ Idempotent incompatibleC ∧
      ¬ ∃ q : Bool, incompatibleM q = q ∧ incompatibleC q = q := by
  constructor
  · intro q
    rfl
  constructor
  · intro q
    rfl
  · rintro ⟨q, hm, hc⟩
    cases q <;> simp [incompatibleM, incompatibleC] at hm hc

/-- A four-state model: first bit is visible, second bit is hidden. -/
def exK (x : Bool × Bool) : Bool × Bool := (x.1, false)
def exM (x : Bool × Bool) : Bool × Bool := (false, x.2)
def exC (x : Bool × Bool) : Bool × Bool := (x.1, x.1)

theorem example_K_idempotent : Idempotent exK := by
  rintro ⟨a, b⟩
  cases a <;> cases b <;> decide

theorem example_raw_idempotents : Idempotent exM ∧ Idempotent exC := by
  constructor
  · rintro ⟨a, b⟩
    cases a <;> cases b <;> decide
  · rintro ⟨a, b⟩
    cases a <;> cases b <;> decide

/-- The microscopic operations do not commute but their current readouts agree. -/
theorem example_hidden_order_difference :
    exM (exC (true, false)) ≠ exC (exM (true, false)) ∧
      exK (exM (exC (true, false))) =
        exK (exC (exM (true, false))) := by
  decide

theorem example_projected_idempotents :
    Idempotent (projected exK exM) ∧
      Idempotent (projected exK exC) := by
  constructor
  · rintro ⟨a, b⟩
    cases a <;> cases b <;> decide
  · rintro ⟨a, b⟩
    cases a <;> cases b <;> decide

theorem example_projected_commute :
    ∀ x, projected exK exM (projected exK exC x) =
      projected exK exC (projected exK exM x) := by
  rintro ⟨a, b⟩
  cases a <;> cases b <;> decide

/-- The new fixed-point theorem is instantiated in a hidden-history model. -/
theorem example_observed_rigid :
    ∃ q : Bool × Bool, exK q = q ∧
      projected exK exM q = q ∧ projected exK exC q = q := by
  exact observed_rigid_exists exK exM exC
    example_K_idempotent
    example_projected_idempotents.1
    example_projected_idempotents.2
    example_projected_commute (true, false)

end LinearInputRigidPoint
