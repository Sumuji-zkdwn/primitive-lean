/-!
# Finite-capacity incompatibility produces local extinction

PR #66 assumed that every local operation's domain is unavailable at a
terminal time. Here a concrete, finitely bounded demand model DERIVES that
domain loss from the simultaneous load of global requirements.

A local system can implement an action exactly when it satisfies EVERY
current requirement. If each local can support at most c of the available
requirements but the global demand contains all N > c requirements, all
local domains are empty. If the old system genuinely moved, PR #65/66
then shows that historical preservation fails.

Sharp countermodels:
* every pair among 3 requirements is covered by some local system, but
  the triple is not covered; pairwise local compatibility is insufficient;
* finite noncommuting operations can remain available forever with no
  historical loss, so neither finiteness nor noncommutativity alone forces
  extinction.
This is a conditional capacity theorem, not an unconditional account of
all expanding logical spaces or all partial operations.
-/

section

namespace LinearInputCapacityExtinction

open LinearInputFiniteSelfSynthesis
open LinearInputHistoryNonpreservation
open LinearInputTemporalExtinction

/-- A local operation is valid precisely when it supports all demands. -/
def Covers {Λ Req : Type*}
    (support : Λ → Req → Bool) (demand : List Req) (loc : Λ) : Prop :=
  ∀ req, req ∈ demand → support loc req = true

def allSupported {Λ Req : Type*}
    (support : Λ → Req → Bool) (demand : List Req) (loc : Λ) : Bool :=
  demand.all (fun req => support loc req)

/-- Boolean conjunction is true exactly when both inputs are true. -/
theorem bool_and_true_iff (a b : Bool) :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem allSupported_iff_covers {Λ Req : Type*}
    (support : Λ → Req → Bool) (demand : List Req) (loc : Λ) :
    allSupported support demand loc = true ↔ Covers support demand loc := by
  induction demand with
  | nil =>
      constructor
      · intro _ req h
        cases h
      · intro _
        rfl
  | cons req rest ih =>
      change (support loc req && rest.all (fun r => support loc r)) = true ↔
        Covers support (req :: rest) loc
      constructor
      · intro h r hr
        have hhead : support loc req = true := ((bool_and_true_iff (support loc req) (allSupported support rest loc)).mp h).1
        have htail : allSupported support rest loc = true :=
          ((bool_and_true_iff (support loc req) (allSupported support rest loc)).mp h).2
        rcases List.mem_cons.mp hr with heq | hmem
        · subst r
          exact hhead
        · exact (ih.mp htail) r hmem
      · intro h
        have hhead : support loc req = true := h req (by simp)
        have htail : allSupported support rest loc = true :=
          ih.mpr (by
            intro r hr
            exact h r (List.mem_cons_of_mem req hr))
        exact (bool_and_true_iff (support loc req) (allSupported support rest loc)).mpr ⟨hhead, htail⟩

/-- Adding demands can never make a previously incapable local capable. -/
theorem coverage_antitone {Λ Req : Type*}
    (support : Λ → Req → Bool)
    (older later : List Req) (loc : Λ)
    (hsub : ∀ r, r ∈ older → r ∈ later)
    (hnew : Covers support later loc) :
    Covers support older loc := by
  intro r hr
  exact hnew r (hsub r hr)

theorem noncoverage_persists_under_demand_growth {Λ Req : Type*}
    (support : Λ → Req → Bool)
    (older later : List Req) (loc : Λ)
    (hsub : ∀ r, r ∈ older → r ∈ later)
    (hfail : ¬ Covers support older loc) :
    ¬ Covers support later loc := by
  intro hnew
  exact hfail (coverage_antitone support older later loc hsub hnew)

/-- If a complete demand exceeds every local's finite capability count,
no local covers all current requirements. -/
theorem bounded_capacity_blocks_global_cover
    {Λ Req : Type*} [Fintype Req] [DecidableEq Req]
    (locals : List Λ) (support : Λ → Req → Bool)
    (demand : List Req) (capacity : ℕ)
    (hcap : ∀ loc, loc ∈ locals →
      (Finset.univ.filter (fun r : Req => support loc r = true)).card ≤
        capacity)
    (hexceed : capacity < Fintype.card Req)
    (hfull : ∀ r : Req, r ∈ demand) :
    ¬ ∃ loc, loc ∈ locals ∧ Covers support demand loc := by
  rintro ⟨loc, hloc, hcover⟩
  have hfullSupport :
      (Finset.univ.filter (fun r : Req => support loc r = true)) =
        Finset.univ := by
    ext r
    simp [hcover r (hfull r)]
  have hbound : Fintype.card Req ≤ capacity := by
    simpa [hfullSupport] using hcap loc hloc
  omega

theorem bounded_capacity_disables_each_local
    {Λ Req : Type*} [Fintype Req] [DecidableEq Req]
    (locals : List Λ) (support : Λ → Req → Bool)
    (demand : List Req) (capacity : ℕ)
    (hcap : ∀ loc, loc ∈ locals →
      (Finset.univ.filter (fun r : Req => support loc r = true)).card ≤
        capacity)
    (hexceed : capacity < Fintype.card Req)
    (hfull : ∀ r : Req, r ∈ demand) :
    ∀ loc, loc ∈ locals → allSupported support demand loc = false := by
  have hno : ¬ ∃ loc, loc ∈ locals ∧ Covers support demand loc :=
    bounded_capacity_blocks_global_cover locals support demand
      capacity hcap hexceed hfull
  intro loc hloc
  cases hc : allSupported support demand loc with
  | false => rfl
  | true =>
      have hcover : Covers support demand loc :=
        (allSupported_iff_covers support demand loc).mp hc
      exact False.elim (hno ⟨loc, hloc, hcover⟩)

/-- The global demand determines the actual domains of local operations.
The underlying local action functions are time-independent. -/
def capacityTimeline {S Ω Λ Req : Type*}
    (locals : List Λ) (support : Λ → Req → Bool)
    (demands : ℕ → List Req)
    (action : Λ → S → S) (readout : ℕ → S → Ω) :
    LocalTimeline S Ω Λ :=
  ⟨locals, (fun t loc _ => allSupported support (demands t) loc),
    action, readout⟩

theorem capacity_overload_forces_total_extinction
    {S Ω Λ Req : Type*} [Fintype Req] [DecidableEq Req]
    (locals : List Λ) (support : Λ → Req → Bool)
    (demands : ℕ → List Req)
    (action : Λ → S → S) (readout : ℕ → S → Ω)
    (time : ℕ) (capacity : ℕ)
    (hcap : ∀ loc, loc ∈ locals →
      (Finset.univ.filter (fun r : Req => support loc r = true)).card ≤
        capacity)
    (hexceed : capacity < Fintype.card Req)
    (hfull : ∀ r : Req, r ∈ demands time) :
    AllExtinct
      (capacityTimeline locals support demands action readout) time := by
  intro x loc hloc
  change allSupported support (demands time) loc = false
  exact bounded_capacity_disables_each_local locals support (demands time)
    capacity hcap hexceed hfull loc hloc

/-- Bridge to PR #66: the prior moving history is lost because overload
causes local extinction, rather than assuming extinction at the outset. -/
theorem capacity_overload_forces_history_loss
    {S Ω Λ Req : Type*} [Fintype Req] [DecidableEq Req]
    (locals : List Λ) (support : Λ → Req → Bool)
    (demands : ℕ → List Req)
    (action : Λ → S → S) (readout : ℕ → S → Ω)
    (before after : ℕ) (capacity : ℕ) (x : S)
    (hcap : ∀ loc, loc ∈ locals →
      (Finset.univ.filter (fun r : Req => support loc r = true)).card ≤
        capacity)
    (hexceed : capacity < Fintype.card Req)
    (hfull : ∀ r : Req, r ∈ demands after)
    (hmoving : stepAt
      (capacityTimeline locals support demands action readout) before x ≠ x) :
    ¬ Preserves
      (historyAt (capacityTimeline locals support demands action readout)
        before)
      (historyAt (capacityTimeline locals support demands action readout)
        after) := by
  exact extinction_forces_nonpreservation
    (capacityTimeline locals support demands action readout)
    before after x hmoving
    (capacity_overload_forces_total_extinction locals support
      demands action readout after capacity hcap hexceed hfull)

/-- Three local systems, each missing exactly one of three demands. -/
def supportsOthers (loc req : Fin 3) : Bool := decide (loc ≠ req)

theorem supportsOthers_pairwise_cover (r s : Fin 3) :
    ∃ loc : Fin 3,
      supportsOthers loc r = true ∧ supportsOthers loc s = true := by
  fin_cases r <;> fin_cases s <;> decide

theorem supportsOthers_exact_capacity (loc : Fin 3) :
    (Finset.univ.filter
      (fun req : Fin 3 => supportsOthers loc req = true)).card = 2 := by
  fin_cases loc <;> decide

theorem supportsOthers_no_global_cover :
    ¬ ∃ loc : Fin 3, loc ∈ ([0, 1, 2] : List (Fin 3)) ∧
      Covers supportsOthers [0, 1, 2] loc := by
  apply bounded_capacity_blocks_global_cover
    ([0, 1, 2] : List (Fin 3)) supportsOthers [0, 1, 2] 2
  · intro loc _
    simp [supportsOthers_exact_capacity loc]
  · decide
  · intro r
    fin_cases r <;> decide

/-- At t=0 only the first two demands are active. From t=1 on,
all three are required simultaneously. -/
def increasingDemands (t : ℕ) : List (Fin 3) :=
  if t = 0 then [0, 1] else [0, 1, 2]

def overloadedTimeline : LocalTimeline (Fin 2) Unit (Fin 3) :=
  capacityTimeline [0, 1, 2] supportsOthers increasingDemands
    (fun _ => LinearInputTemporalExtinction.flip)
    (fun _ _ => ())

theorem overload_initially_operates (x : Fin 2) :
    stepAt overloadedTimeline 0 x =
      LinearInputTemporalExtinction.flip x := by
  rfl

theorem overload_old_history_moves :
    stepAt overloadedTimeline 0 (0 : Fin 2) ≠ 0 := by
  decide

theorem overload_later_every_local_extinct (t : ℕ) (ht : 1 ≤ t) :
    AllExtinct overloadedTimeline t := by
  have hn : t ≠ 0 := by omega
  have hcap : ∀ loc : Fin 3,
      loc ∈ ([0, 1, 2] : List (Fin 3)) →
      (Finset.univ.filter
        (fun req : Fin 3 => supportsOthers loc req = true)).card ≤ 2 := by
    intro loc _
    simp [supportsOthers_exact_capacity loc]
  have hfull : ∀ r : Fin 3, r ∈ increasingDemands t := by
    intro r
    have hr : r ∈ ([0, 1, 2] : List (Fin 3)) := by
      fin_cases r <;> decide
    simpa [increasingDemands, hn] using hr
  exact capacity_overload_forces_total_extinction
    ([0, 1, 2] : List (Fin 3)) supportsOthers increasingDemands
    (fun _ => LinearInputTemporalExtinction.flip)
    (fun _ _ => ()) t 2 hcap (by decide) hfull

theorem overload_causes_nonpreservation (t : ℕ) (ht : 1 ≤ t) :
    ¬ Preserves (historyAt overloadedTimeline 0)
      (historyAt overloadedTimeline t) := by
  exact extinction_forces_nonpreservation overloadedTimeline 0 t 0
    overload_old_history_moves (overload_later_every_local_extinct t ht)

theorem overload_causes_interval_failure (stop : ℕ) (hs : 1 ≤ stop) :
    ¬ PreservedOn overloadedTimeline 0 stop := by
  exact interval_with_extinct_endpoint_is_not_preserved
    overloadedTimeline 0 stop 1 (by omega) hs 0
    overload_old_history_moves (overload_later_every_local_extinct 1 (by omega))

/-- Despite nonpreservation, snapshots are preserved: the lost object is
the nontrivial operation history, not the current observable label. -/
theorem overloaded_snapshots_survive (t : ℕ) :
    SnapshotPreserves (historyAt overloadedTimeline 0)
      (historyAt overloadedTimeline t) := by
  refine ⟨fun x => x, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl

/-- Finiteness and noncommutativity by themselves force no extinction.
Two finite, noncommuting local actions can stay available forever. -/
def swap01 (x : Fin 3) : Fin 3 :=
  if x = 0 then 1 else if x = 1 then 0 else 2

def swap12 (x : Fin 3) : Fin 3 :=
  if x = 1 then 2 else if x = 2 then 1 else 0

theorem finite_actions_do_not_commute :
    swap01 (swap12 0) ≠ swap12 (swap01 0) := by
  decide

def permanentTimeline : LocalTimeline (Fin 3) Unit (Fin 2) :=
  ⟨[0, 1], (fun _ _ _ => true),
    (fun loc => if loc = 0 then swap01 else swap12), (fun _ _ => ())⟩

theorem permanent_has_available_local (t : ℕ) (x : Fin 3) :
    ∃ loc : Fin 2, loc ∈ permanentTimeline.locals ∧
      permanentTimeline.available t loc x = true := by
  exact ⟨0, by decide, rfl⟩

theorem permanent_history_is_preserved :
    Preserves (historyAt permanentTimeline 0)
      (historyAt permanentTimeline 1) := by
  refine ⟨fun x => x, ?_, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl
  · intro x
    rfl

end LinearInputCapacityExtinction
