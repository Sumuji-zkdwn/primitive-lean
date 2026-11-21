import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Regeneration in a finite common-pool resource task

An occupied-to-empty edge contributes one unit at its empty end. A harvest
opens one site and removes one source from each empty neighbor. Randomness is
represented by integer tickets, so a sequence of trials has a common exact
denominator. The conditional probability is recomputed at each visited site.
-/

namespace CPRRegeneration

open Finset

/-- An undirected neighborhood without self-loops. The concrete grid below
uses only in-board cells, including at corners and sides. -/
structure Neighborhood (V : Type*) where
  neighbors : V → Finset V
  symmetric (i j : V) : j ∈ neighbors i ↔ i ∈ neighbors j
  loopless (i : V) : i ∉ neighbors i

variable {V : Type*} [DecidableEq V] (G : Neighborhood V)

def occupiedNeighbors (X : Finset V) (i : V) : ℕ := (G.neighbors i ∩ X).card

def sandAt (X : Finset V) (i : V) : ℕ := if i ∈ X then 0 else occupiedNeighbors G X i

def harvest (X : Finset V) (i : V) : Finset V := X.erase i

def born (X : Finset V) (i : V) : Finset V := insert i X

def totalSand [Fintype V] (X : Finset V) : ℕ := ∑ i, sandAt G X i

/-- Each crossing is counted from its occupied end. -/
def boundarySize (X : Finset V) : ℕ := ∑ i ∈ X, (G.neighbors i \ X).card

private theorem sum_membership [Fintype V] (S : Finset V) :
    (∑ i : V, if i ∈ S then 1 else 0) = S.card := by
  simp

/-- Summing the field at empty receivers counts the cut from the other end. -/
theorem totalSand_eq_boundary [Fintype V] (X : Finset V) :
    totalSand G X = boundarySize G X := by
  let edge (v u : V) : ℕ :=
    if v ∉ X ∧ u ∈ G.neighbors v ∧ u ∈ X then 1 else 0
  have incoming (v : V) : sandAt G X v = ∑ u : V, edge v u := by
    by_cases hv : v ∈ X
    · simp [sandAt, edge, hv]
    · simpa [sandAt, occupiedNeighbors, edge, hv] using
        (sum_membership (G.neighbors v ∩ X)).symm
  have outgoing (u : V) :
      (∑ v : V, edge v u) = if u ∈ X then (G.neighbors u \ X).card else 0 := by
    by_cases hu : u ∈ X
    · simp only [hu, ite_true]
      rw [← sum_membership (G.neighbors u \ X)]
      apply Finset.sum_congr rfl
      intro v _
      simp [edge, hu, G.symmetric v u, and_comm]
    · simp [edge, hu]
  unfold totalSand boundarySize
  simp_rw [incoming]
  rw [Finset.sum_comm]
  simp_rw [outgoing]
  simp

theorem neighbors_harvest (X : Finset V) (i j : V) (hi : i ∈ X) :
    occupiedNeighbors G (harvest X i) j + (if i ∈ G.neighbors j then 1 else 0) =
      occupiedNeighbors G X j := by
  unfold occupiedNeighbors harvest
  rw [Finset.inter_erase]
  by_cases h : i ∈ G.neighbors j
  · simpa [h] using Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨h, hi⟩)
  · simp [h]

/-- The gain at the harvested site and the one-unit losses at its empty
neighbors are expressed without truncated subtraction. -/
theorem sandAt_harvest_balance (X : Finset V) (i j : V) (hi : i ∈ X) :
    sandAt G (harvest X i) j + (if j ∈ G.neighbors i \ X then 1 else 0) =
      sandAt G X j + (if j = i then occupiedNeighbors G X i else 0) := by
  have hn := neighbors_harvest G X i j hi
  by_cases hji : j = i
  · subst j
    simpa [sandAt, harvest, hi, G.loopless] using hn
  · by_cases hj : j ∈ X
    · simp [sandAt, harvest, hji, hj]
    · simpa [sandAt, harvest, hji, hj, G.symmetric j i] using hn

/-- In signed form the change in total sand is two occupied neighbors per
neighbor count minus the degree of the harvested site. -/
theorem totalSand_harvest [Fintype V] (X : Finset V) (i : V) (hi : i ∈ X) :
    totalSand G (harvest X i) + (G.neighbors i).card =
      totalSand G X + 2 * occupiedNeighbors G X i := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl
    (fun j _ => sandAt_harvest_balance G X i j hi)
  simp only [Finset.sum_add_distrib, sum_membership] at h
  have delta : (∑ j : V, if j = i then occupiedNeighbors G X i else 0) =
      occupiedNeighbors G X i := by simp
  rw [delta] at h
  have degree := Finset.card_sdiff_add_card_inter (G.neighbors i) X
  unfold totalSand occupiedNeighbors at *
  omega

theorem totalSand_birth [Fintype V] (X : Finset V) (i : V) (hi : i ∉ X) :
    totalSand G (born X i) + 2 * occupiedNeighbors G X i =
      totalSand G X + (G.neighbors i).card := by
  have erase : harvest (born X i) i = X := by simp [harvest, born, hi]
  have mem : i ∈ born X i := by simp [born]
  have localCount := neighbors_harvest G (born X i) i i mem
  simp only [erase, G.loopless, ite_false, Nat.add_zero] at localCount
  simpa only [erase, ← localCount] using (totalSand_harvest G (born X i) i mem).symm

def hitCount (units : V → ℕ) (X : Finset V) (i : V) : ℕ := units i * sandAt G X i

/-- With a uniform ticket in 0,...,D-1 this has probability hitCount / D. -/
def trial (units : V → ℕ) (X : Finset V) (i : V) (ticket : ℕ) : Finset V :=
  if ticket < hitCount G units X i then born X i else X

@[simp] theorem trial_empty (units : V → ℕ) (i : V) (ticket : ℕ) :
    trial G units ∅ i ticket = ∅ := by
  simp [trial, hitCount, sandAt, occupiedNeighbors]

inductive Action (V : Type*) where
  | harvest (i : V)
  | attempt (i : V) (ticket : ℕ)

def applyAction (units : V → ℕ) (X : Finset V) : Action V → Finset V
  | .harvest i => harvest X i
  | .attempt i ticket => trial G units X i ticket

theorem depleted_absorbing (units : V → ℕ) (actions : List (Action V)) :
    actions.foldl (applyAction G units) ∅ = ∅ := by
  induction actions with
  | nil => rfl
  | cons a rest ih => cases a <;> simpa [applyAction, harvest] using ih

abbrev Cell (n : ℕ) := Fin n × Fin n

def moore (n : ℕ) : Neighborhood (Cell n) where
  neighbors i := Finset.univ.filter fun j => j ≠ i ∧
    j.1.val ≤ i.1.val + 1 ∧ i.1.val ≤ j.1.val + 1 ∧
    j.2.val ≤ i.2.val + 1 ∧ i.2.val ≤ j.2.val + 1
  symmetric i j := by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; grind
  loopless i := by simp

/-- Successful and unsuccessful tickets both contribute to continuation
observables; divide by D for a conditional expectation when D is positive. -/
def stepMass (D : ℕ) (units : V → ℕ) (i : V) (f : Finset V → ℕ) (X : Finset V) : ℕ :=
  (D - hitCount G units X i) * f X + hitCount G units X i * f (born X i)

def ValidWeights (D : ℕ) (units : V → ℕ) : Prop :=
  ∀ i, units i * (G.neighbors i).card ≤ D

theorem hitCount_le {D : ℕ} {units : V → ℕ} (hw : ValidWeights G D units)
    (X : Finset V) (i : V) : hitCount G units X i ≤ D := by
  have hc : occupiedNeighbors G X i ≤ (G.neighbors i).card :=
    Finset.card_le_card Finset.inter_subset_left
  by_cases h : i ∈ X
  · simp [hitCount, sandAt, h]
  · simpa [hitCount, sandAt, h] using (Nat.mul_le_mul_left (units i) hc).trans (hw i)

private theorem sum_tickets (D k yes no : ℕ) (h : k ≤ D) :
    (∑ t ∈ Finset.range D, if t < k then yes else no) = (D - k) * no + k * yes := by
  let f (t : ℕ) := if t < k then yes else no
  have hit : (∑ t ∈ Finset.range k, f t) = k * yes := by
    calc
      _ = ∑ _t ∈ Finset.range k, yes := Finset.sum_congr rfl
        (fun t ht => ite_eq_left (Finset.mem_range.mp ht))
      _ = _ := by simp
  have miss : (∑ t ∈ Finset.range (D-k), f (k+t)) = (D-k) * no := by
    calc
      _ = ∑ _t ∈ Finset.range (D-k), no := Finset.sum_congr rfl
        (fun t _ => ite_eq_right (show ¬ k+t < k by omega))
      _ = _ := by simp
  have split := Finset.sum_range_add f k (D-k)
  rw [show k + (D-k) = D by omega, hit, miss, Nat.add_comm] at split
  exact split

theorem stepMass_eq_ticket_sum {D : ℕ} {units : V → ℕ} (hw : ValidWeights G D units)
    (i : V) (f : Finset V → ℕ) (X : Finset V) :
    stepMass G D units i f X = ∑ t ∈ Finset.range D, f (trial G units X i t) := by
  unfold stepMass
  rw [← sum_tickets D (hitCount G units X i) (f (born X i)) (f X) (hitCount_le G hw X i)]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : t < hitCount G units X i <;> simp [trial, h]

private theorem hitCount_born_nonadjacent (units : V → ℕ) (X : Finset V) (i j : V)
    (hji : j ≠ i) (hfar : i ∉ G.neighbors j) :
    hitCount G units (born X i) j = hitCount G units X j := by
  have inter : G.neighbors j ∩ insert i X = G.neighbors j ∩ X := by
    ext u
    by_cases h : u = i
    · subst u; simp [hfar]
    · simp [h]
  simp [hitCount, sandAt, occupiedNeighbors, born, hji, inter]

theorem nonadjacent_trials_commute (D : ℕ) (units : V → ℕ) (i j : V)
    (hij : i ≠ j) (hfar : j ∉ G.neighbors i) (f : Finset V → ℕ) (X : Finset V) :
    stepMass G D units i (stepMass G D units j f) X =
      stepMass G D units j (stepMass G D units i f) X := by
  have hfar' : i ∉ G.neighbors j := fun h => hfar ((G.symmetric j i).mp h)
  have eq : born (born X i) j = born (born X j) i := Finset.insert_comm ..
  simp only [stepMass, hitCount_born_nonadjacent G units X i j hij.symm hfar',
    hitCount_born_nonadjacent G units X j i hij hfar, eq, Nat.mul_add]
  ac_rfl

def occupied (i : V) (X : Finset V) : ℕ := if i ∈ X then 1 else 0

theorem occupiedNeighbors_eq_sum (X : Finset V) (v : V) :
    occupiedNeighbors G X v = ∑ u ∈ G.neighbors v, occupied u X := by
  simp [occupiedNeighbors, occupied, Finset.sum_ite_mem]

/-- One ticket per occupied neighbor, out of 800. The reported numbers are
counts of elementary outcomes, not rounded probabilities. -/
theorem three_cell_order_witness :
    let G := moore 3
    let a : Cell 3 := (1,0)
    let b : Cell 3 := (1,1)
    let c : Cell 3 := (1,2)
    let K := stepMass G 800 (fun _ => 1)
    K b (K c (occupied c)) {a} = 1 ∧ K c (K b (occupied c)) {a} = 0 := by
  decide

theorem harvest_trial_order_witness :
    let G := moore 3
    let a : Cell 3 := (1,0)
    let b : Cell 3 := (1,1)
    let K := stepMass G 800 (fun _ => 1)
    K b (occupied b) (harvest {a} a) = 0 ∧
      K b (fun X => occupied b (harvest X a)) {a} = 1 := by
  decide

/-- 120/d tickets out of 12000 for d = 3, 5, 8. -/
def degreeUnits (i : V) : ℕ := 120 / (G.neighbors i).card

omit [DecidableEq V] in
theorem degreeUnits_valid : ValidWeights G 12000 (degreeUnits G) := by
  intro i
  exact (Nat.div_mul_le_self 120 (G.neighbors i).card).trans (by decide)

def frozenMass [Fintype V] (units : V → ℕ) (X : Finset V) : ℕ := ∑ i, hitCount G units X i

theorem frozenMass_harvest_balance [Fintype V] (units : V → ℕ) (X : Finset V)
    (i : V) (hi : i ∈ X) :
    frozenMass G units (harvest X i) + ∑ j ∈ G.neighbors i \ X, units j =
      frozenMass G units X + units i * occupiedNeighbors G X i := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl (fun j _ =>
    congrArg (fun k : ℕ => units j * k) (sandAt_harvest_balance G X i j hi))
  simpa only [frozenMass, hitCount, Nat.mul_add, Finset.sum_add_distrib, mul_ite,
    Nat.mul_zero, Nat.mul_one, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h

theorem centre_harvest_can_lower_or_raise :
    let G := moore 3
    let i : Cell 3 := (1,1)
    totalSand G {i} = 8 ∧ totalSand G (harvest {i} i) = 0 ∧
    totalSand G Finset.univ = 0 ∧ totalSand G (harvest Finset.univ i) = 8 := by
  decide

theorem corner_sign_reversal :
    let G := moore 3
    let corner : Cell 3 := (0,0)
    let X : Finset (Cell 3) := {corner, (0,1)}
    let H := harvest X corner
    frozenMass G (fun _ => 15) H + 15 = frozenMass G (fun _ => 15) X ∧
      frozenMass G (degreeUnits G) H = frozenMass G (degreeUnits G) X + 1 := by
  decide

theorem seven_seed_and_pair :
    let G := moore 7
    let a : Cell 7 := (3,3)
    let b : Cell 7 := (3,4)
    totalSand G {a} = 8 ∧ totalSand G {a,b} = 14 ∧
      totalSand G (harvest {a,b} b) = 8 := by
  dsimp only
  simp only [totalSand_eq_boundary]
  decide

/-- A configuration and the number of elementary ticket histories with that
configuration. Different entries may have the same configuration. -/
abbrev Ensemble (V : Type*) := List (Finset V × ℕ)

def moment (μ : Ensemble V) (f : Finset V → ℕ) : ℕ :=
  (μ.map (fun t => t.2 * f t.1)).sum

def visit (D : ℕ) (units : V → ℕ) (i : V) (μ : Ensemble V) : Ensemble V :=
  μ.flatMap fun (X, m) =>
    let k := hitCount G units X i
    [(X, m * (D-k)), (born X i, m * k)]

def sweep (D : ℕ) (units : V → ℕ) (μ : Ensemble V) (order : List V) : Ensemble V :=
  order.foldl (fun ν i => visit G D units i ν) μ

omit [DecidableEq V] in
private theorem moment_cons (t : Finset V × ℕ) (μ : Ensemble V) (f : Finset V → ℕ) :
    moment (t :: μ) f = t.2 * f t.1 + moment μ f := by simp [moment]

omit [DecidableEq V] in
private theorem moment_congr (μ : Ensemble V) {f g : Finset V → ℕ}
    (h : ∀ t ∈ μ, f t.1 = g t.1) : moment μ f = moment μ g := by
  induction μ with
  | nil => rfl
  | cons t rest ih =>
    have tail := ih (fun s hs => h s (List.mem_cons_of_mem t hs))
    simpa [moment, h t (List.mem_cons_self ..)] using
      congrArg (fun z => t.2 * g t.1 + z) tail

omit [DecidableEq V] in
private theorem moment_scale (μ : Ensemble V) (c : ℕ) (f : Finset V → ℕ) :
    moment μ (fun X => c * f X) = c * moment μ f := by
  induction μ with
  | nil => simp [moment]
  | cons t rest ih =>
    simp only [moment_cons, ih, Nat.mul_add, Nat.mul_left_comm t.2 c]

omit [DecidableEq V] in
private theorem moment_sum (μ : Ensemble V) (S : Finset V) (f : V → Finset V → ℕ) :
    moment μ (fun X => ∑ j ∈ S, f j X) = ∑ j ∈ S, moment μ (f j) := by
  induction μ with
  | nil => simp [moment]
  | cons t rest ih =>
    simp only [moment_cons, ih, Finset.mul_sum, Finset.sum_add_distrib]

theorem moment_visit (D : ℕ) (units : V → ℕ) (i : V) (μ : Ensemble V) (f : Finset V → ℕ) :
    moment (visit G D units i μ) f = moment μ (stepMass G D units i f) := by
  induction μ with
  | nil => rfl
  | cons t rest ih =>
    rcases t with ⟨X, m⟩
    change (m * (D - hitCount G units X i)) * f X +
      ((m * hitCount G units X i) * f (born X i) + moment (visit G D units i rest) f) =
      m * stepMass G D units i f X + moment rest (stepMass G D units i f)
    rw [ih]
    simp only [stepMass, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem sweep_total_mass {D : ℕ} {units : V → ℕ} (hw : ValidWeights G D units)
    (μ : Ensemble V) (order : List V) :
    moment (sweep G D units μ order) (fun _ => 1) = D ^ order.length * moment μ (fun _ => 1) := by
  induction order generalizing μ with
  | nil => simp [sweep]
  | cons i rest ih =>
    change moment (sweep G D units (visit G D units i μ) rest) _ = _
    rw [ih, moment_visit]
    have row (X : Finset V) : stepMass G D units i (fun _ => 1) X = D := by
      simpa [stepMass] using Nat.sub_add_cancel (hitCount_le G hw X i)
    rw [show stepMass G D units i (fun _ => 1) = (fun _ => D) from funext row]
    have scale := moment_scale μ D (fun _ => 1)
    simpa [List.length_cons, Nat.pow_succ, Nat.mul_assoc] using
      congrArg (fun n => D ^ rest.length * n) (by simpa using scale :
        moment μ (fun _ => D) = D * moment μ (fun _ => 1))

/-- Before a first visit to an initially empty site, every possible history
still has that site empty. This holds even for zero-weight formal branches. -/
private theorem empty_before_visit (D : ℕ) (units : V → ℕ) (i : V)
    (μ : Ensemble V) (order : List V) (unvisited : i ∉ order)
    (empty : ∀ t ∈ μ, i ∉ t.1) : ∀ s ∈ sweep G D units μ order, i ∉ s.1 := by
  induction order generalizing μ with
  | nil => exact empty
  | cons j rest ih =>
    have hij : i ≠ j := fun h => unvisited (List.mem_cons.mpr (Or.inl h))
    apply ih _ (fun h => unvisited (List.mem_cons_of_mem j h))
    intro s hs
    obtain ⟨⟨X, m⟩, hm, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_cons.mp hs with eq | hs
    · simpa only [eq] using empty (X, m) hm
    · rcases List.mem_singleton.mp hs with rfl
      simpa [born, hij] using empty (X, m) hm

/-- The exact first-moment recursion for a fresh, initially empty site. If
the prefix has k trials and the initial mass is 1, divide the left side by
D^(k+1) and each previous marginal by D^k to obtain the probability formula.
The theorem allows any prefix avoiding i and follows from the full ticket law. -/
theorem fresh_sweep_marginal (D : ℕ) (units : V → ℕ) (X : Finset V)
    (i : V) (order : List V) (hx : i ∉ X) (fresh : i ∉ order) :
    let μ := sweep G D units [(X, 1)] order
    moment (visit G D units i μ) (occupied i) =
      units i * ∑ j ∈ G.neighbors i, moment μ (occupied j) := by
  dsimp only
  let μ := sweep G D units [(X, 1)] order
  have empty : ∀ t ∈ μ, i ∉ t.1 := empty_before_visit G D units i _ order fresh (by simpa using hx)
  change moment (visit G D units i μ) (occupied i) = _
  rw [moment_visit]
  calc
    _ = moment μ (fun Y => units i * ∑ j ∈ G.neighbors i, occupied j Y) := by
      apply moment_congr
      intro t ht
      simp [stepMass, occupied, born, empty t ht, hitCount, sandAt, occupiedNeighbors_eq_sum]
    _ = _ := by rw [moment_scale, moment_sum]

end CPRRegeneration
