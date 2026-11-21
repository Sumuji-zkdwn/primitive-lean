import Mathlib.Tactic

/-!
# Dual finite metrics and observer-dependent sandpile patterns

A common point set carries distinct finite metrics. A toppling graph is derived
from the *internal* metric by thresholding pairwise distances at one.
Finite metrics do not assert differentiable smoothness; see accompanying notes.
-/

namespace DualMetricSandpile

abbrev Site := Fin 3
abbrev Distance := Site → Site → ℕ
abbrev Configuration := Site → ℕ

/-- Finite metric axioms, including identity of indiscernibles. -/
def IsFiniteMetric (d : Distance) : Prop :=
  (∀ x, d x x = 0) ∧
  (∀ x y, d x y = d y x) ∧
  (∀ x y, d x y = 0 → x = y) ∧
  (∀ x y z, d x z ≤ d x y + d y z)

/-- Outer positions 0,1,2. -/
def outside (x y : Site) : ℕ :=
  if x = y then 0
  else if (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) then 2
  else 1

/-- Inner positions 0,1,4. -/
def inside (x y : Site) : ℕ :=
  if x = y then 0
  else if (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) then 1
  else if (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) then 3
  else 4

/-- Inner positions 0,1,3: different distances, same threshold graph. -/
def insideVariant (x y : Site) : ℕ :=
  if x = y then 0
  else if (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) then 1
  else if (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) then 2
  else 3

theorem outside_metric : IsFiniteMetric outside := by decide
theorem inside_metric : IsFiniteMetric inside := by decide
theorem insideVariant_metric : IsFiniteMetric insideVariant := by decide

/-- The two metrics are bi-Lipschitz comparable. -/
theorem comparable : ∀ x y, outside x y ≤ inside x y ∧
    inside x y ≤ 3 * outside x y := by decide

theorem distances_disagree : outside 1 2 ≠ inside 1 2 := by decide

def edge (d : Distance) (x y : Site) : ℕ :=
  if x ≠ y ∧ d x y ≤ 1 then 1 else 0

/-- Every site also loses one chip to a sink whenever it fires. -/
def threshold (d : Distance) (x : Site) : ℕ :=
  1 + ∑ y : Site, edge d x y

def Legal (d : Distance) (c : Configuration) (s : Site) : Prop :=
  threshold d s ≤ c s

def Stable (d : Distance) (c : Configuration) : Prop :=
  ∀ s, ¬ Legal d c s

/-- This is a firing only if Legal d c s holds. -/
def fire (d : Distance) (c : Configuration) (s : Site) : Configuration :=
  fun t => if s = t then c t - threshold d s else c t + edge d s t

/-- Graph equality, rather than numeric distance equality, preserves thresholds. -/
theorem threshold_invariant {d e : Distance}
    (h : ∀ x y, edge d x y = edge e x y) (s : Site) :
    threshold d s = threshold e s := by
  simp [threshold, h]

/-- Same thresholded graph implies the same single-firing operation. -/
theorem fire_invariant {d e : Distance}
    (h : ∀ x y, edge d x y = edge e x y)
    (c : Configuration) (s : Site) : fire d c s = fire e c s := by
  funext t
  change (if s = t then c t - threshold d s else c t + edge d s t) =
    (if s = t then c t - threshold e s else c t + edge e s t)
  rw [threshold_invariant h s, h s t]

theorem hidden_edges : ∀ x y, edge inside x y = edge insideVariant x y := by
  decide

theorem hidden_distances_disagree : inside 1 2 ≠ insideVariant 1 2 := by
  decide

/-- Different numeric metrics can be indistinguishable for every single firing. -/
theorem hidden_fire (c : Configuration) (s : Site) :
    fire inside c s = fire insideVariant c s :=
  fire_invariant hidden_edges c s

def twoAtCenter : Configuration := fun s => if s = 1 then 2 else 0

theorem outer_thresholds :
    threshold outside 0 = 2 ∧ threshold outside 1 = 3 ∧
    threshold outside 2 = 2 := by decide

theorem inner_thresholds :
    threshold inside 0 = 2 ∧ threshold inside 1 = 2 ∧
    threshold inside 2 = 1 := by decide

theorem outer_two_stable : Stable outside twoAtCenter := by decide

theorem inner_only_center_legal :
    Legal inside twoAtCenter 1 ∧
    ∀ s, Legal inside twoAtCenter s → s = 1 := by decide

def innerFinal : Configuration := fun s => if s = 0 then 1 else 0

theorem inner_firing_result : fire inside twoAtCenter 1 = innerFinal := by
  funext s
  fin_cases s <;> decide

theorem inner_final_stable : Stable inside innerFinal := by decide

def oneAtCenter : Configuration := fun s => if s = 1 then 1 else 0

theorem one_chip_indistinguishable :
    Stable outside oneAtCenter ∧ Stable inside oneAtCenter := by decide

/-- One chip cannot separate these zero-initialized protocols, but two can. -/
theorem two_chip_separates : twoAtCenter 0 ≠ innerFinal 0 := by decide

theorem same_site_labels : (0 : Site) ≠ 1 ∧ (1 : Site) ≠ 2 := by decide

end DualMetricSandpile
