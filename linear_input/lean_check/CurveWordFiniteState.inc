/-!
Finite-horizon dynamic programming for additive curve-word costs.

The alphabet is finite and nonempty, so every horizon has an actual minimizing
word.  The state type can be arbitrary; for a finite orientation type this is
exactly a finite-state min-plus Bellman computation.  No asymptotic cycle-mean
or spectral-radius theorem is assumed by these finite-horizon statements.
-/

noncomputable section

namespace LinearInputCurveWordFiniteState

def terminal {Q A : Type*} (next : Q → A → Q) (q : Q) : List A → Q
  | [] => q
  | a :: w => terminal next (next q a) w

def wordCost {Q A : Type*} (next : Q → A → Q) (edge : Q → A → ℝ)
    (q : Q) : List A → ℝ
  | [] => 0
  | a :: w => edge q a + wordCost next edge (next q a) w

theorem terminal_append {Q A : Type*} (next : Q → A → Q)
    (q : Q) (v w : List A) :
    terminal next q (v ++ w) = terminal next (terminal next q v) w := by
  induction v generalizing q with
  | nil => rfl
  | cons a v ih => exact ih (next q a)

theorem wordCost_append {Q A : Type*} (next : Q → A → Q)
    (edge : Q → A → ℝ) (q : Q) (v w : List A) :
    wordCost next edge q (v ++ w) =
      wordCost next edge q v + wordCost next edge (terminal next q v) w := by
  induction v generalizing q with
  | nil => simp [wordCost, terminal]
  | cons a v ih => simp only [List.cons_append, wordCost, terminal, ih, add_assoc]

theorem terminal_repeat_cycle {Q A : Type*} (next : Q → A → Q)
    (q : Q) (w : List A) (hcycle : terminal next q w = q) (k : ℕ) :
    terminal next q (List.replicate k w).flatten = q := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ, List.flatten_cons,
      terminal_append, hcycle] using ih

theorem wordCost_repeat_cycle {Q A : Type*} (next : Q → A → Q)
    (edge : Q → A → ℝ) (q : Q) (w : List A)
    (hcycle : terminal next q w = q) (k : ℕ) :
    wordCost next edge q (List.replicate k w).flatten =
      (k : ℝ) * wordCost next edge q w := by
  induction k with
  | zero => simp [wordCost]
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, wordCost_append, hcycle, ih,
      Nat.cast_add, Nat.cast_one]
    ring

def words {A : Type*} [Fintype A] [DecidableEq A] : ℕ → Finset (List A)
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion (fun a : A => (words n).image (List.cons a))

theorem mem_words {A : Type*} [Fintype A] [DecidableEq A] (w : List A) (n : ℕ) :
    w ∈ words n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w => simp [words, ih]

theorem words_nonempty {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (n : ℕ) : (words (A := A) n).Nonempty := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨List.replicate n a, (mem_words _ _).2 (List.length_replicate ..)⟩

/-- One min-plus update, minimizing over outgoing letters rather than endpoints. -/
def bellmanStep {Q A : Type*} [Fintype A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (v : Q → ℝ) (q : Q) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a => edge q a + v (next q a))

def bellman {Q A : Type*} [Fintype A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) : ℕ → Q → ℝ
  | 0, _ => 0
  | n + 1, q => bellmanStep next edge (bellman next edge n) q

theorem bellman_zero {Q A : Type*} [Fintype A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q : Q) :
    bellman next edge 0 q = 0 := rfl

theorem bellman_succ {Q A : Type*} [Fintype A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (n : ℕ) (q : Q) :
    bellman next edge (n + 1) q =
      Finset.univ.inf' Finset.univ_nonempty
        (fun a => edge q a + bellman next edge n (next q a)) := rfl

theorem bellman_le_word {Q A : Type*} [Fintype A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q : Q) (w : List A) :
    bellman next edge w.length q ≤ wordCost next edge q w := by
  induction w generalizing q with
  | nil => exact le_rfl
  | cons a w ih =>
    exact (Finset.inf'_le _ (Finset.mem_univ a)).trans (add_le_add le_rfl (ih _))

theorem bellman_attained {Q A : Type*} [Fintype A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (n : ℕ) (q : Q) :
    ∃ w : List A, w.length = n ∧ wordCost next edge q w = bellman next edge n q := by
  induction n generalizing q with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun a => edge q a + bellman next edge n (next q a))
    obtain ⟨w, hw, hv⟩ := ih (next q a)
    refine ⟨a :: w, by simp [hw], ?_⟩
    exact (congrArg (edge q a + ·) hv).trans ha.symm

def exhaustiveMinimum {Q A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (n : ℕ) (q : Q) : ℝ :=
  (words n).inf' (words_nonempty n) (wordCost next edge q)

/-- Dynamic programming equals the actual minimum over all words of length n. -/
theorem bellman_eq_exhaustiveMinimum {Q A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (next : Q → A → Q) (edge : Q → A → ℝ) (n : ℕ) (q : Q) :
    bellman next edge n q = exhaustiveMinimum next edge n q := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro w hw
    have hlen := (mem_words w n).1 hw
    simpa only [hlen] using bellman_le_word next edge q w
  · obtain ⟨w, hw, hv⟩ := bellman_attained next edge n q
    exact (Finset.inf'_le _ ((mem_words w n).2 hw)).trans_eq hv

theorem bellman_is_global_minimum {Q A : Type*} [Fintype A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (n : ℕ) (q : Q) :
    (∃ w : List A, w.length = n ∧ wordCost next edge q w = bellman next edge n q) ∧
    ∀ v : List A, v.length = n → bellman next edge n q ≤ wordCost next edge q v := by
  refine ⟨bellman_attained next edge n q, ?_⟩
  intro v hv
  simpa only [hv] using bellman_le_word next edge q v

/-- The four orientations used by the exact two-arc model. -/
def arcPhase (s : LinearInputCurveWordFinite.State) : Fin 4 :=
  ⟨s.2.1 % 4, Nat.mod_lt _ (by decide)⟩

def arcNext (q : Fin 4) (a : Bool) : Fin 4 :=
  ⟨(q.val + if a then 1 else 3) % 4, Nat.mod_lt _ (by decide)⟩

/-- Real input coordinates are normalized by u * xi / c0. -/
def arcEdge (ux uy : ℝ) (q : Fin 4) (a : Bool) : ℝ :=
  let d := LinearInputCurveWordFinite.rotate (if a then (3, 3) else (-1, 1)) q.val
  (if a then 1 else 9) - ux * (d.1 : ℝ) - uy * (d.2 : ℝ)

def arcObjective (ux uy : ℝ) (s : LinearInputCurveWordFinite.State) : ℝ :=
  (s.2.2.1 : ℝ) - ux * (s.1.1 : ℝ) - uy * (s.1.2 : ℝ)

theorem arcPhase_step (s : LinearInputCurveWordFinite.State) (a : Bool) :
    arcPhase (LinearInputCurveWordFinite.step s a) = arcNext (arcPhase s) a := by
  apply Fin.ext
  simp [arcPhase, arcNext, LinearInputCurveWordFinite.step, Nat.add_mod]

/-- The one-step objective increment depends only on orientation and the letter. -/
theorem arcObjective_step (ux uy : ℝ) (s : LinearInputCurveWordFinite.State) (a : Bool) :
    arcObjective ux uy (LinearInputCurveWordFinite.step s a) - arcObjective ux uy s =
      arcEdge ux uy (arcPhase s) a := by
  cases a <;>
    simp [arcObjective, arcEdge, arcPhase, LinearInputCurveWordFinite.step,
      LinearInputCurveWordFinite.rotate, Nat.cast_add, Int.cast_add] <;> ring

theorem arcPhase_fold (s : LinearInputCurveWordFinite.State) (w : List Bool) :
    arcPhase (w.foldl LinearInputCurveWordFinite.step s) = terminal arcNext (arcPhase s) w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simpa only [List.foldl_cons, terminal, arcPhase_step] using ih
      (LinearInputCurveWordFinite.step s a)

/-- Telescoping proves the bridge; equality of the two costs is not a hypothesis. -/
theorem arc_wordCost_eq_objective_difference (ux uy : ℝ)
    (s : LinearInputCurveWordFinite.State) (w : List Bool) :
    wordCost arcNext (arcEdge ux uy) (arcPhase s) w =
      arcObjective ux uy (w.foldl LinearInputCurveWordFinite.step s) - arcObjective ux uy s := by
  induction w generalizing s with
  | nil => simp [wordCost]
  | cons a w ih =>
    rw [wordCost, ← arcPhase_step, ih, List.foldl_cons, ← arcObjective_step]
    ring

theorem arc_wordCost_eq_objective (ux uy : ℝ) (w : List Bool) :
    wordCost arcNext (arcEdge ux uy) 0 w =
      arcObjective ux uy (LinearInputCurveWordFinite.state w) := by
  simpa [arcPhase, arcObjective, LinearInputCurveWordFinite.state] using
    arc_wordCost_eq_objective_difference ux uy ((0, 0), 0, 0, 0) w

/-- Four real values suffice to compute the true fixed-length optimum. -/
theorem arc_bellman_is_global_minimum (ux uy : ℝ) (n : ℕ) :
    (∃ w : List Bool, w.length = n ∧
      arcObjective ux uy (LinearInputCurveWordFinite.state w) =
        bellman arcNext (arcEdge ux uy) n 0) ∧
    ∀ v : List Bool, v.length = n →
      bellman arcNext (arcEdge ux uy) n 0 ≤
        arcObjective ux uy (LinearInputCurveWordFinite.state v) := by
  simpa only [arc_wordCost_eq_objective] using
    bellman_is_global_minimum arcNext (arcEdge ux uy) n 0

theorem arc_bellman_eq_exhaustiveMinimum (ux uy : ℝ) (n : ℕ) :
    bellman arcNext (arcEdge ux uy) n 0 =
      (words n).inf' (words_nonempty n)
        (fun w => arcObjective ux uy (LinearInputCurveWordFinite.state w)) := by
  simpa only [exhaustiveMinimum, arc_wordCost_eq_objective] using
    bellman_eq_exhaustiveMinimum arcNext (arcEdge ux uy) n 0

theorem arc_pureA_cycle (ux uy : ℝ) (q : Fin 4) :
    terminal arcNext q [true, true, true, true] = q ∧
    wordCost arcNext (arcEdge ux uy) q [true, true, true, true] = 4 := by
  fin_cases q <;> norm_num [terminal, wordCost, arcNext, arcEdge,
    LinearInputCurveWordFinite.rotate] <;> ring

theorem arc_pureB_cycle (ux uy : ℝ) (q : Fin 4) :
    terminal arcNext q [false, false, false, false] = q ∧
    wordCost arcNext (arcEdge ux uy) q [false, false, false, false] = 36 := by
  fin_cases q <;> norm_num [terminal, wordCost, arcNext, arcEdge,
    LinearInputCurveWordFinite.rotate] <;> ring

theorem arc_AB_cycle_zero (u : ℝ) :
    terminal arcNext 0 [true, false] = 0 ∧
    wordCost arcNext (arcEdge u 0) 0 [true, false] / 2 = 5 - u := by
  norm_num [terminal, wordCost, arcNext, arcEdge, LinearInputCurveWordFinite.rotate]
  ring

theorem arc_AB_cycle_one (u : ℝ) :
    terminal arcNext 1 [true, false] = 1 ∧
    wordCost arcNext (arcEdge u 0) 1 [true, false] / 2 = 5 + u := by
  norm_num [terminal, wordCost, arcNext, arcEdge, LinearInputCurveWordFinite.rotate]
  ring

/-- Minimum of the displayed periodic cycle means, not an asymptotic optimality axiom. -/
def listedCycleRate (u : ℝ) : ℝ := min 1 (min 9 (min (5 - u) (5 + u)))

theorem listedCycleRate_formula (u : ℝ) : listedCycleRate u = min 1 (5 - |u|) := by
  have hm : min (5 - u) (5 + u) = 5 - |u| := by
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu, min_eq_left (by linarith)]
    · rw [abs_of_nonpos hu, min_eq_right (by linarith)]
      ring
  have h9 : 5 - |u| ≤ (9 : ℝ) := by have := abs_nonneg u; linarith
  simp only [listedCycleRate, hm, min_eq_right h9]

theorem listedCycleRate_pure_regime (u : ℝ) (hu : |u| ≤ 4) :
    listedCycleRate u = 1 := by
  rw [listedCycleRate_formula, min_eq_left (by linarith)]

theorem listedCycleRate_mixed_regime (u : ℝ) (hu : 4 ≤ |u|) :
    listedCycleRate u = 5 - |u| := by
  rw [listedCycleRate_formula, min_eq_right (by linarith)]

end LinearInputCurveWordFiniteState
