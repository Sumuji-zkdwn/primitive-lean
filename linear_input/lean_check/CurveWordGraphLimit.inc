/-!
Minimum cycle mean and the long-horizon optimum for a finite directed labelled
multigraph. Transitions are total and the finite alphabet is nonempty, so there
are no dead ends. Fixed-start asymptotics require reachability of every state
from that start. The minimum is constructed from nonempty closed words of
length at most the state cardinality; neither a potential nor a limit is assumed.
-/

noncomputable section

namespace LinearInputCurveWordGraphLimit

open LinearInputCurveWordFiniteState Filter

theorem cycle_between_prefixes {Q A : Type*} (next : Q → A → Q) (q : Q)
    (w : List A) (i j : ℕ) (hij : i < j) (hj : j ≤ w.length)
    (heq : terminal next q (w.take i) = terminal next q (w.take j)) :
    ∃ p c s : List A, w = p ++ c ++ s ∧ c.length = j - i ∧
      terminal next (terminal next q p) c = terminal next q p := by
  have ht : w.take i ++ (w.take j).drop i = w.take j := by
    simpa only [List.take_take, Nat.min_eq_left hij.le] using
      List.take_append_drop i (w.take j)
  refine ⟨w.take i, (w.take j).drop i, w.drop j, ?_, ?_, ?_⟩
  · rw [ht, List.take_append_drop]
  · simp only [List.length_drop, List.length_take, Nat.min_eq_left hj]
  · have h := congrArg (terminal next q) ht
    rw [terminal_append] at h
    exact h.trans heq.symm

/-- Pigeonhole extraction of a nonempty bounded closed word from any long word. -/
theorem extract_short_cycle {Q A : Type*} [Fintype Q]
    (next : Q → A → Q) (q : Q) (w : List A) (hw : Fintype.card Q ≤ w.length) :
    ∃ p c s : List A, w = p ++ c ++ s ∧ 0 < c.length ∧
      c.length ≤ Fintype.card Q ∧ terminal next (terminal next q p) c = terminal next q p := by
  let f : Fin (Fintype.card Q + 1) → Q := fun i => terminal next q (w.take i.val)
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hij | hji
  · obtain ⟨p, c, s, hword, hlen, hcycle⟩ :=
      cycle_between_prefixes next q w i.val j.val hij (by omega) heq
    exact ⟨p, c, s, hword, by omega, by omega, hcycle⟩
  · obtain ⟨p, c, s, hword, hlen, hcycle⟩ :=
      cycle_between_prefixes next q w j.val i.val hji (by omega) heq.symm
    exact ⟨p, c, s, hword, by omega, by omega, hcycle⟩

def boundedWords {A : Type*} [Fintype A] [DecidableEq A] (N : ℕ) : Finset (List A) :=
  (Finset.range (N + 1)).biUnion (fun n => words n)

theorem mem_boundedWords {A : Type*} [Fintype A] [DecidableEq A]
    (w : List A) (N : ℕ) : w ∈ boundedWords N ↔ w.length ≤ N := by
  simp only [boundedWords, Finset.mem_biUnion, Finset.mem_range, mem_words]
  constructor
  · rintro ⟨n, hn, hw⟩
    omega
  · intro h
    exact ⟨w.length, by omega, rfl⟩

def shortCycles {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (next : Q → A → Q) : Finset (Q × List A) :=
  (Finset.univ.product (boundedWords (Fintype.card Q))).filter
    (fun z => 0 < z.2.length ∧ terminal next z.1 z.2 = z.1)

theorem mem_shortCycles {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (next : Q → A → Q) (q : Q) (w : List A) :
    (q, w) ∈ shortCycles next ↔
      w.length ≤ Fintype.card Q ∧ 0 < w.length ∧ terminal next q w = q := by
  simp [shortCycles, mem_boundedWords]

theorem shortCycles_nonempty {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A] (next : Q → A → Q) :
    (shortCycles next).Nonempty := by
  obtain ⟨q⟩ := ‹Nonempty Q›
  obtain ⟨a⟩ := ‹Nonempty A›
  obtain ⟨p, c, s, _, hcpos, hclen, hcycle⟩ :=
    extract_short_cycle next q (List.replicate (Fintype.card Q) a) (by simp)
  exact ⟨(terminal next q p, c), (mem_shortCycles next _ _).2 ⟨hclen, hcpos, hcycle⟩⟩

def cycleMean {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) : ℝ :=
  (shortCycles next).inf' (shortCycles_nonempty next)
    (fun z => wordCost next edge z.1 z.2 / (z.2.length : ℝ))

theorem short_cycle_cost_lower {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q : Q) (w : List A)
    (hshort : w.length ≤ Fintype.card Q) (hpos : 0 < w.length)
    (hcycle : terminal next q w = q) :
    (w.length : ℝ) * cycleMean next edge ≤ wordCost next edge q w := by
  have h := Finset.inf'_le
    (fun z : Q × List A => wordCost next edge z.1 z.2 / (z.2.length : ℝ))
    ((mem_shortCycles next q w).2 ⟨hshort, hpos, hcycle⟩)
  have hl : (0 : ℝ) < w.length := Nat.cast_pos.mpr hpos
  simpa only [cycleMean, mul_comm] using (le_div_iff₀ hl).mp h

theorem minimum_cycle_exists {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) :
    ∃ q : Q, ∃ w : List A, w.length ≤ Fintype.card Q ∧ 0 < w.length ∧
      terminal next q w = q ∧ wordCost next edge q w = (w.length : ℝ) * cycleMean next edge := by
  obtain ⟨⟨q, w⟩, hw, heq⟩ := Finset.exists_mem_eq_inf' (shortCycles_nonempty next)
    (fun z : Q × List A => wordCost next edge z.1 z.2 / (z.2.length : ℝ))
  obtain ⟨hshort, hpos, hcycle⟩ := (mem_shortCycles next q w).1 hw
  refine ⟨q, w, hshort, hpos, hcycle, ?_⟩
  have hl : (w.length : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hpos)
  have h := congrArg (fun x : ℝ => x * (w.length : ℝ)) heq
  simp only [div_mul_cancel₀ _ hl] at h
  simpa only [cycleMean, mul_comm] using h.symm

theorem remove_cycle_terminal {Q A : Type*} (next : Q → A → Q)
    (q : Q) (p c s : List A) (hc : terminal next (terminal next q p) c = terminal next q p) :
    terminal next q (p ++ c ++ s) = terminal next q (p ++ s) := by
  simp only [terminal_append, hc]

theorem remove_cycle_cost {Q A : Type*} (next : Q → A → Q) (edge : Q → A → ℝ)
    (q : Q) (p c s : List A) (hc : terminal next (terminal next q p) c = terminal next q p) :
    wordCost next edge q (p ++ c ++ s) =
      wordCost next edge q (p ++ s) + wordCost next edge (terminal next q p) c := by
  simp only [wordCost_append, terminal_append, hc]
  ring

def edgeBound {Q A : Type*} [Fintype Q] [Nonempty Q] [Fintype A] [Nonempty A]
    (edge : Q → A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun z : Q × A => |edge z.1 z.2|)

theorem abs_edge_le {Q A : Type*} [Fintype Q] [Nonempty Q] [Fintype A] [Nonempty A]
    (edge : Q → A → ℝ) (q : Q) (a : A) : |edge q a| ≤ edgeBound edge :=
  Finset.le_sup' (fun z : Q × A => |edge z.1 z.2|) (Finset.mem_univ (q, a))

theorem edgeBound_nonneg {Q A : Type*} [Fintype Q] [Nonempty Q] [Fintype A] [Nonempty A]
    (edge : Q → A → ℝ) : 0 ≤ edgeBound edge := by
  obtain ⟨q⟩ := ‹Nonempty Q›
  obtain ⟨a⟩ := ‹Nonempty A›
  exact (abs_nonneg (edge q a)).trans (abs_edge_le edge q a)

theorem word_cost_bounds {Q A : Type*} [Fintype Q] [Nonempty Q] [Fintype A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q : Q) (w : List A) :
    -(w.length : ℝ) * edgeBound edge ≤ wordCost next edge q w ∧
      wordCost next edge q w ≤ (w.length : ℝ) * edgeBound edge := by
  induction w generalizing q with
  | nil => simp [wordCost]
  | cons a w ih =>
    obtain ⟨hel, heu⟩ := abs_le.mp (abs_edge_le edge q a)
    obtain ⟨hwl, hwu⟩ := ih (next q a)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, wordCost]
    constructor <;> nlinarith

def residualBound {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) : ℝ :=
  (Fintype.card Q : ℝ) * (edgeBound edge + |cycleMean next edge|)

/-- Repeatedly removing bounded closed subwords leaves a short residual path. -/
theorem word_cost_lower {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q : Q) (w : List A) :
    (w.length : ℝ) * cycleMean next edge - residualBound next edge ≤ wordCost next edge q w := by
  suffices H : ∀ n : ℕ, ∀ q : Q, ∀ w : List A, w.length = n →
      (n : ℝ) * cycleMean next edge - residualBound next edge ≤ wordCost next edge q w by
    exact H w.length q w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q w hlen
    by_cases hshort : n < Fintype.card Q
    · have hw := (word_cost_bounds next edge q w).1
      rw [hlen] at hw
      have hN : (n : ℝ) ≤ Fintype.card Q := by exact_mod_cast hshort.le
      have hB := edgeBound_nonneg edge
      have hbound := mul_le_mul_of_nonneg_right hN
        (add_nonneg hB (abs_nonneg (cycleMean next edge)))
      have hmu := mul_le_mul_of_nonneg_left (le_abs_self (cycleMean next edge))
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      unfold residualBound
      nlinarith
    · obtain ⟨p, c, s, hword, hcpos, hcshort, hcycle⟩ :=
        extract_short_cycle next q w (by omega)
      have hnlen : n = p.length + c.length + s.length := by
        rw [← hlen, hword]
        simp only [List.length_append]
      have hrlen : (p ++ s).length < n := by simp only [List.length_append]; omega
      have hr := ih (p ++ s).length hrlen q (p ++ s) rfl
      have hc := short_cycle_cost_lower next edge (terminal next q p) c hcshort hcpos hcycle
      rw [hword, remove_cycle_cost next edge q p c s hcycle, hnlen]
      simp only [List.length_append, Nat.cast_add] at hr ⊢
      nlinarith

/-- The constructed rate is no greater than the mean of any nonempty closed word. -/
theorem closed_word_cost_lower {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q : Q) (w : List A)
    (hcycle : terminal next q w = q) :
    (w.length : ℝ) * cycleMean next edge ≤ wordCost next edge q w := by
  suffices H : ∀ n : ℕ, ∀ q : Q, ∀ w : List A, w.length = n → terminal next q w = q →
      (n : ℝ) * cycleMean next edge ≤ wordCost next edge q w by
    exact H w.length q w rfl hcycle
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q w hlen hwcycle
    by_cases hn : n = 0
    · have hw : w = [] := List.length_eq_zero_iff.mp (hlen.trans hn)
      subst w
      simp [hn, wordCost]
    · by_cases hshort : n ≤ Fintype.card Q
      · simpa only [hlen] using short_cycle_cost_lower next edge q w (by omega) (by omega) hwcycle
      · obtain ⟨p, c, s, hword, hcpos, hcshort, hccycle⟩ :=
          extract_short_cycle next q w (by omega)
        have hnlen : n = p.length + c.length + s.length := by
          rw [← hlen, hword]
          simp only [List.length_append]
        have hrlen : (p ++ s).length < n := by simp only [List.length_append]; omega
        have hrcycle : terminal next q (p ++ s) = q := by
          rw [← remove_cycle_terminal next q p c s hccycle, ← hword]
          exact hwcycle
        have hr := ih (p ++ s).length hrlen q (p ++ s) rfl hrcycle
        have hc := short_cycle_cost_lower next edge (terminal next q p) c hcshort hcpos hccycle
        rw [hword, remove_cycle_cost next edge q p c s hccycle, hnlen]
        simp only [List.length_append, Nat.cast_add] at hr ⊢
        nlinarith

theorem shorter_optimal_cycle_of_repeat {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Nonempty Q] [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q : Q) (w : List A)
    (hwcycle : terminal next q w = q)
    (hwcost : wordCost next edge q w = (w.length : ℝ) * cycleMean next edge)
    (i j : ℕ) (hij : i < j) (hj : j < w.length)
    (heq : terminal next q (w.take i) = terminal next q (w.take j)) :
    ∃ q' : Q, ∃ c : List A, 0 < c.length ∧ c.length < w.length ∧
      terminal next q' c = q' ∧ wordCost next edge q' c =
        (c.length : ℝ) * cycleMean next edge := by
  obtain ⟨p, c, s, hword, hlen, hc⟩ :=
    cycle_between_prefixes next q w i j hij hj.le heq
  have hrc : terminal next q (p ++ s) = q := by
    rw [← remove_cycle_terminal next q p c s hc, ← hword]
    exact hwcycle
  have hr := closed_word_cost_lower next edge q (p ++ s) hrc
  have hcc := closed_word_cost_lower next edge (terminal next q p) c hc
  rw [hword, remove_cycle_cost next edge q p c s hc] at hwcost
  simp only [List.length_append, Nat.cast_add] at hr hwcost
  refine ⟨terminal next q p, c, by omega, by omega, hc, ?_⟩
  nlinarith

/-- A minimum-mean cycle can be chosen with no repeated vertex before its return. -/
theorem minimum_simple_cycle_exists {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) :
    ∃ q : Q, ∃ w : List A, w.length ≤ Fintype.card Q ∧ 0 < w.length ∧
      terminal next q w = q ∧
      Function.Injective (fun i : Fin w.length => terminal next q (w.take i.val)) ∧
      wordCost next edge q w = (w.length : ℝ) * cycleMean next edge := by
  classical
  let P : ℕ → Prop := fun n => ∃ q : Q, ∃ w : List A,
    w.length = n ∧ n ≤ Fintype.card Q ∧ 0 < n ∧ terminal next q w = q ∧
      wordCost next edge q w = (n : ℝ) * cycleMean next edge
  have hex : ∃ n, P n := by
    obtain ⟨q, w, hs, hp, hc, hv⟩ := minimum_cycle_exists next edge
    exact ⟨w.length, q, w, rfl, hs, hp, hc, hv⟩
  obtain ⟨q, w, hlen, hs, hp, hc, hv⟩ := Nat.find_spec hex
  refine ⟨q, w, by omega, by omega, hc, ?_, by simpa only [hlen] using hv⟩
  intro i j heq
  by_contra hne
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  have hopt : wordCost next edge q w = (w.length : ℝ) * cycleMean next edge :=
    by simpa only [hlen] using hv
  have impossible : ∀ a b : Fin w.length, a.val < b.val →
      terminal next q (w.take a.val) = terminal next q (w.take b.val) → False := by
    intro a b hab he
    obtain ⟨q', c, hcp, hcl, hcc, hcv⟩ :=
      shorter_optimal_cycle_of_repeat next edge q w hc hopt a.val b.val hab b.isLt he
    have hP : P c.length := ⟨q', c, rfl, by omega, hcp, hcc, hcv⟩
    have hm := Nat.find_min' hex hP
    omega
  rcases lt_or_gt_of_ne hval with hij | hji
  · exact impossible i j hij heq
  · exact impossible j i hji heq.symm

theorem repeated_length {A : Type*} (w : List A) (k : ℕ) :
    (List.replicate k w).flatten.length = k * w.length := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

def upperBound {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (L : ℕ) : ℝ :=
  ((L + Fintype.card Q : ℕ) : ℝ) * (edgeBound edge + |cycleMean next edge|)

/-- Access a minimizing cycle, repeat it, and fill the final shorter remainder. -/
theorem words_from_minimum_cycle {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q₀ q : Q) (p c : List A)
    (hp : terminal next q₀ p = q) (hcshort : c.length ≤ Fintype.card Q)
    (hcpos : 0 < c.length) (hc : terminal next q c = q)
    (hcost : wordCost next edge q c = (c.length : ℝ) * cycleMean next edge)
    (n : ℕ) (hn : p.length ≤ n) :
    ∃ w : List A, w.length = n ∧
      wordCost next edge q₀ w ≤ (n : ℝ) * cycleMean next edge + upperBound next edge p.length := by
  obtain ⟨a⟩ := ‹Nonempty A›
  let k := (n - p.length) / c.length
  let r := (n - p.length) % c.length
  let v := (List.replicate k c).flatten
  let s := List.replicate r a
  have hrlt : r < c.length := Nat.mod_lt _ hcpos
  have hdiv : k * c.length + r = n - p.length := by
    simpa only [k, r, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div (n - p.length) c.length
  have hlen : (p ++ v ++ s).length = n := by
    simp only [List.length_append, v, s, repeated_length, List.length_replicate]
    omega
  have hv : terminal next q v = q := terminal_repeat_cycle next q c hc k
  have hpbound := (word_cost_bounds next edge q₀ p).2
  have hsbound := (word_cost_bounds next edge q s).2
  have hval : wordCost next edge q₀ (p ++ v ++ s) =
      wordCost next edge q₀ p + (k : ℝ) * ((c.length : ℝ) * cycleMean next edge) +
        wordCost next edge q s := by
    simp only [wordCost_append, terminal_append, hp, hv]
    rw [show wordCost next edge q v = (k : ℝ) * wordCost next edge q c from
      wordCost_repeat_cycle next edge q c hc k, hcost]
  have hnreal : (n : ℝ) = (p.length : ℝ) + (k : ℝ) * (c.length : ℝ) + (r : ℝ) := by
    exact_mod_cast (show n = p.length + k * c.length + r by omega)
  have hrN : (r : ℝ) ≤ Fintype.card Q := by exact_mod_cast (le_trans hrlt.le hcshort)
  have hB := edgeBound_nonneg edge
  have hfactor : 0 ≤ edgeBound edge + |cycleMean next edge| :=
    add_nonneg hB (abs_nonneg _)
  have hmore := mul_le_mul_of_nonneg_right
    (add_le_add_left hrN (p.length : ℝ)) hfactor
  have hmu := mul_le_mul_of_nonneg_left (neg_le_abs (cycleMean next edge))
    (add_nonneg (Nat.cast_nonneg p.length) (Nat.cast_nonneg r) :
      (0 : ℝ) ≤ (p.length : ℝ) + (r : ℝ))
  have hslen : s.length = r := List.length_replicate
  rw [hslen] at hsbound
  refine ⟨p ++ v ++ s, hlen, ?_⟩
  rw [hval, hnreal]
  unfold upperBound
  simp only [Nat.cast_add]
  nlinarith

theorem bellman_lower_bound {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q : Q) (n : ℕ) :
    (n : ℝ) * cycleMean next edge - residualBound next edge ≤ bellman next edge n q := by
  obtain ⟨w, hw, hv⟩ := bellman_attained next edge n q
  simpa only [hw, hv] using word_cost_lower next edge q w

theorem bellman_upper_eventually {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q₀ : Q)
    (hreach : ∀ q : Q, ∃ p : List A, terminal next q₀ p = q) :
    ∃ L : ℕ, ∀ n : ℕ, L ≤ n →
      bellman next edge n q₀ ≤ (n : ℝ) * cycleMean next edge + upperBound next edge L := by
  obtain ⟨q, c, hs, hp, hc, hv⟩ := minimum_cycle_exists next edge
  obtain ⟨p, hpath⟩ := hreach q
  refine ⟨p.length, ?_⟩
  intro n hn
  obtain ⟨w, hw, hcost⟩ := words_from_minimum_cycle next edge q₀ q p c hpath hs hp hc hv n hn
  have hmin := bellman_le_word next edge q₀ w
  rw [hw] at hmin
  exact hmin.trans hcost

/-- General finite-state minimum-cycle-mean limit for a start reaching all states. -/
theorem bellman_average_tendsto {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q₀ : Q)
    (hreach : ∀ q : Q, ∃ p : List A, terminal next q₀ p = q) :
    Tendsto (fun n : ℕ => bellman next edge n q₀ / (n : ℝ)) atTop
      (nhds (cycleMean next edge)) := by
  obtain ⟨L, hupper⟩ := bellman_upper_eventually next edge q₀ hreach
  have hlzero := tendsto_const_div_atTop_nhds_zero_nat (residualBound next edge)
  have huzero := tendsto_const_div_atTop_nhds_zero_nat (upperBound next edge L)
  have hl : Tendsto (fun n : ℕ => cycleMean next edge - residualBound next edge / (n : ℝ))
      atTop (nhds (cycleMean next edge)) := by simpa using tendsto_const_nhds.sub hlzero
  have hu : Tendsto (fun n : ℕ => cycleMean next edge + upperBound next edge L / (n : ℝ))
      atTop (nhds (cycleMean next edge)) := by simpa using tendsto_const_nhds.add huzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnzero : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    calc
      cycleMean next edge - residualBound next edge / (n : ℝ) =
          ((n : ℝ) * cycleMean next edge - residualBound next edge) / (n : ℝ) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (bellman_lower_bound next edge q₀ n) hnpos.le
  · refine eventually_atTop.2 ⟨max L 1, ?_⟩
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnzero : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    calc
      bellman next edge n q₀ / (n : ℝ) ≤
          ((n : ℝ) * cycleMean next edge + upperBound next edge L) / (n : ℝ) :=
        div_le_div_of_nonneg_right (hupper n (by omega)) hnpos.le
      _ = cycleMean next edge + upperBound next edge L / (n : ℝ) := by field_simp

theorem exhaustive_average_tendsto {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q₀ : Q)
    (hreach : ∀ q : Q, ∃ p : List A, terminal next q₀ p = q) :
    Tendsto (fun n : ℕ => exhaustiveMinimum next edge n q₀ / (n : ℝ)) atTop
      (nhds (cycleMean next edge)) := by
  simpa only [← bellman_eq_exhaustiveMinimum] using bellman_average_tendsto next edge q₀ hreach

end LinearInputCurveWordGraphLimit
