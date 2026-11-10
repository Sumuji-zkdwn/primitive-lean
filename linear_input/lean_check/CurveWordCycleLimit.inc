/-!
The exact long-word limit for the four-orientation two-arc model.

An explicit potential bounds every edge from below, and a chosen outgoing
letter attains equality at every orientation.  These verified edge identities
give finite-horizon bounds and an actual limit, without assuming a general
minimum-cycle-mean theorem or an asymptotic optimality conclusion.
Input u is normalized as physical u * xi / c0.
-/

noncomputable section

namespace LinearInputCurveWordCycleLimit

open LinearInputCurveWordFiniteState Filter

def rate (u : ℝ) : ℝ := min 1 (5 - |u|)

def potential (u : ℝ) (q : Fin 4) : ℝ :=
  if u < -4 then
    match q.val with
    | 0 => 0
    | 1 => -4 - 4 * u
    | 2 => -8 - 2 * u
    | _ => -12
  else if 4 < u then
    match q.val with
    | 0 => 0
    | 1 => -4 - 2 * u
    | 2 => 8 - 2 * u
    | _ => 4 + 2 * u
  else
    match q.val with
    | 0 => 0
    | 1 => -3 * u
    | 2 => 0
    | _ => 3 * u

def selectedLetter (u : ℝ) (q : Fin 4) : Bool :=
  if u < -4 then decide (q.val < 2)
  else if 4 < u then decide (q.val ≠ 1)
  else true

theorem potential_zero (u : ℝ) : potential u 0 = 0 := by simp [potential]

theorem rate_negative (u : ℝ) (hu : u < -4) : rate u = 5 + u := by
  rw [rate, abs_of_nonpos (by linarith), min_eq_right (by linarith)]
  ring

theorem rate_positive (u : ℝ) (hu : 4 < u) : rate u = 5 - u := by
  rw [rate, abs_of_nonneg (by linarith), min_eq_right (by linarith)]

theorem rate_middle (u : ℝ) (hlo : -4 ≤ u) (hhi : u ≤ 4) : rate u = 1 := by
  have ha : |u| ≤ 4 := abs_le.mpr ⟨hlo, hhi⟩
  exact min_eq_left (by linarith)

/-- All eight directed edges satisfy the potential lower bound in each regime. -/
theorem edge_lower_bound (u : ℝ) (q : Fin 4) (a : Bool) :
    rate u + potential u (arcNext q a) - potential u q ≤ arcEdge u 0 q a := by
  by_cases hn : u < -4
  · rw [rate_negative u hn]
    fin_cases q <;> cases a <;>
      norm_num [potential, hn, arcNext, arcEdge, LinearInputCurveWordFinite.rotate] <;>
      linarith
  · by_cases hp : 4 < u
    · rw [rate_positive u hp]
      fin_cases q <;> cases a <;>
        norm_num [potential, hn, hp, arcNext, arcEdge, LinearInputCurveWordFinite.rotate] <;>
        linarith
    · rw [rate_middle u (le_of_not_gt hn) (le_of_not_gt hp)]
      fin_cases q <;> cases a <;>
        norm_num [potential, hn, hp, arcNext, arcEdge, LinearInputCurveWordFinite.rotate] <;>
        linarith

/-- A concrete outgoing letter attains the lower bound at each state. -/
theorem selected_edge_eq (u : ℝ) (q : Fin 4) :
    arcEdge u 0 q (selectedLetter u q) =
      rate u + potential u (arcNext q (selectedLetter u q)) - potential u q := by
  by_cases hn : u < -4
  · rw [rate_negative u hn]
    fin_cases q <;>
      norm_num [potential, selectedLetter, hn, arcNext, arcEdge,
        LinearInputCurveWordFinite.rotate] <;> ring
  · by_cases hp : 4 < u
    · rw [rate_positive u hp]
      fin_cases q <;>
        norm_num [potential, selectedLetter, hn, hp, arcNext, arcEdge,
          LinearInputCurveWordFinite.rotate] <;> ring
    · rw [rate_middle u (le_of_not_gt hn) (le_of_not_gt hp)]
      fin_cases q <;>
        norm_num [potential, selectedLetter, hn, hp, arcNext, arcEdge,
          LinearInputCurveWordFinite.rotate] <;> ring

theorem word_lower_bound (u : ℝ) (q : Fin 4) (w : List Bool) :
    (w.length : ℝ) * rate u + potential u (terminal arcNext q w) - potential u q ≤
      wordCost arcNext (arcEdge u 0) q w := by
  induction w generalizing q with
  | nil => simp [terminal, wordCost]
  | cons a w ih =>
    have he := edge_lower_bound u q a
    have hw := ih (arcNext q a)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, terminal, wordCost]
    nlinarith

def selectedWord (u : ℝ) : ℕ → Fin 4 → List Bool
  | 0, _ => []
  | n + 1, q => selectedLetter u q :: selectedWord u n (arcNext q (selectedLetter u q))

theorem selectedWord_length (u : ℝ) (n : ℕ) (q : Fin 4) :
    (selectedWord u n q).length = n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp [selectedWord, ih]

theorem selectedWord_cost (u : ℝ) (n : ℕ) (q : Fin 4) :
    wordCost arcNext (arcEdge u 0) q (selectedWord u n q) =
      (n : ℝ) * rate u + potential u (terminal arcNext q (selectedWord u n q)) -
        potential u q := by
  induction n generalizing q with
  | zero => simp [selectedWord, terminal, wordCost]
  | succ n ih =>
    simp only [selectedWord, wordCost, terminal, ih, selected_edge_eq,
      Nat.cast_add, Nat.cast_one]
    ring

def potentialBound (u : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun q : Fin 4 => |potential u q|)

theorem abs_potential_le (u : ℝ) (q : Fin 4) :
    |potential u q| ≤ potentialBound u :=
  Finset.le_sup' (fun q : Fin 4 => |potential u q|) (Finset.mem_univ q)

theorem potentialBound_nonneg (u : ℝ) : 0 ≤ potentialBound u := by
  simpa only [potential_zero, abs_zero] using abs_potential_le u 0

theorem potential_lower (u : ℝ) (q : Fin 4) : -potentialBound u ≤ potential u q :=
  (neg_le_neg (abs_potential_le u q)).trans (neg_abs_le (potential u q))

theorem potential_upper (u : ℝ) (q : Fin 4) : potential u q ≤ potentialBound u :=
  (le_abs_self (potential u q)).trans (abs_potential_le u q)

/-- The error from n times the exact rate is bounded independently of n. -/
theorem bellman_bounds (u : ℝ) (n : ℕ) :
    (n : ℝ) * rate u - potentialBound u ≤ bellman arcNext (arcEdge u 0) n 0 ∧
    bellman arcNext (arcEdge u 0) n 0 ≤ (n : ℝ) * rate u + potentialBound u := by
  constructor
  · obtain ⟨w, hw, hv⟩ := bellman_attained arcNext (arcEdge u 0) n 0
    have hlow := word_lower_bound u 0 w
    have hp := potential_lower u (terminal arcNext 0 w)
    rw [hw, potential_zero, hv] at hlow
    linarith
  · have hhigh := bellman_le_word arcNext (arcEdge u 0) 0 (selectedWord u n 0)
    rw [selectedWord_length, selectedWord_cost, potential_zero] at hhigh
    have hp := potential_upper u (terminal arcNext 0 (selectedWord u n 0))
    linarith

theorem average_bounds (u : ℝ) (n : ℕ) (hn : 0 < n) :
    rate u - potentialBound u / (n : ℝ) ≤ bellman arcNext (arcEdge u 0) n 0 / (n : ℝ) ∧
    bellman arcNext (arcEdge u 0) n 0 / (n : ℝ) ≤ rate u + potentialBound u / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnzero : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  obtain ⟨hl, hu⟩ := bellman_bounds u n
  constructor
  · calc
      rate u - potentialBound u / (n : ℝ) =
          ((n : ℝ) * rate u - potentialBound u) / (n : ℝ) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hl hnpos.le
  · calc
      bellman arcNext (arcEdge u 0) n 0 / (n : ℝ) ≤
          ((n : ℝ) * rate u + potentialBound u) / (n : ℝ) :=
        div_le_div_of_nonneg_right hu hnpos.le
      _ = rate u + potentialBound u / (n : ℝ) := by field_simp

/-- The actual fixed-length optimum converges to min(1, 5 - |u|). -/
theorem bellman_average_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => bellman arcNext (arcEdge u 0) n 0 / (n : ℝ))
      atTop (nhds (min 1 (5 - |u|))) := by
  have hzero := tendsto_const_div_atTop_nhds_zero_nat (potentialBound u)
  have hlo : Tendsto (fun n : ℕ => rate u - potentialBound u / (n : ℝ))
      atTop (nhds (rate u)) := by simpa using tendsto_const_nhds.sub hzero
  have hhi : Tendsto (fun n : ℕ => rate u + potentialBound u / (n : ℝ))
      atTop (nhds (rate u)) := by simpa using tendsto_const_nhds.add hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · exact eventually_atTop.2 ⟨1, fun n hn => (average_bounds u n (by omega)).1⟩
  · exact eventually_atTop.2 ⟨1, fun n hn => (average_bounds u n (by omega)).2⟩

theorem exhaustive_average_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ =>
      ((words n).inf' (words_nonempty n)
        (fun w => arcObjective u 0 (LinearInputCurveWordFinite.state w))) / (n : ℝ))
      atTop (nhds (min 1 (5 - |u|))) := by
  simpa only [← arc_bellman_eq_exhaustiveMinimum] using bellman_average_tendsto u

end LinearInputCurveWordCycleLimit
