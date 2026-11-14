/-!
Boltzmann word sums and their genuine finite transfer matrices. Parallel letters
with the same destination contribute additively to a matrix entry. The matrix
power identity is proved from exhaustive word sums, not used as their definition.
-/

noncomputable section

namespace LinearInputCurveWordTransfer

open LinearInputCurveWordFiniteState Filter
open scoped BigOperators Matrix.Norms.Operator

theorem sum_words_succ {A R : Type*} [Fintype A] [DecidableEq A] [AddCommMonoid R]
    (f : List A → R) (n : ℕ) :
    ∑ w ∈ words (n + 1), f w = ∑ a : A, ∑ w ∈ words n, f (a :: w) := by
  rw [words, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_image]
    intro x _ y _ h
    exact (List.cons.inj h).2
  · intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro w ha hb
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp ha
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hb
    exact hab (List.cons.inj (hx.trans hy.symm)).1

theorem words_card {A : Type*} [Fintype A] [DecidableEq A] (n : ℕ) :
    (words (A := A) n).card = Fintype.card A ^ n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    have h := sum_words_succ (fun _ : List A => (1 : ℕ)) n
    simpa [ih, pow_succ, Nat.mul_comm] using h

def wordPartition {Q A : Type*} [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (n : ℕ) (q : Q) : ℝ :=
  ∑ w ∈ words n, Real.exp (-β * wordCost next edge q w)

def transferMatrix {Q A : Type*} [Fintype A] [DecidableEq Q]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) : Matrix Q Q ℝ :=
  fun q r => ∑ a : A, if next q a = r then Real.exp (-β * edge q a) else 0

theorem wordPartition_zero {Q A : Type*} [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (q : Q) :
    wordPartition next edge β 0 q = 1 := by simp [wordPartition, words, wordCost]

theorem wordPartition_succ {Q A : Type*} [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (n : ℕ) (q : Q) :
    wordPartition next edge β (n + 1) q =
      ∑ a : A, Real.exp (-β * edge q a) * wordPartition next edge β n (next q a) := by
  unfold wordPartition
  rw [sum_words_succ]
  apply Finset.sum_congr rfl
  intro a _
  simp only [wordCost, mul_add, Real.exp_add, Finset.mul_sum]

theorem transferMatrix_action {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (v : Q → ℝ) (q : Q) :
    ∑ r : Q, transferMatrix next edge β q r * v r =
      ∑ a : A, Real.exp (-β * edge q a) * v (next q a) := by
  simp only [transferMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem wordPartition_eq_matrix_power {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (n : ℕ) (q : Q) :
    wordPartition next edge β n q = ∑ r : Q, (transferMatrix next edge β ^ n) q r := by
  induction n generalizing q with
  | zero => simp [wordPartition_zero, Matrix.one_apply]
  | succ n ih =>
    rw [wordPartition_succ, pow_succ']
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← ih]
    exact (transferMatrix_action next edge β _ q).symm

theorem transferMatrix_nonneg {Q A : Type*} [DecidableEq Q] [Fintype A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (q r : Q) :
    0 ≤ transferMatrix next edge β q r := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> positivity

theorem transferMatrix_edge_positive {Q A : Type*} [DecidableEq Q] [Fintype A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (q : Q) (a : A) :
    0 < transferMatrix next edge β q (next q a) := by
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset A))
    (f := fun b => if next q b = next q a then Real.exp (-β * edge q b) else 0)
    (fun b _ => by split_ifs <;> positivity) (Finset.mem_univ a)
  exact (Real.exp_pos _).trans_le (by simpa only [ite_true, transferMatrix] using h)

theorem transferMatrix_pow_nonneg {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (n : ℕ) (q r : Q) :
    0 ≤ (transferMatrix next edge β ^ n) q r := by
  induction n generalizing q r with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (ih q j) (transferMatrix_nonneg next edge β j r))

theorem transferMatrix_path_positive {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (q : Q) (w : List A) :
    0 < (transferMatrix next edge β ^ w.length) q (terminal next q w) := by
  induction w generalizing q with
  | nil => simp [terminal]
  | cons a w ih =>
    rw [List.length_cons, pow_succ', Matrix.mul_apply, terminal]
    have hs := Finset.single_le_sum
      (s := (Finset.univ : Finset Q))
      (f := fun j => transferMatrix next edge β q j *
        (transferMatrix next edge β ^ w.length) j (terminal next (next q a) w))
      (fun j _ => mul_nonneg (transferMatrix_nonneg next edge β q j)
        (transferMatrix_pow_nonneg next edge β w.length j _)) (Finset.mem_univ (next q a))
    exact (mul_pos (transferMatrix_edge_positive next edge β q a) (ih (next q a))).trans_le hs

def wordFreeEnergy {Q A : Type*} [Fintype A] [DecidableEq A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (n : ℕ) (q : Q) : ℝ :=
  -Real.log (wordPartition next edge β n q) / β

theorem per_letter_bounds {Q A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) {β : ℝ} (hβ : 0 < β)
    (n : ℕ) (hn : 0 < n) (q : Q) :
    bellman next edge n q / (n : ℝ) - Real.log (Fintype.card A : ℝ) / β ≤
      wordFreeEnergy next edge β n q / (n : ℝ) ∧
    wordFreeEnergy next edge β n q / (n : ℝ) ≤ bellman next edge n q / (n : ℝ) := by
  obtain ⟨hl, hu⟩ := LinearInputCurveWordThermodynamics.freeEnergy_bounds
    (words n) (words_nonempty n) (wordCost next edge q) hβ
  change exhaustiveMinimum next edge n q - Real.log ((words (A := A) n).card : ℝ) / β ≤
    wordFreeEnergy next edge β n q at hl
  change wordFreeEnergy next edge β n q ≤ exhaustiveMinimum next edge n q at hu
  rw [← bellman_eq_exhaustiveMinimum] at hl hu
  rw [words_card, Nat.cast_pow, Real.log_pow] at hl
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnzero : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hβzero : β ≠ 0 := ne_of_gt hβ
  constructor
  · calc
      bellman next edge n q / (n : ℝ) - Real.log (Fintype.card A : ℝ) / β =
          (bellman next edge n q - (n : ℝ) * Real.log (Fintype.card A : ℝ) / β) / (n : ℝ) := by
            field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hl hnpos.le
  · exact div_le_div_of_nonneg_right hu hnpos.le

theorem transfer_rows_positive {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (q : Q) :
    0 < LinearInputCurveWordSpectral.rowSum (transferMatrix next edge β) 1 q := by
  have h := LinearInputCurveWordThermodynamics.partition_positive
    (words 1) (words_nonempty 1) (wordCost next edge q) β
  change 0 < wordPartition next edge β 1 q at h
  rw [wordPartition_eq_matrix_power] at h
  exact h

theorem transfer_reachability {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (q : Q)
    (hreach : ∀ j : Q, ∃ w : List A, terminal next q w = j) :
    ∀ j : Q, ∃ n : ℕ, 0 < (transferMatrix next edge β ^ n) q j := by
  intro j
  obtain ⟨w, hw⟩ := hreach j
  exact ⟨w.length, by simpa only [hw] using transferMatrix_path_positive next edge β q w⟩

def spectralFreeEnergy {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) : ℝ :=
  -Real.log (spectralRadius ℂ
    (LinearInputCurveWordSpectral.complexMatrix (transferMatrix next edge β))).toReal / β

/-- The finite word partition converges per letter to the usual spectral free energy. -/
theorem wordFreeEnergy_average_tendsto {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (β : ℝ) (q : Q)
    (hreach : ∀ j : Q, ∃ w : List A, terminal next q w = j) :
    Tendsto (fun n : ℕ => wordFreeEnergy next edge β n q / (n : ℝ)) atTop
      (nhds (spectralFreeEnergy next edge β)) := by
  have hlog := LinearInputCurveWordSpectral.rowSum_log_tendsto
    (transferMatrix_nonneg next edge β) (transfer_rows_positive next edge β) q
    (transfer_reachability next edge β q hreach)
  have h := hlog.mul_const (-1 / β)
  convert h using 1
  · funext n
    rw [wordFreeEnergy, wordPartition_eq_matrix_power]
    unfold LinearInputCurveWordSpectral.rowSum
    ring
  · unfold spectralFreeEnergy
    congr 1
    ring

/-- The spectral free energy is within log(card A)/beta of the minimum cycle mean. -/
theorem spectralFreeEnergy_bounds {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) {β : ℝ} (hβ : 0 < β) (q : Q)
    (hreach : ∀ j : Q, ∃ w : List A, terminal next q w = j) :
    LinearInputCurveWordGraphLimit.cycleMean next edge - Real.log (Fintype.card A : ℝ) / β ≤
      spectralFreeEnergy next edge β ∧
    spectralFreeEnergy next edge β ≤ LinearInputCurveWordGraphLimit.cycleMean next edge := by
  have hmin := LinearInputCurveWordGraphLimit.bellman_average_tendsto next edge q hreach
  have hfree := wordFreeEnergy_average_tendsto next edge β q hreach
  constructor
  · apply le_of_tendsto_of_tendsto (hmin.sub tendsto_const_nhds) hfree
    exact eventually_atTop.2 ⟨1, fun n hn => (per_letter_bounds next edge hβ n (by omega) q).1⟩
  · apply le_of_tendsto_of_tendsto hfree hmin
    exact eventually_atTop.2 ⟨1, fun n hn => (per_letter_bounds next edge hβ n (by omega) q).2⟩

/-- After the long-word limit, the zero-temperature spectral limit is the cycle mean. -/
theorem spectralFreeEnergy_zero_temperature {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (next : Q → A → Q) (edge : Q → A → ℝ) (q : Q)
    (hreach : ∀ j : Q, ∃ w : List A, terminal next q w = j) :
    Tendsto (spectralFreeEnergy next edge) atTop
      (nhds (LinearInputCurveWordGraphLimit.cycleMean next edge)) := by
  have hzero : Tendsto (fun β : ℝ => Real.log (Fintype.card A : ℝ) / β) atTop (nhds 0) :=
    tendsto_id.const_div_atTop _
  have hlo : Tendsto (fun β : ℝ => LinearInputCurveWordGraphLimit.cycleMean next edge -
      Real.log (Fintype.card A : ℝ) / β) atTop
      (nhds (LinearInputCurveWordGraphLimit.cycleMean next edge)) := by
    simpa using tendsto_const_nhds.sub hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact (spectralFreeEnergy_bounds next edge hβ q hreach).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact (spectralFreeEnergy_bounds next edge hβ q hreach).2

end LinearInputCurveWordTransfer
