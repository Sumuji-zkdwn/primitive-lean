/-!
Long-word growth of nonnegative transfer matrices. The spectral radius is the
usual complex spectral radius, not a definition in terms of partition growth.
The analytic input is mathlib's Gelfand formula; finite row-sum comparisons
connect it to a fixed initial state.
-/

noncomputable section

namespace LinearInputCurveWordSpectral
open Matrix Filter
open scoped Topology NNReal ENNReal Matrix.Norms.Operator
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

def rowSum (M : Matrix Q Q ℝ) (n : ℕ) (q : Q) : ℝ := ∑ j, (M ^ n) q j

def complexMatrix (M : Matrix Q Q ℝ) : Matrix Q Q ℂ := M.map Complex.ofReal

theorem complexMatrix_pow (M : Matrix Q Q ℝ) (n : ℕ) :
    complexMatrix M ^ n = complexMatrix (M ^ n) := by
  exact (Matrix.map_pow M Complex.ofRealHom n).symm

theorem rowSum_zero (M : Matrix Q Q ℝ) (q : Q) : rowSum M 0 q = 1 := by
  simp [rowSum, Matrix.one_apply]

theorem rowSum_nonneg {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j) (n : ℕ) (q : Q) :
    0 ≤ rowSum M n q :=
  Finset.sum_nonneg (fun j _ => Matrix.pow_apply_nonneg hM n q j)

theorem rowSum_add (M : Matrix Q Q ℝ) (n k : ℕ) (q : Q) :
    rowSum M (n + k) q = ∑ j, (M ^ n) q j * rowSum M k j := by
  simp only [rowSum, pow_add, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem rowSum_le_norm {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j) (n : ℕ) (q : Q) :
    rowSum M n q ≤ ‖complexMatrix M ^ n‖ := by
  rw [complexMatrix_pow, Matrix.linfty_opNorm_def]
  have hh := Finset.le_sup (s := Finset.univ)
    (f := fun i : Q => ∑ j : Q, ‖complexMatrix (M ^ n) i j‖₊) (Finset.mem_univ q)
  have hh' := NNReal.coe_le_coe.mpr hh
  simpa only [rowSum, NNReal.coe_sum, coe_nnNorm, complexMatrix, Matrix.map_apply,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Matrix.pow_apply_nonneg hM n q _)] using hh'

theorem norm_le_of_rowSum_le {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C) (h : ∀ q, rowSum M n q ≤ C) :
    ‖complexMatrix M ^ n‖ ≤ C := by
  rw [complexMatrix_pow, Matrix.linfty_opNorm_def]
  have hs : (Finset.univ.sup fun i : Q => ∑ j : Q, ‖complexMatrix (M ^ n) i j‖₊) ≤
      (⟨C, hC⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    simpa only [rowSum, NNReal.coe_sum, coe_nnNorm, complexMatrix, Matrix.map_apply,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Matrix.pow_apply_nonneg hM n i _)] using! h i
  exact_mod_cast hs

theorem rowSum_add_upper {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (n k : ℕ) (q : Q) :
    rowSum M (n + k) q ≤ rowSum M n q * ‖complexMatrix M ^ k‖ := by
  rw [rowSum_add, rowSum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (rowSum_le_norm hM k j) (Matrix.pow_apply_nonneg hM n q j)

theorem rowSum_add_lower {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (n k : ℕ) (q j : Q) :
    (M ^ k) q j * rowSum M n j ≤ rowSum M (n + k) q := by
  rw [Nat.add_comm, rowSum_add]
  exact Finset.single_le_sum (fun i _ =>
    mul_nonneg (Matrix.pow_apply_nonneg hM k q i) (rowSum_nonneg hM n i)) (Finset.mem_univ j)

theorem rowSum_lower_pow {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {δ : ℝ} (hδ : 0 ≤ δ) (hlower : ∀ q, δ ≤ rowSum M 1 q) (n : ℕ) (q : Q) :
    δ ^ n ≤ rowSum M n q := by
  induction n generalizing q with
  | zero => simp [rowSum_zero]
  | succ n ih =>
    have hs : rowSum M (n + 1) q = ∑ j, (M ^ 1) q j * rowSum M n j := by
      simpa only [Nat.add_comm] using rowSum_add M 1 n q
    rw [hs]
    calc
      δ ^ (n + 1) = (∑ j, (M ^ 1) q j) * δ ^ n +
          (δ - rowSum M 1 q) * δ ^ n := by simp only [rowSum]; ring
      _ ≤ (∑ j, (M ^ 1) q j) * δ ^ n := by
        have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hlower q)) (pow_nonneg hδ n)
        linarith
      _ = ∑ j, (M ^ 1) q j * δ ^ n := by rw [Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (ih j) (by simpa using hM q j))

variable [Nonempty Q]

theorem spectralRadius_ne_top (M : Matrix Q Q ℝ) :
    spectralRadius ℂ (complexMatrix M) ≠ ⊤ := by
  have _ := ‹Nonempty Q›
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnNorm _)

/-- Gelfand's formula for the actual complexified transfer matrix. -/
theorem norm_root_tendsto (M : Matrix Q Q ℝ) :
    Tendsto (fun n : ℕ => ‖complexMatrix M ^ n‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ (complexMatrix M)).toReal) := by
  have h := (ENNReal.tendsto_toReal (spectralRadius_ne_top M)).comp
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexMatrix M))
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using h

/-- Reachability from q gives a uniform, length-independent comparison of
the operator norm and the partition sum starting at q. -/
theorem exists_norm_bound_by_row {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (q : Q) (hreach : ∀ j, ∃ k : ℕ, 0 < (M ^ k) q j) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, ‖complexMatrix M ^ n‖ ≤ C * rowSum M n q := by
  choose k hk using hreach
  let coeff : Q → ℝ := fun j => ‖complexMatrix M ^ k j‖ / (M ^ k j) q j
  let C : ℝ := max 1 (Finset.univ.sup' Finset.univ_nonempty coeff)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C, hC, fun n => norm_le_of_rowSum_le hM n
    (mul_nonneg hC.le (rowSum_nonneg hM n q)) ?_⟩
  intro j
  have hlow := rowSum_add_lower hM n (k j) q j
  have hhigh := rowSum_add_upper hM n (k j) q
  have hcj : coeff j ≤ C :=
    (Finset.le_sup' coeff (Finset.mem_univ j)).trans (le_max_right _ _)
  have hdiv : rowSum M n j ≤ coeff j * rowSum M n q := by
    dsimp [coeff]
    rw [div_mul_eq_mul_div, le_div_iff₀ (hk j)]
    nlinarith [hlow.trans hhigh]
  exact hdiv.trans (mul_le_mul_of_nonneg_right hcj (rowSum_nonneg hM n q))

theorem spectralRadius_pos_of_rowSum_pos {M : Matrix Q Q ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hrows : ∀ q, 0 < rowSum M 1 q) :
    0 < (spectralRadius ℂ (complexMatrix M)).toReal := by
  obtain ⟨q, _, hq⟩ := Finset.exists_min_image Finset.univ (rowSum M 1) Finset.univ_nonempty
  let δ := rowSum M 1 q
  have hδ : 0 < δ := hrows q
  have hlower : ∀ j, δ ≤ rowSum M 1 j := fun j => hq j (Finset.mem_univ j)
  have hlim : δ ≤ (spectralRadius ℂ (complexMatrix M)).toReal := by
    apply ge_of_tendsto (norm_root_tendsto M)
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpow := (rowSum_lower_pow hM hδ.le hlower n q).trans (rowSum_le_norm hM n q)
    have hroot := Real.rpow_le_rpow (pow_nonneg hδ.le n) hpow (by positivity : 0 ≤ 1 / (n : ℝ))
    have he : (δ ^ n) ^ (1 / (n : ℝ)) = δ := by
      rw [← Real.rpow_natCast_mul hδ.le, mul_one_div_cancel (ne_of_gt hnpos), Real.rpow_one]
    rwa [he] at hroot
  exact hδ.trans_le hlim

theorem rowSum_pos {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hrows : ∀ q, 0 < rowSum M 1 q) (n : ℕ) (q : Q) : 0 < rowSum M n q := by
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ (rowSum M 1) Finset.univ_nonempty
  exact (pow_pos (hrows j) n).trans_le
    (rowSum_lower_pow hM (hrows j).le (fun i => hj i (Finset.mem_univ i)) n q)

theorem norm_log_tendsto {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hrows : ∀ q, 0 < rowSum M 1 q) :
    Tendsto (fun n : ℕ => Real.log ‖complexMatrix M ^ n‖ / (n : ℝ)) atTop
      (𝓝 (Real.log (spectralRadius ℂ (complexMatrix M)).toReal)) := by
  have h := (norm_root_tendsto M).log (spectralRadius_pos_of_rowSum_pos hM hrows).ne'
  have hp (n : ℕ) : 0 < ‖complexMatrix M ^ n‖ :=
    (rowSum_pos hM hrows n (Classical.choice inferInstance)).trans_le (rowSum_le_norm hM n _)
  simpa only [Real.log_rpow (hp _), one_div_mul_eq_div] using h

/-- A fixed initial row has the same exponential growth as the usual spectral
radius when all states are reachable from it. No aperiodicity is needed. -/
theorem rowSum_log_tendsto {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hrows : ∀ q, 0 < rowSum M 1 q) (q : Q)
    (hreach : ∀ j, ∃ k : ℕ, 0 < (M ^ k) q j) :
    Tendsto (fun n : ℕ => Real.log (rowSum M n q) / (n : ℝ)) atTop
      (𝓝 (Real.log (spectralRadius ℂ (complexMatrix M)).toReal)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_bound_by_row hM q hreach
  have hu := norm_log_tendsto hM hrows
  have hl : Tendsto (fun n : ℕ => Real.log ‖complexMatrix M ^ n‖ / (n : ℝ) -
      Real.log C / (n : ℝ)) atTop
      (𝓝 (Real.log (spectralRadius ℂ (complexMatrix M)).toReal)) := by
    simpa using hu.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log C))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hr := rowSum_pos hM hrows n q
    have hp := hr.trans_le (rowSum_le_norm hM n q)
    have hb := Real.log_le_log hp (hbound n)
    rw [Real.log_mul hC.ne' hr.ne'] at hb
    have hb' : Real.log ‖complexMatrix M ^ n‖ - Real.log C ≤ Real.log (rowSum M n q) := by
      linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hb' hnpos.le
  · refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (rowSum_pos hM hrows n q) (rowSum_le_norm hM n q)) hnpos.le

omit [Nonempty Q] in
theorem rowSum_one_pos_of_cycle {M : Matrix Q Q ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (q : Q) (hcycle : ∃ k > 0, 0 < (M ^ k) q q) : 0 < rowSum M 1 q := by
  obtain ⟨k, hk, hentry⟩ := hcycle
  have hr : 0 < rowSum M k q := hentry.trans_le
    (Finset.single_le_sum (fun j _ => Matrix.pow_apply_nonneg hM k q j) (Finset.mem_univ q))
  have hu := rowSum_add_upper hM 1 (k - 1) q
  rw [show 1 + (k - 1) = k by omega] at hu
  by_contra! h
  rw [le_antisymm h (rowSum_nonneg hM 1 q), zero_mul] at hu
  exact (not_lt_of_ge hu) hr

/-- General finite irreducible nonnegative matrices, including periodic ones. -/
theorem rowSum_log_tendsto_of_irreducible {M : Matrix Q Q ℝ}
    (hM : Matrix.IsIrreducible M) (q : Q) :
    Tendsto (fun n : ℕ => Real.log (rowSum M n q) / (n : ℝ)) atTop
      (𝓝 (Real.log (spectralRadius ℂ (complexMatrix M)).toReal)) := by
  have hpaths := (Matrix.isIrreducible_iff_exists_pow_pos hM.nonneg).mp hM
  apply rowSum_log_tendsto hM.nonneg
  · intro i
    exact rowSum_one_pos_of_cycle hM.nonneg i (hpaths i i)
  · intro j
    obtain ⟨k, _, hk⟩ := hpaths q j
    exact ⟨k, hk⟩

/-- The free energy per letter converges to -log ρ / β. -/
theorem freeEnergy_row_tendsto {M : Matrix Q Q ℝ}
    (hM : Matrix.IsIrreducible M) (q : Q) (β : ℝ) :
    Tendsto (fun n : ℕ => (-Real.log (rowSum M n q) / β) / (n : ℝ)) atTop
      (𝓝 (-Real.log (spectralRadius ℂ (complexMatrix M)).toReal / β)) := by
  have h := (rowSum_log_tendsto_of_irreducible hM q).mul_const (-1 / β)
  convert h using 1
  · funext n
    ring
  · congr 1
    ring

end LinearInputCurveWordSpectral
