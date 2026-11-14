/-! Polynomial truncations connect the standard scalar logarithmic series
to the noncommutative coefficientwise exponential inverse. -/

noncomputable section
namespace LinearInputCurveWordLogFormula

open LinearInputCurveWordFormalSeries LinearInputCurveWordFriedrichs
open LinearInputCurveWordScalarLog LinearInputCurveWordCoproduct

theorem tensor_sum_apply {ι κ : Type*} (s : Finset κ) (P : κ → TensorSeries ι)
    (w : List ι) : (∑ k ∈ s, P k) w = ∑ k ∈ s, P k w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    change P k w + (∑ k ∈ s, P k) w = P k w + ∑ k ∈ s, P k w
    rw [ih]

theorem tensor_smul_apply {ι : Type*} (r : ℝ) (P : TensorSeries ι) (w : List ι) :
    (r • P) w = r * P w := rfl

theorem power_eq_tensorPow {ι : Type*} (A : TensorSeries ι) (n : ℕ) :
    power A n = (A ^ n : TensorSeries ι) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change product A (power A n) = _
    rw [ih, pow_succ']; rfl

/-- Evaluation of any polynomial at a positive-order word series only needs
its coefficients through the degree of the queried word. -/
theorem aeval_coefficient {ι : Type*} (A : TensorSeries ι) (hA : A [] = 0)
    (p : Polynomial ℝ) (w : List ι) :
    (Polynomial.aeval A p) w =
      ∑ k ∈ Finset.range (w.length + 1), p.coeff k * power A k w := by
  let N := max (p.natDegree + 1) (w.length + 1)
  have hN : p.natDegree < N := by dsimp [N]; omega
  have he := congrArg (fun F : TensorSeries ι => F w)
    (Polynomial.aeval_eq_sum_range' hN A)
  rw [tensor_sum_apply] at he
  simp_rw [tensor_smul_apply, ← power_eq_tensorPow] at he
  rw [he]
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
  intro k _ hk
  have hk' : w.length < k := by simp only [Finset.mem_range] at hk; omega
  rw [power_vanishes_above_degree hA k w hk', mul_zero]

theorem aeval_congr_degree {ι : Type*} (A : TensorSeries ι) (hA : A [] = 0)
    (p q : Polynomial ℝ) (w : List ι)
    (h : ∀ k, k ≤ w.length → p.coeff k = q.coeff k) :
    (Polynomial.aeval A p) w = (Polynomial.aeval A q) w := by
  rw [aeval_coefficient A hA, aeval_coefficient A hA]
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

theorem scalar_coeff_pow_vanishes {f : PowerSeries ℝ}
    (hf : PowerSeries.constantCoeff f = 0) (n k : ℕ) (hnk : n < k) :
    PowerSeries.coeff n (f ^ k) = 0 := by
  have hx : PowerSeries.X ∣ f := PowerSeries.X_dvd_iff.mpr hf
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hx k) n hnk

theorem scalar_coeff_trunc_pow (f : PowerSeries ℝ) (N n k : ℕ) (hn : n < N) :
    PowerSeries.coeff n ((PowerSeries.trunc N f : PowerSeries ℝ) ^ k) =
      PowerSeries.coeff n (f ^ k) := by
  have h := congrArg (fun p : Polynomial ℝ => p.coeff n) (PowerSeries.trunc_trunc_pow f N k)
  simpa only [PowerSeries.coeff_trunc, ite_eq_left hn] using h

/-- Truncating both scalar series preserves every coefficient below the
cutoff when the substituted series has zero constant coefficient. -/
theorem scalar_coeff_subst_trunc (f g : PowerSeries ℝ)
    (hg : PowerSeries.constantCoeff g = 0) (N n : ℕ) (hn : n < N) :
    PowerSeries.coeff n
        ((PowerSeries.trunc N f : PowerSeries ℝ).subst
          (PowerSeries.trunc N g : PowerSeries ℝ)) =
      PowerSeries.coeff n (f.subst g) := by
  have hg' : PowerSeries.constantCoeff (PowerSeries.trunc N g : PowerSeries ℝ) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left (by omega),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hg]
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hg'),
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hg)]
  apply finsum_congr
  intro k
  rw [scalar_coeff_trunc_pow g N n k hn]
  by_cases hk : k < N
  · rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left hk]
  · rw [scalar_coeff_pow_vanishes hg n k (by omega)]
    simp

theorem coe_comp_eq_subst (p q : Polynomial ℝ) (hq : q.coeff 0 = 0) :
    ((p.comp q : Polynomial ℝ) : PowerSeries ℝ) =
      (p : PowerSeries ℝ).subst (q : PowerSeries ℝ) := by
  have hq' : PowerSeries.constantCoeff (q : PowerSeries ℝ) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
    exact hq
  rw [PowerSeries.subst_coe (PowerSeries.HasSubst.of_constantCoeff_zero' hq')]
  have h := Polynomial.aeval_algHom_apply (Polynomial.coeToPowerSeries.algHom ℝ) q p
  simpa [Polynomial.comp_eq_aeval] using h.symm

theorem aeval_trunc_exp {ι : Type*} (A : TensorSeries ι) (hA : A [] = 0)
    (N : ℕ) (w : List ι) (hw : w.length < N) :
    (Polynomial.aeval A (PowerSeries.trunc N (PowerSeries.exp ℝ))) w = formalExp A w := by
  rw [aeval_coefficient A hA]
  unfold formalExp
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < N := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hw
  rw [PowerSeries.coeff_trunc, ite_eq_left hk', coeff_exp_real]

theorem aeval_trunc_log {ι : Type*} (A : TensorSeries ι) (hA : A [] = 0)
    (N : ℕ) (w : List ι) (hw : w.length < N) :
    (Polynomial.aeval A (PowerSeries.trunc N (PowerSeries.log ℝ))) w =
      ∑ k ∈ Finset.range (w.length + 1),
        ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) * power A k w := by
  rw [aeval_coefficient A hA]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < N := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hw
  rw [PowerSeries.coeff_trunc, ite_eq_left hk', coeff_log_real]

/-- The conventional alternating-power logarithm is an actual inverse to the
explicit exponential in every word degree. -/
theorem formalExp_formalLog {ι : Type*} (F : Series ι) (hF : F [] = 1) :
    formalExp (formalLog F) = F := by
  funext w
  let A : TensorSeries ι := fun z => F z - unitSeries z
  have hA : A [] = 0 := by simp [A, hF, unitSeries]
  let N := w.length + 1
  let p : Polynomial ℝ := PowerSeries.trunc N (PowerSeries.log ℝ)
  let q : Polynomial ℝ := PowerSeries.trunc N (PowerSeries.exp ℝ)
  have hp : p.coeff 0 = 0 := by simp [p, N, PowerSeries.coeff_trunc]
  let B : TensorSeries ι := Polynomial.aeval A p
  have hB : B [] = 0 := by
    dsimp only [B]
    rw [aeval_coefficient A hA]
    simp [hp]
  have hBcoeff : ∀ z, z.length ≤ w.length → B z = formalLog F z := by
    intro z hz
    exact aeval_trunc_log A hA N z (by dsimp [N]; omega)
  have hpoly : ∀ k, k ≤ w.length → (q.comp p).coeff k = (1 + Polynomial.X : Polynomial ℝ).coeff k := by
    intro k hk
    have h := scalar_coeff_subst_trunc (PowerSeries.exp ℝ) (PowerSeries.log ℝ)
      PowerSeries.constantCoeff_log N k (by dsimp [N]; omega)
    rw [exp_subst_log] at h
    rw [← Polynomial.coeff_coe, coe_comp_eq_subst q p hp]
    simpa only [p, q, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      map_add, PowerSeries.coeff_one, PowerSeries.coeff_X, eq_comm] using h
  calc
    formalExp (formalLog F) w = formalExp B w :=
      formalExp_congr_through w.length (fun z hz => (hBcoeff z hz).symm) w le_rfl
    _ = (Polynomial.aeval B q) w := (aeval_trunc_exp B hB N w (by dsimp [N]; omega)).symm
    _ = (Polynomial.aeval A (q.comp p)) w := by rw [Polynomial.aeval_comp]
    _ = (Polynomial.aeval A (1 + Polynomial.X)) w := aeval_congr_degree A hA _ _ w hpoly
    _ = F w := by
      simp only [map_add, map_one, Polynomial.aeval_X]
      change unitSeries w + (F w - unitSeries w) = F w
      ring

/-- The constructed unique exponential inverse equals the standard logarithmic
power series, coefficient by coefficient in all degrees. -/
theorem formalLog_eq_logarithm {ι : Type*} (F : Series ι) (hF : F [] = 1) :
    formalLog F = logarithm F := by
  apply formalExp_injective (formalLog_empty F) (logarithm_empty F)
  rw [formalExp_formalLog F hF, formalExp_logarithm F hF]

theorem formalLog_formalExp {ι : Type*} (A : Series ι) (hA : A [] = 0) :
    formalLog (formalExp A) = A := by
  rw [formalLog_eq_logarithm _ (formalExp_empty A), logarithm_formalExp A hA]

theorem formalLog_primitive {ι : Type*} {F : Series ι} (hF : GroupLike F) :
    Primitive (formalLog F) := by
  rw [formalLog_eq_logarithm F hF.1]
  exact logarithm_primitive hF

/-- The usual BCH expression uses the standard alternating logarithm of
the concatenation product of the two exponential series. -/
theorem bch_eq_formalLog {ι : Type*} (A B : Series ι) :
    bch A B = formalLog (product (formalExp A) (formalExp B)) := by
  rw [formalLog_eq_logarithm _ (by rw [LinearInputCurveWordFormalSeries.product_empty,
    formalExp_empty, formalExp_empty, mul_one])]
  rfl

/-- The standard logarithmic power series of any group-like coefficient
series has homogeneous witnesses in the actual free Lie algebra. -/
theorem formalLog_completed_lie {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Series ι} (hF : GroupLike F) :
    ∃ L : ℕ → FreeLieAlgebra ℝ ι, L 0 = 0 ∧
      (∀ n, L n ∈ lieDegree ι n) ∧
      ∀ n w, lieExpansion (L n) w =
        if w.length = n then formalLog F w else 0 :=
  primitive_completed_lie_expansion (formalLog_primitive hF)

/-- In particular this applies to the actual iterated-integral signature. -/
theorem signature_formalLog_completed_lie {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ι → ℝ → ℝ} (hv : ∀ i, Continuous (v i)) (a b : ℝ) :
    ∃ L : ℕ → FreeLieAlgebra ℝ ι, L 0 = 0 ∧
      (∀ n, L n ∈ lieDegree ι n) ∧
      ∀ n w, lieExpansion (L n) w = if w.length = n then
        formalLog (LinearInputCurveWordSignature.signature v a b) w else 0 :=
  formalLog_completed_lie (signature_groupLike hv a b)

end LinearInputCurveWordLogFormula
