
/-!
# Initial-data stopping arithmetic

This module proves one-sided Gronwall, scalar analytic-tail composition, and
finite choices of the spatial cutoff and time-step count. The physical
analytic-class construction and its Fourier estimates are documented in
`docs/INITIAL_CERTIFICATE_ANALYSIS.md`; they are not silently assumed to have
been formalized here. In particular the differential inequality, analytic
tail bounds, and the splitting error supplied by an application remain explicit.
-/

namespace KerrKoopman.StoppingCertificate

open Set

/-- The analytic-class norm bound controls the initial relative energy. -/
theorem initial_energy_budget (h d : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hclass : h + d ≤ 3 / 20) : (2 * d ^ 2 + h ^ 2) / 2 ≤ 9 / 400 := by
  have hsum : (h + d) ^ 2 ≤ (3 / 20 : ℝ) ^ 2 := by
    nlinarith
  nlinarith [mul_nonneg hh hd, sq_nonneg h]

/-- The same class bounds the initial fluctuation norm by 11/50. -/
theorem initial_fluctuation_budget (h d r : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hr : 0 ≤ r) (hclass : h + d ≤ 3 / 20)
    (hr2 : r ^ 2 ≤ 2 * d ^ 2 + h ^ 2) : r ≤ 11 / 50 := by
  have hb := initial_energy_budget h d hh hd hclass
  nlinarith

/-- A constant source can be enclosed by the simpler exponential envelope. -/
theorem gronwall_four_le_envelope (δ η t : ℝ) (hη : 0 ≤ η) :
    gronwallBound δ 4 η t ≤ Real.exp (4 * t) * (δ + t * η) := by
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-4 * t))
    (Real.exp_nonneg (4 * t))
  have hi : Real.exp (-4 * t) * Real.exp (4 * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hi] at he
  have hm := mul_le_mul_of_nonneg_right he hη
  rw [gronwallBound_of_K_ne_0 (by norm_num : (4 : ℝ) ≠ 0)]
  nlinarith

/-- One-sided (not absolute-derivative) differential control is enough. -/
theorem relative_energy_envelope (R R' : ℝ → ℝ) (δ η T t : ℝ)
    (hη : 0 ≤ η) (hc : ContinuousOn R (Icc 0 T))
    (hd : ∀ s ∈ Ico 0 T, HasDerivAt R (R' s) s)
    (hzero : R 0 ≤ δ) (hineq : ∀ s ∈ Ico 0 T, R' s ≤ 4 * R s + η)
    (ht : t ∈ Icc 0 T) :
    R t ≤ Real.exp (4 * t) * (δ + t * η) := by
  have hg := le_gronwallBound_of_liminf_deriv_right_le hc
    (fun s hs _ hr => (hd s hs).hasDerivWithinAt.liminf_right_slope_le hr)
    hzero hineq t ht
  simp only [sub_zero] at hg
  exact hg.trans (gronwall_four_le_envelope δ η t hη)

/-- Two Fourier-tail envelopes give the relative-energy source constant. -/
theorem tail_source_budget (q a b : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haq : a ≤ 2 * q) (hbq : b ≤ q ^ 2 / 5) :
    a ^ 2 / 2 + a * b ≤ (12 / 5 : ℝ) * q ^ 2 := by
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hbq' : b ≤ q / 5 := by linarith
  have haa := mul_le_mul haq haq ha (by positivity : 0 ≤ 2 * q)
  have hab := mul_le_mul haq hbq' hb (by positivity : 0 ≤ 2 * q)
  nlinarith

/-- A deliberately rational upper bound avoids requiring numerical exp evaluation. -/
theorem exp_four_lt_58 : Real.exp 4 < 58 := by
  have he : Real.exp 1 < (11 / 4 : ℝ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hp : Real.exp 1 ^ 4 < (11 / 4 : ℝ) ^ 4 := by
    exact pow_lt_pow_left₀ he (Real.exp_nonneg 1) (by norm_num)
  have hid : Real.exp 1 ^ 4 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hid] at hp
  norm_num at hp ⊢
  linarith

/-- The entire certified analytic class has restored spatial amplitude <=17. -/
theorem spatial_amplitude_budget (t q R : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq : 0 ≤ q)
    (hR : R ≤ Real.exp (4 * t) * ((9 / 400 : ℝ) + t * (12 / 5)) * q ^ 2) :
    Real.sqrt (2 * R) ≤ 17 * q := by
  have he : Real.exp (4 * t) ≤ 58 :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_four_lt_58.le
  have hcoeff : 0 ≤ (9 / 400 : ℝ) + t * (12 / 5) := by positivity
  have hcoef : (9 / 400 : ℝ) + t * (12 / 5) ≤ 969 / 400 := by linarith
  have hprod := mul_le_mul he hcoef hcoeff (by norm_num : (0 : ℝ) ≤ 58)
  have hmul := mul_le_mul_of_nonneg_right hprod (sq_nonneg q)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg q]

/-- Compose differential control, initial tails, and restored-field coercivity. -/
theorem restored_spatial_from_differential_control (R R' : ℝ → ℝ)
    (q T t : ℝ) (hq : 0 ≤ q) (hT : T ≤ 1)
    (hc : ContinuousOn R (Icc 0 T))
    (hd : ∀ s ∈ Ico 0 T, HasDerivAt R (R' s) s)
    (hzero : R 0 ≤ (9 / 400 : ℝ) * q ^ 2)
    (hineq : ∀ s ∈ Ico 0 T, R' s ≤ 4 * R s + (12 / 5 : ℝ) * q ^ 2)
    (ht : t ∈ Icc 0 T) : Real.sqrt (2 * R t) ≤ 17 * q := by
  apply spatial_amplitude_budget t q (R t) ht.1 (ht.2.trans hT) hq
  have he := relative_energy_envelope R R'
    ((9 / 400 : ℝ) * q ^ 2) ((12 / 5 : ℝ) * q ^ 2) T t
    (by positivity) hc hd hzero hineq ht
  convert he using 1
  ring

/-- A common initial-independent exponential spatial tail. -/
noncomputable def spatialTail (N : ℕ) : ℝ :=
  17 * Real.exp (-(3 / 20 : ℝ) * ((N : ℝ) + 1))

/-- The cutoff depends only on the requested accuracy. -/
noncomputable def spatialCutoff (ε : ℝ) : ℕ :=
  Nat.ceil ((20 / 3 : ℝ) * Real.log (34 / ε))

/-- A directly checkable exponential threshold controls the spatial tail. -/
theorem spatial_tail_of_threshold (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hexp : 34 / ε ≤ Real.exp ((3 / 20 : ℝ) * ((N : ℝ) + 1))) :
    spatialTail N ≤ ε / 2 := by
  have hmul := (div_le_iff₀ hε).mp hexp
  have hi : Real.exp (-(3 / 20 : ℝ) * ((N : ℝ) + 1)) *
      Real.exp ((3 / 20 : ℝ) * ((N : ℝ) + 1)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have h := mul_le_mul_of_nonneg_left hmul
    (Real.exp_nonneg (-(3 / 20 : ℝ) * ((N : ℝ) + 1)))
  unfold spatialTail
  nlinarith [hi]

/-- The cutoff above assigns at most half the error budget to spatial truncation. -/
theorem spatialCutoff_spec (ε : ℝ) (hε : 0 < ε) :
    spatialTail (spatialCutoff ε) ≤ ε / 2 := by
  have hn := Nat.le_ceil ((20 / 3 : ℝ) * Real.log (34 / ε))
  change (20 / 3 : ℝ) * Real.log (34 / ε) ≤ (spatialCutoff ε : ℝ) at hn
  have hlog : Real.log (34 / ε) ≤
      (3 / 20 : ℝ) * ((spatialCutoff ε : ℝ) + 1) := by linarith
  have hexp := (Real.log_le_iff_le_exp (by positivity : 0 < (34 : ℝ) / ε)).mp hlog
  exact spatial_tail_of_threshold _ ε hε hexp

/-- Integer powers of two bound exp from below without numerical rounding. -/
theorem pow_two_le_exp_nat (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp (m : ℝ) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hp : (2 : ℝ) ^ m ≤ Real.exp 1 ^ m := by gcongr
  have hi : Real.exp 1 ^ m = Real.exp (m : ℝ) := by
    rw [← Real.exp_nat_mul]
    simp
  rwa [hi] at hp

/-- Integer powers of three bound exp from above without numerical rounding. -/
theorem exp_nat_le_pow_three (m : ℕ) : Real.exp (m : ℝ) ≤ (3 : ℝ) ^ m := by
  have he : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
  have hp : Real.exp 1 ^ m ≤ (3 : ℝ) ^ m := by gcongr
  have hi : Real.exp 1 ^ m = Real.exp (m : ℝ) := by
    rw [← Real.exp_nat_mul]
    simp
  rwa [hi] at hp

/-- Rational and integer comparisons alone certify a spatial cutoff. -/
theorem rational_spatial_budget (N m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hm : 34 / ε ≤ (2 : ℝ) ^ m)
    (hN : (20 / 3 : ℝ) * m ≤ (N : ℝ) + 1) :
    spatialTail N ≤ ε / 2 := by
  apply spatial_tail_of_threshold N ε hε
  exact (hm.trans (pow_two_le_exp_nat m)).trans
    (Real.exp_le_exp.mpr (by nlinarith))

/-- Rational and integer comparisons alone certify a splitting step count. -/
theorem rational_time_budget (N n J : ℕ) (T ε : ℝ) (hε : 0 < ε)
    (hn : 0 < n) (hJ : (N : ℝ) * T ≤ J)
    (hcount : ((33 / 50 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 * (3 : ℝ) ^ J) / ε ≤ n) :
    ((33 / 100 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 * Real.exp ((N : ℝ) * T)) /
      (n : ℝ) ≤ ε / 2 := by
  have he := (Real.exp_le_exp.mpr hJ).trans (exp_nat_le_pow_three J)
  have he' := mul_le_mul_of_nonneg_left he
    (by positivity : 0 ≤ (33 / 50 : ℝ) * (N : ℝ) ^ 2 * T ^ 2)
  have hb := (div_le_iff₀ hε).mp hcount
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  apply (div_le_iff₀ hn').mpr
  nlinarith

/-- Twice the uniform splitting numerator divided by the target accuracy. -/
noncomputable def timeSteps (N : ℕ) (T ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (((33 / 50 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 *
    Real.exp ((N : ℝ) * T)) / ε))

theorem timeSteps_pos (N : ℕ) (T ε : ℝ) : 0 < timeSteps N T ε := by
  unfold timeSteps
  exact lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) (le_max_left _ _)

/-- The time-step count assigns the other half of the budget to splitting. -/
theorem timeSteps_spec (N : ℕ) (T ε : ℝ) (hε : 0 < ε) :
    ((33 / 100 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 * Real.exp ((N : ℝ) * T)) /
      (timeSteps N T ε : ℝ) ≤ ε / 2 := by
  have hn : 0 < (timeSteps N T ε : ℝ) := by
    exact_mod_cast timeSteps_pos N T ε
  have hceil := Nat.le_ceil (((33 / 50 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 *
    Real.exp ((N : ℝ) * T)) / ε)
  have hmax : (Nat.ceil (((33 / 50 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 *
      Real.exp ((N : ℝ) * T)) / ε) : ℝ) ≤ (timeSteps N T ε : ℝ) := by
    exact Nat.cast_le.mpr (le_max_right 1 _)
  have hb := (div_le_iff₀ hε).mp (hceil.trans hmax)
  apply (div_le_iff₀ hn).mpr
  nlinarith

/-- A genuine finite stopping conclusion; application errors remain visible. -/
theorem finite_stopping_certificate (ε T spaceErr stepErr totalErr : ℝ)
    (hε : 0 < ε)
    (hspace : spaceErr ≤ spatialTail (spatialCutoff ε))
    (hstep : stepErr ≤
      ((33 / 100 : ℝ) * (spatialCutoff ε : ℝ) ^ 2 * T ^ 2 *
        Real.exp ((spatialCutoff ε : ℝ) * T)) /
        (timeSteps (spatialCutoff ε) T ε : ℝ))
    (htotal : totalErr ≤ spaceErr + stepErr) : totalErr ≤ ε := by
  have hs := spatialCutoff_spec ε hε
  have ht := timeSteps_spec (spatialCutoff ε) T ε hε
  linarith

/-- The executable integer/rational rule has the same total-error guarantee. -/
theorem rational_finite_stopping_certificate (N n m J : ℕ)
    (ε T spaceErr stepErr totalErr : ℝ) (hε : 0 < ε) (hn : 0 < n)
    (hm : 34 / ε ≤ (2 : ℝ) ^ m)
    (hN : (20 / 3 : ℝ) * m ≤ (N : ℝ) + 1)
    (hJ : (N : ℝ) * T ≤ J)
    (hcount : ((33 / 50 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 * (3 : ℝ) ^ J) / ε ≤ n)
    (hspace : spaceErr ≤ spatialTail N)
    (hstep : stepErr ≤
      ((33 / 100 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 * Real.exp ((N : ℝ) * T)) / n)
    (htotal : totalErr ≤ spaceErr + stepErr) : totalErr ≤ ε := by
  have hs := rational_spatial_budget N m ε hε hm hN
  have ht := rational_time_budget N n J T ε hε hn hJ hcount
  linarith

end KerrKoopman.StoppingCertificate
