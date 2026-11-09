import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed physical energy and unbounded point reconstruction

The cosine-coefficient energy `sum a_k^2 / 4` is identified with the actual
mean magnetic energy by proving cosine orthogonality and the finite-sum
integral. The trigonometric profiles are proved smooth, periodic, nonconstant
for positive energy, and to have common mean and exact Kerr initial energy.
The bounded-encoder obstruction is an actual normed-space theorem, and hence
applies in particular to Hilbert encoders whenever they reconstruct these peaks.
-/

open MeasureTheory

namespace KerrKoopman.Reconstruction

noncomputable section

/-- All `n+1` positive cosine frequencies have this coefficient. -/
def amplitude (ε : ℝ) (n : ℕ) : ℝ :=
  2 * Real.sqrt (ε / ((n : ℝ) + 1))

/-- Cosine coefficient energy, connected to the physical integral below. -/
def coefficientEnergy (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ _i : Fin (n + 1), amplitude ε n ^ 2 / 4

/-- The centered magnetic trigonometric polynomial, with no zero mode. -/
def profile (ε : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), amplitude ε n * Real.cos (((i : ℝ) + 1) * x)

/-- The value at the common spatial point zero. -/
def peak (ε : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * amplitude ε n

theorem amplitude_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ amplitude ε n := by
  unfold amplitude
  positivity

theorem amplitude_sq (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    amplitude ε n ^ 2 = 4 * ε / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hs := Real.sq_sqrt (div_nonneg hε hn.le)
  unfold amplitude
  rw [mul_pow, hs]
  ring

theorem coefficientEnergy_eq (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    coefficientEnergy ε n = ε := by
  unfold coefficientEnergy
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [amplitude_sq ε hε n]
  push_cast
  field_simp

theorem profile_zero (ε : ℝ) (n : ℕ) : profile ε n 0 = peak ε n := by
  unfold profile peak
  simp [Nat.cast_add, Nat.cast_one]

theorem peak_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ peak ε n := by
  exact mul_nonneg (by positivity) (amplitude_nonneg ε n)

theorem peak_sq (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    peak ε n ^ 2 = 4 * ε * ((n : ℝ) + 1) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold peak
  rw [mul_pow, amplitude_sq ε hε n]
  field_simp

theorem peaks_unbounded (ε : ℝ) (hε : 0 < ε) (B : ℝ) :
    ∃ n : ℕ, B < peak ε n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B ^ 2 / (4 * ε))
  refine ⟨n, ?_⟩
  have hp : 0 < 4 * ε := by positivity
  have hn' : B ^ 2 < (n : ℝ) * (4 * ε) := (div_lt_iff₀ hp).mp hn
  have hs := peak_sq ε hε.le n
  have hnonneg := peak_nonneg ε n
  nlinarith

theorem no_uniform_peak_bound (ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ B : ℝ, ∀ n : ℕ, peak ε n ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := peaks_unbounded ε hε B
  exact (not_lt_of_ge (hB n)) hn

/-- No bounded family of encoded vectors admits one continuous linear decoder
which returns every fixed-energy peak. This needs no inner product. -/
theorem no_bounded_encoder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) (hε : 0 < ε) (encode : ℕ → E) (decode : E →L[ℝ] ℝ)
    (B : ℝ) (hencode : ∀ n, ‖encode n‖ ≤ B) :
    ¬ ∀ n, decode (encode n) = peak ε n := by
  intro hdecode
  obtain ⟨n, hn⟩ := peaks_unbounded ε hε (‖decode‖ * B)
  have hbound : ‖decode (encode n)‖ ≤ ‖decode‖ * B :=
    (decode.le_opNorm (encode n)).trans
      (mul_le_mul_of_nonneg_left (hencode n) (norm_nonneg decode))
  rw [hdecode n, Real.norm_of_nonneg (peak_nonneg ε n)] at hbound
  exact (not_lt_of_ge hbound) hn

theorem integral_cos_int_frequency (k : ℤ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * x)) =
      if k = 0 then 2 * Real.pi else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [if_neg hk, intervalIntegral.integral_comp_mul_left Real.cos hkR,
      integral_cos]
    have hs : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
      have heq : (k : ℝ) * (2 * Real.pi) = ((k * 2 : ℤ) : ℝ) * Real.pi := by
        push_cast
        ring
      rw [heq, Real.sin_int_mul_pi]
    simp [hs]

theorem integral_cos_positive_frequency (k : ℕ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (((k : ℝ) + 1) * x)) = 0 := by
  have h := integral_cos_int_frequency ((k : ℤ) + 1)
  have hk : (k : ℤ) + 1 ≠ 0 := by omega
  simpa [hk] using h

theorem integral_cos_pair (j k : ℕ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi),
      Real.cos (((j : ℝ) + 1) * x) * Real.cos (((k : ℝ) + 1) * x)) =
      if j = k then Real.pi else 0 := by
  have hprod (x : ℝ) :
      Real.cos (((j : ℝ) + 1) * x) * Real.cos (((k : ℝ) + 1) * x) =
        (Real.cos ((((j : ℤ) + k + 2 : ℤ) : ℝ) * x) +
          Real.cos ((((j : ℤ) - k : ℤ) : ℝ) * x)) / 2 := by
    push_cast
    rw [show ((j : ℝ) + k + 2) * x = ((j : ℝ) + 1) * x + ((k : ℝ) + 1) * x by ring]
    rw [show ((j : ℝ) - k) * x = ((j : ℝ) + 1) * x - ((k : ℝ) + 1) * x by ring]
    rw [Real.cos_add, Real.cos_sub]
    ring
  simp_rw [hprod]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [integral_cos_int_frequency, integral_cos_int_frequency]
  have hpos : (j : ℤ) + k + 2 ≠ 0 := by omega
  have hsub : ((j : ℤ) - k = 0) ↔ j = k := by omega
  simp only [hpos, if_false, hsub, zero_add]
  split_ifs <;> ring

theorem integral_cos_sum_sq (m : ℕ) (a : Fin m → ℝ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi),
      (∑ i : Fin m, a i * Real.cos (((i : ℝ) + 1) * x)) ^ 2) =
      Real.pi * ∑ i : Fin m, a i ^ 2 := by
  have hexpand (x : ℝ) :
      (∑ i : Fin m, a i * Real.cos (((i : ℝ) + 1) * x)) ^ 2 =
        ∑ i : Fin m, ∑ j : Fin m, (a i * a j) *
          (Real.cos (((i : ℝ) + 1) * x) * Real.cos (((j : ℝ) + 1) * x)) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finset_sum
    (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_finset_sum
    (fun j _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_cos_pair]
  simp [Fin.val_inj, pow_two, mul_comm]

theorem profile_integral_zero (ε : ℝ) (n : ℕ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), profile ε n x) = 0 := by
  unfold profile
  rw [intervalIntegral.integral_finset_sum
    (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_cos_positive_frequency]
  simp

theorem profile_contDiff (ε : ℝ) (n : ℕ) : ContDiff ℝ ⊤ (profile ε n) := by
  unfold profile
  fun_prop

theorem profile_periodic (ε : ℝ) (n : ℕ) :
    Function.Periodic (profile ε n) (2 * Real.pi) := by
  intro x
  unfold profile
  apply Finset.sum_congr rfl
  intro i hi
  rw [show ((i : ℝ) + 1) * (x + 2 * Real.pi) =
    ((i : ℝ) + 1) * x + (((i : ℕ) + 1 : ℕ) : ℝ) * (2 * Real.pi) by
      push_cast
      ring]
  rw [Real.cos_add_nat_mul_two_pi]

theorem magnetic_mean (ε : ℝ) (n : ℕ) (Hbar : ℝ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), Hbar + profile ε n x) /
      (2 * Real.pi) = Hbar := by
  have hc : Continuous (profile ε n) := by unfold profile; fun_prop
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (hc.intervalIntegrable _ _), profile_integral_zero]
  simp [Real.pi_ne_zero]

theorem profile_nonconstant (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    ¬ ∃ c : ℝ, ∀ x : ℝ, profile ε n x = c := by
  rintro ⟨c, hc⟩
  have hzero := profile_integral_zero ε n
  have hf : profile ε n = fun _ => c := funext hc
  rw [hf] at hzero
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hzero
  have hc0 : c = 0 := (mul_eq_zero.mp hzero).resolve_left (by positivity)
  have hpeak : peak ε n = 0 := by rw [← profile_zero, hc, hc0]
  have hs := peak_sq ε hε.le n
  rw [hpeak] at hs
  have hn : 0 < (n : ℝ) + 1 := by positivity
  nlinarith

theorem profile_integral_sq (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), profile ε n x ^ 2) =
      4 * Real.pi * ε := by
  unfold profile
  rw [integral_cos_sum_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [amplitude_sq ε hε n]
  push_cast
  field_simp

theorem centered_magnetic_mean_energy (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), profile ε n x ^ 2 / 2) / (2 * Real.pi) = ε := by
  rw [intervalIntegral.integral_div, profile_integral_sq ε hε n]
  field_simp
  ring

theorem magnetic_mean_energy (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (Hbar : ℝ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), (Hbar + profile ε n x) ^ 2 / 2) /
      (2 * Real.pi) = Hbar ^ 2 / 2 + ε := by
  have hexpand (x : ℝ) : (Hbar + profile ε n x)^2 =
      Hbar ^ 2 + 2 * Hbar * profile ε n x + profile ε n x ^ 2 := by ring
  have hc : Continuous (profile ε n) := by unfold profile; fun_prop
  rw [intervalIntegral.integral_div]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, profile_integral_zero,
    profile_integral_sq ε hε n]
  simp only [mul_zero, add_zero, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  field_simp
  ring

theorem kerr_initial_mean_energy (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (Hbar : ℝ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi),
      (Hbar + profile ε n x) ^ 2 / 2 + (1 : ℝ) / 2 + (1 : ℝ) / 4) /
      (2 * Real.pi) = Hbar ^ 2 / 2 + ε + 3 / 4 := by
  have hc : Continuous (profile ε n) := by unfold profile; fun_prop
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [add_div]
  rw [magnetic_mean_energy ε hε n Hbar]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp
  ring

/-- Directly stated for the physical magnetic value, including its fixed mean.
The waveform family above is smooth, periodic and has one common energy. -/
theorem no_bounded_magnetic_encoder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) (hε : 0 < ε) (Hbar : ℝ)
    (encode : ℕ → E) (decode : E →L[ℝ] ℝ)
    (B : ℝ) (hencode : ∀ n, ‖encode n‖ ≤ B) :
    ¬ ∀ n, decode (encode n) = Hbar + profile ε n 0 := by
  intro hdecode
  obtain ⟨n, hn⟩ := peaks_unbounded ε hε (‖decode‖ * B - Hbar)
  have hbound : ‖decode (encode n)‖ ≤ ‖decode‖ * B :=
    (decode.le_opNorm (encode n)).trans
      (mul_le_mul_of_nonneg_left (hencode n) (norm_nonneg decode))
  have hupper : decode (encode n) ≤ ‖decode‖ * B :=
    (le_abs_self (decode (encode n))).trans hbound
  rw [hdecode n, profile_zero] at hupper
  linarith

end

end KerrKoopman.Reconstruction
