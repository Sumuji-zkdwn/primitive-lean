
/-!
# Certified iteration of the actual Hilbert shear step

This file supplies the actual stability-and-defect recurrence that was left as
an explicit premise in IterationBound. The result applies to any bounded Q and
globally nonexpansive G on a real Hilbert space. Uniformity as spatial cutoffs
grow is a separate question: the displayed bound retains ||Q|| explicitly.
-/

namespace KerrKoopman.HilbertIteration

noncomputable section

open HilbertShear HilbertFlow HilbertError
open scoped NNReal Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The actual split iterates satisfy the geometric error recurrence. -/
theorem actual_error_recurrence (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (hG0 : G 0 = 0)
    (h : ℝ) (hh : 0 ≤ h) (z : State V) (k : ℕ) :
    ‖(lieStep Q G h)^[k + 1] z - flow Q G hG ((k + 1 : ℕ) * h) z‖ ≤
      Real.exp (‖Q‖ * h) *
        ‖(lieStep Q G h)^[k] z - flow Q G hG ((k : ℝ) * h) z‖ +
      ((3 / 2 : ℝ) * ‖Q‖ ^ 2 * h ^ 2 * ‖z‖) *
        Real.exp (((k + 1 : ℕ) : ℝ) * ‖Q‖ * h) := by
  let v := flow Q G hG ((k : ℝ) * h) z
  have hk : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
  have hlocal := lieStep_flow_error_le Q G hG h hh v
  have hfield : ‖field Q G v‖ ≤ ‖Q‖ * (Real.exp (‖Q‖ * ((k : ℝ) * h)) * ‖z‖) :=
    (field_norm_le Q G hG hG0 v).trans
      (mul_le_mul_of_nonneg_left (flow_norm_le Q G hG hG0 _ hk z) (norm_nonneg _))
  have hlocal' : ‖lieStep Q G h v - flow Q G hG h v‖ ≤
      ((3 / 2 : ℝ) * ‖Q‖ ^ 2 * h ^ 2 * ‖z‖) *
        Real.exp (((k + 1 : ℕ) : ℝ) * ‖Q‖ * h) := by
    calc
      _ ≤ (3 / 2 : ℝ) * ‖Q‖ * h ^ 2 * Real.exp (‖Q‖ * h) * ‖field Q G v‖ := hlocal
      _ ≤ (3 / 2 : ℝ) * ‖Q‖ * h ^ 2 * Real.exp (‖Q‖ * h) *
          (‖Q‖ * (Real.exp (‖Q‖ * ((k : ℝ) * h)) * ‖z‖)) := by gcongr
      _ = _ := by
        rw [show (((k + 1 : ℕ) : ℝ) * ‖Q‖ * h) =
          ‖Q‖ * h + ‖Q‖ * ((k : ℝ) * h) by push_cast; ring, Real.exp_add]
        ring
  have hs := lieStep_norm_sub_le Q G hG h ((lieStep Q G h)^[k] z) v
  rw [abs_of_nonneg hh] at hs
  have hf : flow Q G hG (((k + 1 : ℕ) : ℝ) * h) z = flow Q G hG h v := by
    rw [show (((k + 1 : ℕ) : ℝ) * h) = h + (k : ℝ) * h by push_cast; ring]
    exact flow_add Q G hG h ((k : ℝ) * h) z
  rw [Function.iterate_succ_apply', hf]
  have ht := dist_triangle (lieStep Q G h ((lieStep Q G h)^[k] z))
    (lieStep Q G h v) (flow Q G hG h v)
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add hs hlocal')

/-- Explicit physical-time error bound for n actual steps of size h. -/
theorem iterate_error_le (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (hG0 : G 0 = 0)
    (h : ℝ) (hh : 0 ≤ h) (z : State V) (n : ℕ) :
    ‖(lieStep Q G h)^[n] z - flow Q G hG ((n : ℝ) * h) z‖ ≤
      (n : ℝ) * ((3 / 2 : ℝ) * ‖Q‖ ^ 2 * h ^ 2 * ‖z‖) *
        Real.exp ((n : ℝ) * ‖Q‖ * h) := by
  apply IterationBound.exponential_recurrence_bound ‖Q‖ h
    ((3 / 2 : ℝ) * ‖Q‖ ^ 2 * h ^ 2 * ‖z‖)
    (fun k => ‖(lieStep Q G h)^[k] z - flow Q G hG ((k : ℝ) * h) z‖)
  · simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, flow_zero,
      sub_self, norm_zero]
  · exact actual_error_recurrence Q G hG hG0 h hh z

/-- A fully instantiated O(1/n) estimate against the actual global solution. -/
theorem finite_time_error_le (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (hG0 : G 0 = 0)
    (T : ℝ) (hT : 0 ≤ T) (z : State V) (n : ℕ) (hn : 0 < n) :
    ‖(lieStep Q G (T / n))^[n] z - flow Q G hG T z‖ ≤
      ((3 / 2 : ℝ) * ‖Q‖ ^ 2 * T ^ 2 * ‖z‖ / n) * Real.exp (‖Q‖ * T) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnh : (n : ℝ) * (T / n) = T := by field_simp
  have hb := IterationBound.finite_time_error_bound ‖Q‖ T ‖z‖ n hn
    (fun k => ‖(lieStep Q G (T / n))^[k] z - flow Q G hG ((k : ℝ) * (T / n)) z‖)
    (by simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul,
      flow_zero, sub_self, norm_zero])
    (actual_error_recurrence Q G hG hG0 (T / n) (div_nonneg hT (Nat.cast_nonneg _)) z)
  simpa only [hnh] using hb

/-- The repeated explicit steps converge to the actual physical-time flow for
each fixed bounded spatial operator. -/
theorem iterate_tendsto_flow (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (hG0 : G 0 = 0)
    (T : ℝ) (hT : 0 ≤ T) (z : State V) :
    Filter.Tendsto (fun n : ℕ => (lieStep Q G (T / n))^[n] z)
      Filter.atTop (𝓝 (flow Q G hG T z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    exact finite_time_error_le Q G hG hG0 T hT z n hn
  · simpa only [zero_mul] using
      (tendsto_const_div_atTop_nhds_zero_nat
        ((3 / 2 : ℝ) * ‖Q‖ ^ 2 * T ^ 2 * ‖z‖)).mul_const (Real.exp (‖Q‖ * T))

/-- A scalar bound suitable for using evaluated field norms at the computed
states. The nonnegative sequence m need not come from an exact trajectory. -/
theorem evaluated_recurrence_bound (a b : ℝ) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (m err : ℕ → ℝ) (hm : ∀ k, 0 ≤ m k) (hzero : err 0 = 0)
    (hstep : ∀ k, err (k + 1) ≤ a * err k + b * a * m k) (n : ℕ) :
    err n ≤ b * a ^ n * ∑ k ∈ Finset.range n, m k := by
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    have hmstep : b * a * m n ≤ b * a ^ (n + 1) * m n := by
      have hp : 1 ≤ a ^ n := one_le_pow₀ ha
      calc
        _ = (b * a * m n) * 1 := by ring
        _ ≤ (b * a * m n) * a ^ n :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hb ha0) (hm n))
        _ = _ := by rw [pow_succ]; ring
    calc
      err (n + 1) ≤ a * err n + b * a * m n := hstep n
      _ ≤ a * (b * a ^ n * ∑ k ∈ Finset.range n, m k) +
          b * a ^ (n + 1) * m n :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha0) hmstep
      _ = _ := by rw [Finset.sum_range_succ, pow_succ]; ring

/-- The actual finite error also admits a certificate using only field norms
at the computed split states, without G(0)=0. -/
theorem evaluated_iterate_error_le (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (h : ℝ) (hh : 0 ≤ h) (z : State V) (n : ℕ) :
    ‖(lieStep Q G h)^[n] z - flow Q G hG ((n : ℝ) * h) z‖ ≤
      ((3 / 2 : ℝ) * ‖Q‖ * h ^ 2) * Real.exp ((n : ℝ) * ‖Q‖ * h) *
        ∑ k ∈ Finset.range n, ‖field Q G ((lieStep Q G h)^[k] z)‖ := by
  let m : ℕ → ℝ := fun k => ‖field Q G ((lieStep Q G h)^[k] z)‖
  let err : ℕ → ℝ := fun k =>
    ‖(lieStep Q G h)^[k] z - flow Q G hG ((k : ℝ) * h) z‖
  have hzero : err 0 = 0 := by simp [err, flow_zero]
  have hstep (k : ℕ) : err (k + 1) ≤ Real.exp (‖Q‖ * h) * err k +
      ((3 / 2 : ℝ) * ‖Q‖ * h ^ 2) * Real.exp (‖Q‖ * h) * m k := by
    let y := (lieStep Q G h)^[k] z
    let v := flow Q G hG ((k : ℝ) * h) z
    have hf : flow Q G hG (((k + 1 : ℕ) : ℝ) * h) z = flow Q G hG h v := by
      rw [show (((k + 1 : ℕ) : ℝ) * h) = h + (k : ℝ) * h by push_cast; ring]
      exact flow_add Q G hG h ((k : ℝ) * h) z
    have hlocal := lieStep_flow_error_le Q G hG h hh y
    have hstable := flow_norm_sub_le Q G hG h hh y v
    have ht := dist_triangle (lieStep Q G h y) (flow Q G hG h y) (flow Q G hG h v)
    simp only [dist_eq_norm] at ht
    change ‖(lieStep Q G h)^[k + 1] z - flow Q G hG (((k + 1 : ℕ) : ℝ) * h) z‖ ≤ _
    rw [Function.iterate_succ_apply', hf]
    exact ht.trans (by linarith)
  have hb := evaluated_recurrence_bound (Real.exp (‖Q‖ * h))
    ((3 / 2 : ℝ) * ‖Q‖ * h ^ 2)
    (Real.one_le_exp_iff.mpr (mul_nonneg (norm_nonneg _) hh)) (by positivity)
    m err (fun _ => norm_nonneg _) hzero hstep n
  have hpow : Real.exp (‖Q‖ * h) ^ n = Real.exp ((n : ℝ) * ‖Q‖ * h) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [hpow] using hb

end

end KerrKoopman.HilbertIteration
