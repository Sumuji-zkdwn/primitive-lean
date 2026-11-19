/-! A seven-step return with reversed tangent, in the arc model of PR #159. -/

namespace RobotSix

open LinearInputCurveWordAlgebra LinearInputCurveWordArc LinearInputRobotWalkArc
open LinearInputCurveWordFinite (allWords mem_allWords)

noncomputable abbrev stepAngle : ℝ := 2 * Real.pi / ((6 : ℕ) : ℝ)

def witness : List Bool := [false, true, true, true, true, true, false]

def mirror : List Bool := witness.map Bool.not

theorem witness_trace :
    witness.length = 7 ∧
    edges 0 witness = [-1, -1, 0, 1, 2, 3, 3] ∧
    edgeResidues 6 0 witness = [5, 5, 0, 1, 2, 3, 3] ∧
    turns witness = 3 := by decide

/-- Coefficients in the basis (1, z) after reduction modulo Φ₆. -/
def coefficients (w : List Bool) : ℤ × ℤ :=
  let c := fun i : ℕ => ((edgeResidues 6 0 w).count i : ℤ)
  (c 0 - c 2 - c 3 + c 5, c 1 + c 2 - c 4 - c 5)

private theorem reduce_six_powers {z : ℂ} (hz : z ^ 2 - z + 1 = 0) (c : ℕ → ℕ) :
    (∑ i ∈ Finset.range 6, (c i : ℂ) * z ^ i) =
      ((c 0 : ℂ) - c 2 - c 3 + c 5) + ((c 1 : ℂ) + c 2 - c 4 - c 5) * z := by
  have h2 : z ^ 2 = z - 1 := by linear_combination hz
  have h3 : z ^ 3 = -1 := by linear_combination (z + 1) * hz
  have h4 : z ^ 4 = -z := by linear_combination (z ^ 2 + z) * hz
  have h5 : z ^ 5 = 1 - z := by linear_combination (z ^ 3 + z ^ 2 - 1) * hz
  simp [Finset.sum_range_succ, h2, h3, h4, h5]
  ring

/-- The integer pair evaluates to the original integrated endpoint after multiplication
by the first chord. This holds for words of every length. -/
theorem endpoint_formula {h : ℝ} (hh : 0 < h) (w : List Bool) :
    endpoint (arcWord h stepAngle w) =
      endpoint (arcState h stepAngle) *
        (((coefficients w).1 : ℂ) + ((coefficients w).2 : ℂ) * rotation stepAngle) := by
  let z := rotation stepAngle
  have hp : IsPrimitiveRoot z 6 := step_root_primitive 6 (by decide)
  have hz : z ^ 2 - z + 1 = 0 := by
    have hr := (Polynomial.isRoot_cyclotomic_iff_charZero (R := ℂ) (by decide : 0 < 6)).mpr hp
    simpa [Polynomial.IsRoot.def] using hr
  rw [stepAngle, endpoint_eq_residue_counts 6 (by decide) hh w]
  congr 1
  simpa [coefficients, z, stepAngle] using
    reduce_six_powers hz (fun i => (edgeResidues 6 0 w).count i)

private theorem eval_pair_zero_iff (a b : ℤ) :
    (a : ℂ) + (b : ℂ) * rotation stepAngle = 0 ↔ (a, b) = (0, 0) := by
  have hi : (rotation stepAngle).im ≠ 0 := by
    rw [rotation, Complex.exp_ofReal_mul_I_im]
    apply ne_of_gt
    exact Real.sin_pos_of_pos_of_lt_pi (by dsimp [stepAngle]; positivity)
      (by dsimp [stepAngle]; linarith [Real.pi_pos])
  constructor
  · intro he
    have him := congrArg Complex.im he
    have hbR : (b : ℝ) * (rotation stepAngle).im = 0 := by
      simpa [Complex.mul_im] using him
    have hb : b = 0 := by exact_mod_cast (mul_eq_zero.mp hbR).resolve_right hi
    subst b
    have ha : a = 0 := by simpa using he
    simp [ha]
  · rintro hpair
    cases hpair
    simp

theorem endpoint_zero_iff {h : ℝ} (hh : 0 < h) (w : List Bool) :
    endpoint (arcWord h stepAngle w) = 0 ↔ coefficients w = (0, 0) := by
  have hc : endpoint (arcState h stepAngle) ≠ 0 := chord_ne_zero hh (by decide : 1 < 6)
  rw [endpoint_formula hh, mul_eq_zero, or_iff_right hc]
  exact eval_pair_zero_iff _ _

/-- The rotation of the actual tangent is 1 exactly at multiples of the order. -/
theorem facing_iff_dvd {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 < h) (w : List Bool) :
    rotation (angle (arcWord h (2 * Real.pi / N) w)) = 1 ↔ (N : ℤ) ∣ turns w := by
  rw [angle_arcWord hh (by positivity), rotation_int_mul]
  exact (step_root_primitive N hN).zpow_eq_one_iff_dvd _

/-- A repeated count profile suffices at composite orders too. No primality is used. -/
theorem facing_of_periodic_counts {q d : ℕ} (hq : 2 ≤ q) (hd : 0 < d) {h : ℝ}
    (hh : 0 < h) (w : List Bool)
    (hp : ∀ i < q * d, (edgeResidues (q * d) 0 w).count i =
      (edgeResidues (q * d) 0 w).count (i % d)) :
    rotation (angle (arcWord h (2 * Real.pi / (q * d : ℕ)) w)) = 1 := by
  have hN : 0 < q * d := Nat.mul_pos (by omega) hd
  have hr := LinearInputRobotWalkLengths.heading_closed_of_periodic hd hq w hp
  apply (facing_iff_dvd hN hh w).mpr
  apply Int.dvd_of_emod_eq_zero
  have hn : (0 : ℤ) < (q * d : ℕ) := by exact_mod_cast hN
  have hnonneg := Int.emod_nonneg (turns w) hn.ne'
  omega

theorem witness_closes_reversed {h : ℝ} (hh : 0 < h) :
    endpoint (arcWord h stepAngle witness) = 0 ∧
    angle (arcWord h stepAngle witness) = Real.pi ∧
    rotation (angle (arcWord h stepAngle witness)) = -1 ∧
    rotation (angle (arcWord h stepAngle witness)) ≠ 1 := by
  have hc := (endpoint_zero_iff hh witness).mpr (by decide)
  have ha : angle (arcWord h stepAngle witness) = Real.pi := by
    rw [angle_arcWord hh (by dsimp [stepAngle]; positivity), witness_trace.2.2.2]
    dsimp [stepAngle]
    push_cast
    ring
  refine ⟨hc, ha, ?_, ?_⟩
  · rw [ha]
    exact Complex.exp_pi_mul_I
  · rw [ha, rotation, Complex.exp_pi_mul_I]
    norm_num

/-- Enumerate using PR #159's previously verified Boolean-word generator. -/
def shortReturns : List (List Bool) :=
  ((List.range 8).flatMap allWords).filter (fun w => decide (coefficients w = (0, 0)))

theorem mem_shortReturns {h : ℝ} (hh : 0 < h) (w : List Bool) :
    w ∈ shortReturns ↔ w.length < 8 ∧ endpoint (arcWord h stepAngle w) = 0 := by
  simp [shortReturns, List.mem_flatMap, mem_allWords, endpoint_zero_iff hh]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem short_returns_exact :
    shortReturns = [List.nil, List.replicate 6 true, List.replicate 6 false, mirror, witness] := by
  decide

/-- The two named words exhaust the failures at lengths zero through seven. -/
theorem short_counterexamples_iff {h : ℝ} (hh : 0 < h) (w : List Bool) (hw : w.length ≤ 7) :
    (endpoint (arcWord h stepAngle w) = 0 ∧ rotation (angle (arcWord h stepAngle w)) ≠ 1) ↔
      w = mirror ∨ w = witness := by
  have hmem : w ∈ shortReturns ↔ endpoint (arcWord h stepAngle w) = 0 := by
    rw [mem_shortReturns hh, and_iff_right (show w.length < 8 by omega)]
  have hfilter : shortReturns.filter (fun u => decide (¬ (6 : ℤ) ∣ turns u)) =
      [mirror, witness] := by rw [short_returns_exact]; decide
  have hface : rotation (angle (arcWord h stepAngle w)) = 1 ↔ (6 : ℤ) ∣ turns w :=
    facing_iff_dvd (N := 6) (by decide) hh w
  simp only [← hmem, ne_eq, hface]
  calc
    _ ↔ w ∈ shortReturns.filter (fun u => decide (¬ (6 : ℤ) ∣ turns u)) := by simp
    _ ↔ _ := by rw [hfilter]; simp

theorem least_counterexample_length {h : ℝ} (hh : 0 < h) :
    IsLeast {n : ℕ | ∃ w : List Bool, w.length = n ∧
      endpoint (arcWord h stepAngle w) = 0 ∧ rotation (angle (arcWord h stepAngle w)) ≠ 1} 7 := by
  refine ⟨⟨witness, rfl, (witness_closes_reversed hh).1, (witness_closes_reversed hh).2.2.2⟩, ?_⟩
  rintro n ⟨w, rfl, hc, hf⟩
  by_contra! hshort
  rcases (short_counterexamples_iff hh w (by omega)).mp ⟨hc, hf⟩ with rfl | rfl <;>
    simp [mirror, witness] at hshort

end RobotSix
