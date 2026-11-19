/-!
Equal-length circular arcs with opposite signed turns.  Traversing one edge of
the heading graph in either direction contributes the same rotated chord.
Integer headings keep track of whole turns even after the position closes.
-/

noncomputable section

namespace LinearInputRobotWalkArc

open LinearInputCurveWordAlgebra LinearInputCurveWordArc
open scoped BigOperators
local notation "rot" => LinearInputCurveWordAlgebra.rotation

def arcWord (h a : ℝ) : List Bool → State
  | [] => emptyState
  | b :: w => join (arcState h (if b then a else -a)) (arcWord h a w)

def turns : List Bool → ℤ
  | [] => 0
  | true :: w => 1 + turns w
  | false :: w => -1 + turns w

def edges (j : ℤ) : List Bool → List ℤ
  | [] => []
  | true :: w => j :: edges (j + 1) w
  | false :: w => (j - 1) :: edges (j - 1) w

def edgeResidues (N : ℕ) (j : ℤ) (w : List Bool) : List ℕ :=
  (edges j w).map fun i => (i % (N : ℤ)).toNat

theorem arcWord_append (h a : ℝ) (u v : List Bool) :
    arcWord h a (u ++ v) = join (arcWord h a u) (arcWord h a v) := by
  induction u with
  | nil => simp [arcWord, empty_join]
  | cons b u ih => simp [arcWord, ih, join_assoc]

theorem turns_append (u v : List Bool) : turns (u ++ v) = turns u + turns v := by
  induction u with
  | nil => simp [turns]
  | cons b u ih => cases b <;> simp [turns, ih, add_assoc]

theorem angle_arcWord {h a : ℝ} (hh : 0 < h) (ha : a ≠ 0) (w : List Bool) :
    angle (arcWord h a w) = (turns w : ℝ) * a := by
  induction w with
  | nil => simp [arcWord, turns, angle, emptyState]
  | cons b w ih =>
    cases b <;> simp only [arcWord, join_angle, ih, turns, Bool.false_eq_true, ite_false, ite_true, arc_state_formula hh ha,
      arc_state_formula hh (neg_ne_zero.mpr ha)] <;> push_cast <;> unfold angle <;> ring

theorem rotation_int_mul (j : ℤ) (a : ℝ) :
    rot ((j : ℝ) * a) = rot a ^ j := by
  simp only [LinearInputCurveWordAlgebra.rotation, Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc, Complex.exp_int_mul]

theorem step_root_primitive (N : ℕ) (hN : 0 < N) :
    IsPrimitiveRoot (rot (2 * Real.pi / N)) N := by
  convert Complex.isPrimitiveRoot_exp N hN.ne' using 1
  unfold LinearInputCurveWordAlgebra.rotation
  push_cast
  ring_nf

private theorem rotation_neg (a : ℝ) : rot (-a) = (rot a)⁻¹ := by
  simp [LinearInputCurveWordAlgebra.rotation, neg_mul, Complex.exp_neg]

/-- The right-turn chord is the left-turn chord viewed from one heading earlier. -/
theorem negative_chord {h a : ℝ} (hh : 0 < h) (ha : a ≠ 0) :
    endpoint (arcState h (-a)) = rot (-a) * endpoint (arcState h a) := by
  rw [arc_state_formula hh (neg_ne_zero.mpr ha), arc_state_formula hh ha]
  apply Complex.ext <;>
    simp only [endpoint, LinearInputCurveWordAlgebra.rotation, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg, div_neg, mul_neg] <;>
    field_simp <;> nlinarith [Real.sin_sq_add_cos_sq a]

/-- The integrated chord of one step is nonzero for at least two headings. -/
theorem chord_ne_zero {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 1 < N) :
    endpoint (arcState h (2 * Real.pi / N)) ≠ 0 := by
  let a : ℝ := 2 * Real.pi / N
  have ha : a ≠ 0 := by dsimp [a]; positivity
  intro he
  change endpoint (arcState h a) = 0 at he
  rw [arc_state_formula hh ha] at he
  have hx := congrArg Complex.re he
  have hy := congrArg Complex.im he
  change h * Real.sin a / a = 0 at hx
  change h * (1 - Real.cos a) / a = 0 at hy
  have hs : Real.sin a = 0 := (mul_eq_zero.mp ((div_eq_zero_iff.mp hx).resolve_right ha)).resolve_left hh.ne'
  have hc : Real.cos a = 1 := by
    have h1 := (mul_eq_zero.mp ((div_eq_zero_iff.mp hy).resolve_right ha)).resolve_left hh.ne'
    linarith
  apply (step_root_primitive N (by omega)).ne_one hN
  change rot a = 1
  apply Complex.ext <;>
    simp [LinearInputCurveWordAlgebra.rotation, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, hs, hc]

/-- A lifted initial heading rotates the sum over the actual traversed heading edges. -/
theorem rotated_endpoint_eq_edge_sum {h a : ℝ} (hh : 0 < h) (ha : a ≠ 0)
    (w : List Bool) (j : ℤ) :
    rot a ^ j * endpoint (arcWord h a w) =
      endpoint (arcState h a) * ((edges j w).map (fun i => rot a ^ i)).sum := by
  have hz : rot a ≠ 0 := Complex.exp_ne_zero _
  induction w generalizing j with
  | nil => simp [arcWord, emptyState, endpoint, edges]
  | cons b w ih =>
    cases b with
    | false =>
      simp only [arcWord, Bool.false_eq_true, ite_false, join_endpoint, edges, List.map_cons,
        List.sum_cons]
      rw [negative_chord hh ha]
      have hang : angle (arcState h (-a)) = -a := by
        rw [arc_state_formula hh (neg_ne_zero.mpr ha)]; rfl
      rw [hang, rotation_neg, mul_add, ← mul_assoc, ← mul_assoc,
        ← zpow_sub_one₀ hz, ih (j-1)]
      ring
    | true =>
      simp only [arcWord, ite_true, join_endpoint, edges, List.map_cons, List.sum_cons]
      have hang : angle (arcState h a) = a := by rw [arc_state_formula hh ha]; rfl
      rw [hang, mul_add, ← mul_assoc, ← zpow_add_one₀ hz, ih (j+1)]
      ring

theorem endpoint_eq_edge_sum {h a : ℝ} (hh : 0 < h) (ha : a ≠ 0) (w : List Bool) :
    endpoint (arcWord h a w) =
      endpoint (arcState h a) * ((edges 0 w).map (fun i => rot a ^ i)).sum := by
  simpa using rotated_endpoint_eq_edge_sum hh ha w 0

private theorem residue_power {N : ℕ} (hN : 0 < N) (i : ℤ) :
    rot (2 * Real.pi / N) ^ i =
      rot (2 * Real.pi / N) ^ (i % (N : ℤ)).toNat := by
  let z := rot (2 * Real.pi / N)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hroot := (step_root_primitive N hN).pow_eq_one
  change z ^ i = z ^ (i % (N : ℤ)).toNat
  calc
    _ = z ^ (i % (N : ℤ) + (N : ℤ) * (i / (N : ℤ))) := by rw [Int.emod_add_mul_ediv]
    _ = z ^ (i % (N : ℤ)) := by
      rw [zpow_add₀ hz, zpow_mul, zpow_natCast, show z ^ N = 1 from hroot, one_zpow, mul_one]
    _ = _ := by rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]

private theorem sum_powers_by_count (z : ℂ) (N : ℕ) (l : List ℕ)
    (hl : ∀ i ∈ l, i < N) :
    (l.map (fun i => z ^ i)).sum =
      ∑ i ∈ Finset.range N, (l.count i : ℂ) * z ^ i := by
  induction l with
  | nil => simp
  | cons k l ih =>
    have hk := hl k (by simp)
    have htail : ∀ i ∈ l, i < N := fun i hi => hl i (by simp [hi])
    simp only [List.map_cons, List.sum_cons, ih htail, List.count_cons, Nat.cast_add, add_mul,
      Finset.sum_add_distrib]
    simp [apply_ite, ite_mul, Finset.mem_range.mpr hk, add_comm]

theorem endpoint_eq_residue_counts {h : ℝ} (N : ℕ) (hN : 0 < N) (hh : 0 < h)
    (w : List Bool) :
    endpoint (arcWord h (2 * Real.pi / N) w) =
      endpoint (arcState h (2 * Real.pi / N)) *
        ∑ i ∈ Finset.range N, ((edgeResidues N 0 w).count i : ℂ) *
            rot (2 * Real.pi / N) ^ i := by
  rw [endpoint_eq_edge_sum hh (by positivity)]
  congr 1
  rw [← sum_powers_by_count]
  · simp only [edgeResidues, List.map_map, Function.comp_def]
    simp_rw [← residue_power hN]
  · intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    have hb := Int.emod_lt_of_pos j (show 0 < (N : ℤ) by exact_mod_cast hN)
    omega

def nineCertificate : List Bool :=
  [true, false, true, true, true, true, false, true, true, true, true, false, true, true, true]

/-- A non-multiple of nine steps closes with one full positive turn. -/
theorem nine_certificate_closes {h : ℝ} (hh : 0 < h) :
    nineCertificate.length = 15 ∧
    endpoint (arcWord h (2 * Real.pi / 9) nineCertificate) = 0 ∧
    angle (arcWord h (2 * Real.pi / 9) nineCertificate) = 2 * Real.pi ∧
    rot (angle (arcWord h (2 * Real.pi / 9) nineCertificate)) = 1 := by
  let z := rot (2 * Real.pi / 9)
  have hp : IsPrimitiveRoot z 9 := by simpa [z] using step_root_primitive 9 (by decide)
  have hsum : 1 + z ^ 3 + z ^ 6 = 0 := by
    have hf : (1 + z ^ 3 + z ^ 6) * (z ^ 3 - 1) = 0 := by
      calc
        _ = z ^ 9 - 1 := by ring
        _ = 0 := by rw [hp.pow_eq_one, sub_self]
    exact (mul_eq_zero.mp hf).resolve_right (sub_ne_zero.mpr
      (hp.pow_ne_one_of_pos_of_lt (by decide) (by decide)))
  have hang : angle (arcWord h (2 * Real.pi / 9) nineCertificate) = 2 * Real.pi := by
    rw [angle_arcWord hh (by positivity)]
    change (9 : ℝ) * (2 * Real.pi / 9) = 2 * Real.pi
    ring
  refine ⟨rfl, ?_, hang, ?_⟩
  · rw [endpoint_eq_edge_sum hh (by positivity)]
    change _ * (([0,0,0,1,2,3,3,3,4,5,6,6,6,7,8] : List ℤ).map (fun i => z ^ i)).sum = 0
    suffices hs : (([0,0,0,1,2,3,3,3,4,5,6,6,6,7,8] : List ℤ).map
        (fun i => z ^ i)).sum = 0 by rw [hs, mul_zero]
    norm_num
    linear_combination (3 + z + z ^ 2) * hsum
  · rw [hang]
    simp [LinearInputCurveWordAlgebra.rotation]

end LinearInputRobotWalkArc

end
