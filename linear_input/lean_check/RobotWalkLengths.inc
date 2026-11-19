/-!
Constructing closed equal-radius arc words by rotating a single block.
The construction applies at every positive scale and its length is explicit.
-/

noncomputable section

namespace LinearInputRobotWalkLengths

open LinearInputCurveWordAlgebra LinearInputRobotWalkArc

/-- Repeat a word, keeping the order of all its letters. -/
def copies (w : List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => copies w n ++ w

theorem copies_length (w : List Bool) (n : ℕ) :
    (copies w n).length = n * w.length := by
  induction n with
  | zero => simp [copies]
  | succ n ih => simp [copies, ih, Nat.succ_mul]

theorem copies_state (h a : ℝ) (w : List Bool) (n : ℕ) :
    rotation (angle (arcWord h a (copies w n))) = rotation (angle (arcWord h a w)) ^ n ∧
    endpoint (arcWord h a (copies w n)) =
      (∑ i ∈ Finset.range n, rotation (angle (arcWord h a w)) ^ i) *
        endpoint (arcWord h a w) := by
  induction n with
  | zero => simp [copies, arcWord, emptyState, endpoint, angle, rotation_zero]
  | succ n ih =>
    simp only [copies, arcWord_append, join_angle, rotation_add, join_endpoint,
      Finset.sum_range_succ, pow_succ, ih.1, ih.2, add_mul, and_self]

/-- Insert cancelling left and right turns in a block with a prescribed net turn. -/
def turningBlock (advance detours : ℕ) : List Bool :=
  List.replicate advance true ++ copies [true, false] detours

theorem turningBlock_length (advance detours : ℕ) :
    (turningBlock advance detours).length = advance + 2 * detours := by
  simp [turningBlock, copies_length, Nat.mul_comm]

private theorem signed_replicate_true (k : ℕ) :
    turns (List.replicate k true) = k := by
  induction k with
  | zero => simp [turns]
  | succ k ih => simp [List.replicate_succ, turns, ih]; ring

private theorem detour_turns (k : ℕ) :
    turns (copies [true, false] k) = 0 := by
  induction k with
  | zero => simp [copies, turns]
  | succ k ih => simp [copies, turns_append, turns, ih]

theorem turningBlock_turns (advance detours : ℕ) :
    turns (turningBlock advance detours) = advance := by
  simp [turningBlock, turns_append, signed_replicate_true, detour_turns]

/-- At turn angle 2π/(q d), repeat a block advancing s d headings.
Coprimality ensures that its q copies have zero total displacement. -/
theorem construct_closed (q d s t : ℕ) (hq : 1 < q) (hd : 0 < d)
    (hs : s.Coprime q) {h : ℝ} (hh : 0 < h) :
    ∃ w : List Bool, w.length = s * (q * d) + 2 * q * t ∧
      endpoint (arcWord h (2 * Real.pi / (q * d : ℕ)) w) = 0 ∧
      rotation (angle (arcWord h (2 * Real.pi / (q * d : ℕ)) w)) = 1 := by
  let w := turningBlock (s * d) t
  let a : ℝ := 2 * Real.pi / (q * d : ℕ)
  have hq0 : q ≠ 0 := by omega
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hr : IsPrimitiveRoot (rotation (angle (arcWord h a w))) q := by
    rw [angle_arcWord hh ha, show turns w = ↑(s * d) from turningBlock_turns ..]
    convert Complex.isPrimitiveRoot_exp_of_coprime s q hq0 hs using 1
    unfold LinearInputCurveWordAlgebra.rotation
    congr 1
    push_cast
    dsimp [a]
    push_cast
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp [hdC]
  refine ⟨copies w q, ?_, ?_, ?_⟩
  · rw [copies_length, turningBlock_length]
    ring
  · change endpoint (arcWord h a (copies w q)) = 0
    rw [(copies_state h a w q).2, hr.geom_sum_eq_zero hq, zero_mul]
  · change rotation (angle (arcWord h a (copies w q))) = 1
    rw [(copies_state h a w q).1, hr.pow_eq_one]

/-- The residue of a lifted heading, as an index in [0,N). -/
private def residue (N : ℕ) (x : ℤ) : ℕ := (x % (N : ℤ)).toNat

private theorem residue_lt {N : ℕ} (hN : 0 < N) (x : ℤ) : residue N x < N := by
  have hn : 0 < (N : ℤ) := by exact_mod_cast hN
  have := Int.emod_lt_of_pos x hn
  unfold residue
  omega

private theorem residue_succ {N : ℕ} (hN : 0 < N) (x : ℤ) :
    residue N (x + 1) = if residue N x + 1 = N then 0 else residue N x + 1 := by
  have hn : 0 < (N : ℤ) := by exact_mod_cast hN
  have hlo := Int.emod_nonneg x (ne_of_gt hn)
  have hhi := Int.emod_lt_of_pos x hn
  unfold residue
  rw [← Int.emod_add_emod x (N : ℤ) 1]
  split_ifs with hh
  · have hx : x % (N : ℤ) + 1 = N := by omega
    simp [hx]
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

private def side (N i : ℕ) (x : ℤ) : ℕ := if i < residue N x then 1 else 0

/-- A forward step changes side of the cut precisely at its boundary edges;
when these coincide their two contributions cancel modulo two. -/
private theorem cut_step {N i : ℕ} (hN : 0 < N) (hi : i < N) (x : ℤ) :
    ((if residue N x = i then 1 else 0) + (if residue N x = N-1 then 1 else 0) +
      side N i x + side N i (x+1)) % 2 = 0 := by
  have hr := residue_lt hN x
  unfold side
  rw [residue_succ hN]
  split_ifs <;> omega

private theorem cut_walk {N i : ℕ} (hN : 0 < N) (hi : i < N)
    (j : ℤ) (w : List Bool) :
    ((edgeResidues N j w).count i + (edgeResidues N j w).count (N-1) +
      side N i j + side N i (j + turns w)) % 2 = 0 := by
  induction w generalizing j with
  | nil => simp [edgeResidues, edges, turns]; omega
  | cons b w ih =>
    cases b
    · have ht := ih (j-1)
      have hs := cut_step hN hi (j-1)
      rw [show j-1+1=j by omega] at hs
      change ((residue N (j-1) :: edgeResidues N (j-1) w).count i +
        (residue N (j-1) :: edgeResidues N (j-1) w).count (N-1) +
        side N i j + side N i (j + (-1 + turns w))) % 2 = 0
      rw [show j + (-1 + turns w) = j-1 + turns w by omega]
      simp only [List.count_cons, beq_iff_eq]
      omega
    · have ht := ih (j+1)
      have hs := cut_step hN hi j
      change ((residue N j :: edgeResidues N (j+1) w).count i +
        (residue N j :: edgeResidues N (j+1) w).count (N-1) +
        side N i j + side N i (j + (1 + turns w))) % 2 = 0
      rw [show j + (1 + turns w) = j+1 + turns w by omega]
      simp only [List.count_cons, beq_iff_eq]
      omega

/-- A repeated edge profile on the cycle forces the terminal heading to be the
initial heading modulo the number of edges. The proof uses parity across cuts. -/
theorem heading_closed_of_periodic {d q : ℕ} (hd : 0 < d) (hq : 2 ≤ q) (w : List Bool)
    (hp : ∀ i < q * d, (edgeResidues (q * d) 0 w).count i =
      (edgeResidues (q * d) 0 w).count (i % d)) :
    (turns w % (q * d : ℕ)).toNat = 0 := by
  let N := q * d
  change residue N (turns w) = 0
  have hN : 0 < N := Nat.mul_pos (by omega) hd
  have h2 : 2 * d ≤ N := Nat.mul_le_mul_right d hq
  have hh : ∀ i < N, ((edgeResidues N 0 w).count i +
      (edgeResidues N 0 w).count (N-1) + side N i (turns w)) % 2 = 0 := by
    intro i hi
    simpa [side, residue] using cut_walk hN hi 0 w
  have hside (i j : ℕ) (hi : i<N) (hj : j<N) (he : i % d=j % d) :
      (i < residue N (turns w)) ↔ (j < residue N (turns w)) := by
    have hc : (edgeResidues N 0 w).count i = (edgeResidues N 0 w).count j :=
      (hp i hi).trans ((he ▸ hp j hj).symm)
    have h1 := hh i hi
    have h2' := hh j hj
    rw [hc] at h1
    unfold side at h1 h2'
    split_ifs at h1 h2' <;> omega
  have hlast : N - d = (q-1)*d := by dsimp [N]; rw [Nat.sub_one_mul]
  have hmod : (N-d) % d = 0 := by rw [hlast]; simp
  have hfinal := residue_lt hN (turns w)
  by_contra hn
  have hx : N-d < residue N (turns w) :=
    (hside 0 (N-d) (by omega) (by omega) (by simp [hmod])).mp (by omega)
  have hmodlast : (N-1)%d = d-1 := by
    rw [show N-1 = (N-d) + (d-1) by omega, Nat.add_mod, hmod]
    simp [Nat.mod_eq_of_lt (show d-1<d by omega)]
  have := (hside (d-1) (N-1) (by omega) (by omega)
    (by simp [hmodlast, Nat.mod_eq_of_lt (show d-1<d by omega)])).mp (by omega)
  omega

theorem edge_parity_of_periodic {d q : ℕ} (hd : 0 < d) (hq : 2 ≤ q) (w : List Bool)
    (hp : ∀ i < q * d, (edgeResidues (q * d) 0 w).count i =
      (edgeResidues (q * d) 0 w).count (i % d)) (i : ℕ) (hi : i < q * d) :
    (edgeResidues (q * d) 0 w).count i % 2 =
      (edgeResidues (q * d) 0 w).count (q * d-1) % 2 := by
  have hzero := heading_closed_of_periodic hd hq w hp
  have hk := cut_walk (Nat.mul_pos (by omega) hd) hi 0 w
  have hres : residue (q * d) (turns w) = 0 := hzero
  have hz : side (q * d) i (turns w) = 0 := by simp only [side, hres, Nat.not_lt_zero, ite_false]
  simp only [zero_add, hz, Nat.add_zero] at hk
  have hs : side (q * d) i 0 = 0 := by simp [side, residue]
  rw [hs, Nat.add_zero] at hk
  omega

theorem possible_length_of_periodic {d q : ℕ} (hd : 0 < d) (hq : 2 ≤ q)
    {w : List Bool} (hw : w ≠ [])
    (hp : ∀ i < q * d, (edgeResidues (q * d) 0 w).count i =
      (edgeResidues (q * d) 0 w).count (i % d)) :
    ∃ t : ℕ, w.length = q * d + 2 * q * t ∨ w.length = 2 * (q * d) + 2 * q * t := by
  apply LinearInputRobotWalkSupport.length_of_periodic_of_parity hq hd hw hp
  intro i hi
  have hN := Nat.mul_pos (show 0 < q by omega) hd
  exact (edge_parity_of_periodic hd hq w hp i hi).trans
    (edge_parity_of_periodic hd hq w hp 0 hN).symm

end LinearInputRobotWalkLengths
