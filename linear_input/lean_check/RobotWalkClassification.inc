/-!
A circular-arc word closes in the plane exactly when its multiplicities of
heading edges repeat in blocks of length `q^a`, at order `q^(a+1)`.
-/

noncomputable section
namespace LinearInputRobotWalkClassification

open LinearInputCurveWordAlgebra LinearInputRobotWalkArc

theorem closed_iff_periodic (q a : ℕ) (hq : q.Prime) {h : ℝ} (hh : 0 < h)
    (w : List Bool) :
    endpoint (arcWord h (2 * Real.pi / (q ^ (a + 1) : ℕ)) w) = 0 ↔
      ∀ i < q ^ (a + 1), (edgeResidues (q ^ (a + 1)) 0 w).count i =
        (edgeResidues (q ^ (a + 1)) 0 w).count (i % q ^ a) := by
  have hN : 1 < q ^ (a + 1) := one_lt_pow₀ hq.one_lt (by omega)
  rw [endpoint_eq_residue_counts _ (by omega) hh, mul_eq_zero,
    or_iff_right (chord_ne_zero hh hN)]
  exact LinearInputRobotCyclotomic.sum_zero_iff_periodic q a hq
    (step_root_primitive _ (by omega)) _

open LinearInputRobotWalkLengths

/-- Endpoints and facing direction are different projections of the curve-word state. -/
theorem facing_of_closed (q a : ℕ) (hq : q.Prime) {h : ℝ} (hh : 0 < h)
    (w : List Bool) (hw : endpoint (arcWord h (2 * Real.pi / (q ^ (a + 1) : ℕ)) w) = 0) :
    LinearInputCurveWordAlgebra.rotation (angle (arcWord h (2 * Real.pi / (q ^ (a + 1) : ℕ)) w)) = 1 := by
  let N := q ^ (a + 1)
  have hN : 0 < N := pow_pos hq.pos _
  have hp := (closed_iff_periodic q a hq hh w).mp hw
  have ht := heading_closed_of_periodic (d := q ^ a) (pow_pos hq.pos _) hq.two_le w
    (by simpa only [pow_succ' q a] using hp)
  have ht' : (turns w % (N : ℤ)).toNat = 0 := by simpa only [N, pow_succ' q a] using ht
  have hn' : (0 : ℤ) < N := by exact_mod_cast hN
  have hnz := Int.emod_nonneg (turns w) hn'.ne'
  have hdvd : (N : ℤ) ∣ turns w := Int.dvd_of_emod_eq_zero (by omega)
  change LinearInputCurveWordAlgebra.rotation (angle (arcWord h (2 * Real.pi / N) w)) = 1
  rw [angle_arcWord hh (by positivity), rotation_int_mul]
  exact ((step_root_primitive N hN).zpow_eq_one_iff_dvd _).mpr hdvd

/-- Existence refers to the end position of actual joined circular arcs. -/
def IsClosedLength (h : ℝ) (N n : ℕ) : Prop :=
  ∃ w : List Bool, w.length = n ∧ endpoint (arcWord h (2 * Real.pi / N) w) = 0

theorem closed_length_iff (q a n : ℕ) (hq : q.Prime) (ho : Odd q)
    {h : ℝ} (hh : 0 < h) (hn : 0 < n) :
    IsClosedLength h (q ^ (a + 1)) n ↔
      ∃ t : ℕ, n = q ^ (a + 1) + 2*q*t ∨ n = 2*q ^ (a + 1) + 2*q*t := by
  constructor
  · rintro ⟨w, rfl, hw⟩
    have hne : w ≠ [] := by rintro rfl; simp at hn
    have hp := (closed_iff_periodic q a hq hh w).mp hw
    rw [pow_succ' q a] at hp ⊢
    exact possible_length_of_periodic (pow_pos hq.pos _) hq.two_le hne hp
  · rintro ⟨t, hlen | hlen⟩
    · obtain ⟨w, hw, hc, _⟩ := construct_closed q (q^a) 1 t hq.one_lt
        (pow_pos hq.pos _) (by simp) hh
      exact ⟨w, by simpa [hlen, pow_succ' q a] using hw, by simpa only [pow_succ' q a] using hc⟩
    · obtain ⟨w, hw, hc, _⟩ := construct_closed q (q^a) 2 t hq.one_lt
        (pow_pos hq.pos _) (Nat.coprime_two_left.mpr ho) hh
      exact ⟨w, by simpa only [hlen, pow_succ' q a] using hw, by simpa only [pow_succ' q a] using hc⟩

/-- For exponent at least two the shortest positive return off the multiples of
the order is exactly one full turn plus two traversals for each of the q copies. -/
theorem least_nonmultiple (q a : ℕ) (hq : q.Prime) (ho : Odd q) {h : ℝ} (hh : 0 < h) :
    IsLeast {n : ℕ | IsClosedLength h (q ^ (a + 2)) n ∧ ¬ q ^ (a + 2) ∣ n}
      (q ^ (a + 2) + 2*q) := by
  let N := q ^ (a + 2)
  have hq3 := hq.odd_iff.mp ho
  have hN : 2*q < N := by
    have hpow : 0 < q^a := pow_pos hq.pos _
    dsimp [N]
    rw [pow_add, pow_two]
    nlinarith [Nat.mul_le_mul_right (q*q) (show 1 ≤ q^a by omega),
      Nat.mul_le_mul_right q hq3]
  have hnondvd : ¬ N ∣ N + 2*q := by
    intro hdiv
    have : N ∣ 2*q := (Nat.dvd_add_right (dvd_refl N)).mp hdiv
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) hN) this
  constructor
  · refine ⟨(closed_length_iff q (a+1) _ hq ho hh (by positivity)).mpr ?_, hnondvd⟩
    exact ⟨1, Or.inl (by simp)⟩
  · rintro n ⟨hw, hdiv⟩
    have hn : 0 < n := by
      by_contra! hn
      have : n = 0 := by omega
      exact hdiv (this ▸ dvd_zero _)
    obtain ⟨t, ht | ht⟩ := (closed_length_iff q (a+1) n hq ho hh hn).mp hw
    · change n = N + 2*q*t at ht
      cases t with
      | zero => simp at ht; exact (hdiv (ht ▸ dvd_refl N)).elim
      | succ t => change N + 2*q ≤ n; rw [ht, Nat.mul_succ]; omega
    · change n = 2*N + 2*q*t at ht
      change N + 2*q ≤ n
      omega

end LinearInputRobotWalkClassification
end
