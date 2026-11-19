/-! Transfer the integral edge polynomial to characteristic two. -/

namespace RobotFacingOdd

open LinearInputCurveWordAlgebra LinearInputRobotWalkArc Polynomial

/-- Each traversal contributes one monomial, regardless of its direction. -/
noncomputable def edgePolynomial (N : ℕ) (w : List Bool) : ℤ[X] :=
  ((edgeResidues N 0 w).map (fun i => (X : ℤ[X]) ^ i)).sum

private theorem reduce_heading_power {K : Type*} [Field K] {u : K}
    {N : ℕ} (hN : 0 < N) (hu : IsPrimitiveRoot u N) (i : ℤ) :
    u ^ (i % (N : ℤ)).toNat = u ^ i := by
  have hun := hu.ne_zero hN.ne'
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  conv_rhs => rw [← Int.emod_add_mul_ediv i (N : ℤ)]
  rw [zpow_add₀ hun, zpow_mul, zpow_natCast, hu.pow_eq_one, one_zpow, mul_one]

private theorem eval_edgePolynomial {K : Type*} [Field K] {u : K}
    {N : ℕ} (hN : 0 < N) (hu : IsPrimitiveRoot u N) (w : List Bool) :
    aeval u (edgePolynomial N w) = ((edges 0 w).map (fun i => u ^ i)).sum := by
  simp only [edgePolynomial, edgeResidues, map_list_sum, List.map_map, Function.comp_def,
    map_pow, aeval_X, reduce_heading_power hN hu]

theorem cyclotomic_dvd_of_closed {N : ℕ} (hN : 1 < N) {h : ℝ} (hh : 0 < h)
    (w : List Bool) (hc : endpoint (arcWord h (2 * Real.pi / N) w) = 0) :
    cyclotomic N ℤ ∣ edgePolynomial N w := by
  let z := rotation (2 * Real.pi / N)
  have hn : 0 < N := by omega
  have hz : IsPrimitiveRoot z N := step_root_primitive N hn
  rw [cyclotomic_eq_minpoly hz hn]
  apply minpoly.isIntegrallyClosed_dvd (hz.isIntegral hn)
  rw [eval_edgePolynomial hn hz]
  rw [endpoint_eq_edge_sum hh (by positivity)] at hc
  exact (mul_eq_zero.mp hc).resolve_left (chord_ne_zero hh hN)

/-- In characteristic two, the two orientations of an edge have the same boundary. -/
private theorem char_two_boundary {K : Type*} [Field K] [CharP K 2] {u : K}
    (hu : u ≠ 0) (w : List Bool) (j : ℤ) :
    (u + 1) * ((edges j w).map (fun i => u ^ i)).sum = u ^ (j + turns w) + u ^ j := by
  induction w generalizing j with
  | nil => simp [edges, turns, CharTwo.add_self_eq_zero]
  | cons b w ih =>
    cases b with
    | false =>
      simp only [edges, turns, List.map_cons, List.sum_cons, mul_add, ih]
      rw [show j + (-1 + turns w) = j - 1 + turns w by omega]
      have hs : u ^ (j - 1) * u = u ^ j := by
        rw [← zpow_add_one₀ hu, sub_add_cancel]
      calc
        _ = u ^ (j - 1 + turns w) + u ^ (j - 1) * u + (u ^ (j - 1) + u ^ (j - 1)) := by ring
        _ = _ := by rw [hs, CharTwo.add_self_eq_zero, add_zero]
    | true =>
      simp only [edges, turns, List.map_cons, List.sum_cons, mul_add, ih]
      rw [show j + (1 + turns w) = j + 1 + turns w by omega]
      have hs : u ^ (j + 1) = u ^ j * u := zpow_add_one₀ hu _
      calc
        _ = u ^ (j + 1 + turns w) + u ^ j + (u ^ (j + 1) + u ^ (j + 1)) := by rw [hs]; ring
        _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

/-- Position closure forces facing closure for every odd order greater than one. -/
theorem facing_of_closed_odd {N : ℕ} (hN : 1 < N) (hodd : Odd N) {h : ℝ}
    (hh : 0 < h) (w : List Bool) (hc : endpoint (arcWord h (2 * Real.pi / N) w) = 0) :
    rotation (angle (arcWord h (2 * Real.pi / N) w)) = 1 := by
  let K := AlgebraicClosure (ZMod 2)
  have hn : 0 < N := by omega
  let : NeZero (N : ZMod 2) :=
    ⟨fun h => (Nat.not_even_iff_odd.mpr hodd) (ZMod.natCast_eq_zero_iff_even.mp h)⟩
  let : NeZero (N : K) := (inferInstance : NeZero (N : ZMod 2)).of_injective
    (algebraMap (ZMod 2) K).injective
  obtain ⟨u, hu⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K N
  have hphi : aeval u (cyclotomic N ℤ) = 0 := by
    simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using hu.isRoot_cyclotomic hn
  have heval := aeval_eq_zero_of_dvd_aeval_eq_zero (cyclotomic_dvd_of_closed hN hh w hc) hphi
  have hsum := (eval_edgePolynomial hn hu w).symm.trans heval
  have hb := char_two_boundary (hu.ne_zero hn.ne') w 0
  simp only [hsum, mul_zero, zero_add, zpow_zero] at hb
  exact (RobotSix.facing_iff_dvd hn hh w).mpr
    ((hu.zpow_eq_one_iff_dvd _).mp (CharTwo.add_eq_zero.mp hb.symm))

end RobotFacingOdd
