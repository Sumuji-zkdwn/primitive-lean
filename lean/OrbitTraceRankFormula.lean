import OrbitTraceFiltration
import OrbitTraceJordanIndex

/-!
# The all-degree rank formula for the canonical transfer deviation

`docs/research/2026-11-04-orbit-trace-integrals.md` (sections 10, 11 and 14)
left the rank formula

  rank (N^j restricted to V_d) = max(0, d + 1 - j (p + 1))

as a hand proof without a Lean proof, where `V_d = Q[X]_{≤ d}` and
`N = canonicalDelta p a = L - id` is the genuine linear operator of
`OrbitTraceTransferOperator.lean`.

The proof here does not construct a Jordan basis. It isolates one property:

* `ExactShift T m`: `T` kills every polynomial of degree `< m` and lowers the
  degree of every other nonzero polynomial by exactly `m`.

`ExactShift` is closed under composition (`ExactShift.comp`, `ExactShift.pow`),
and for any such `T` the image of `V_d` is exactly `V_{d-m}`
(`ExactShift.map_degreeLT`) while its kernel inside `V_d` is `V_{min(m, d+1)-1}`
(`ExactShift.ker_inf_degreeLT`). For `a ≠ 0` the canonical deviation satisfies
`ExactShift N (p + 1)` (`canonicalDelta_exactShift`), using the already verified
exact monomial degree drop and degree bound. Hence

* `canonicalDelta_pow_rank`: `finrank (N^j (V_d)) = d + 1 - j (p + 1)`
  (natural subtraction, i.e. `max(0, ·)`),
* `canonicalDelta_ker_rank`: `finrank (V_d ⊓ ker N) = min (p + 1) (d + 1)`,
* `canonicalDelta_pow_vanish_iff`: `N^j` vanishes on `V_d` iff `d < j (p + 1)`,
  so the nilpotency index on `V_d` is `d / (p + 1) + 1`.

The Jordan type follows from the rank sequence by the usual linear-algebra
argument; that deduction and the explicit chain basis are not formalized here.
-/

namespace OrbitTrace

open Polynomial

section ExactShift

variable {K : Type*} [Field K]

/-- `T` kills degree `< m` and lowers every other nonzero polynomial by exactly `m`. -/
def ExactShift (T : K[X] →ₗ[K] K[X]) (m : ℕ) : Prop :=
  ∀ P : K[X], (P.natDegree < m → T P = 0) ∧
    (P ≠ 0 → m ≤ P.natDegree → T P ≠ 0 ∧ (T P).natDegree = P.natDegree - m)

theorem ExactShift.id : ExactShift (LinearMap.id : K[X] →ₗ[K] K[X]) 0 :=
  fun P => ⟨fun h => absurd h (Nat.not_lt_zero _), fun hP _ => ⟨hP, by simp⟩⟩

theorem ExactShift.comp {S T : K[X] →ₗ[K] K[X]} {m n : ℕ} (hT : ExactShift T m)
    (hS : ExactShift S n) : ExactShift (S ∘ₗ T) (m + n) := by
  intro P
  refine ⟨fun hlt => ?_, fun hP hle => ?_⟩
  · by_cases h0 : P = 0
    · simp [h0]
    by_cases hm : P.natDegree < m
    · simp [(hT P).1 hm]
    · obtain ⟨hTP, hdeg⟩ := (hT P).2 h0 (by omega)
      simp only [LinearMap.comp_apply]
      exact (hS (T P)).1 (by omega)
  · obtain ⟨hTP, hdeg⟩ := (hT P).2 hP (by omega)
    obtain ⟨hSTP, hdeg'⟩ := (hS (T P)).2 hTP (by omega)
    exact ⟨hSTP, by simp only [LinearMap.comp_apply]; omega⟩

theorem ExactShift.pow {T : K[X] →ₗ[K] K[X]} {m : ℕ} (hT : ExactShift T m) (j : ℕ) :
    ExactShift (T ^ j) (j * m) := by
  induction j with
  | zero =>
    rw [pow_zero, Nat.zero_mul, Module.End.one_eq_id]
    exact ExactShift.id
  | succ j ih =>
    rw [pow_succ, Module.End.mul_eq_comp, show (j + 1) * m = m + j * m by ring]
    exact hT.comp ih

theorem ExactShift.maps_degreeLT {T : K[X] →ₗ[K] K[X]} {m : ℕ} (hT : ExactShift T m)
    {d : ℕ} {P : K[X]} (hP : P ∈ degreeLT K (d + 1)) : T P ∈ degreeLT K (d + 1 - m) := by
  rw [Polynomial.mem_degreeLT] at hP ⊢
  by_cases h0 : P = 0
  · simp [h0]
  by_cases hm : P.natDegree < m
  · simp [(hT P).1 hm]
  · obtain ⟨hTP, hdeg⟩ := (hT P).2 h0 (by omega)
    have := (natDegree_lt_iff_degree_lt h0).mpr hP
    rw [← natDegree_lt_iff_degree_lt hTP]
    omega

/-- The image of `V_d = degreeLT (d+1)` is exactly `degreeLT (d+1-m)`. -/
theorem ExactShift.map_degreeLT {T : K[X] →ₗ[K] K[X]} {m : ℕ} (hT : ExactShift T m)
    (d : ℕ) : Submodule.map T (degreeLT K (d + 1)) = degreeLT K (d + 1 - m) := by
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    exact hT.maps_degreeLT hP
  · -- every target of degree < n (n ≤ d+1-m) is reached, by induction on n
    suffices key : ∀ n, n ≤ d + 1 - m → ∀ Q ∈ degreeLT K n,
        Q ∈ Submodule.map T (degreeLT K (d + 1)) from key _ le_rfl
    intro n
    induction n with
    | zero =>
      intro _ Q hQ
      have hQ0 : Q = 0 := by
        ext k
        rw [Polynomial.mem_degreeLT, degree_lt_iff_coeff_zero] at hQ
        simpa using hQ k (Nat.zero_le k)
      rw [hQ0]
      exact Submodule.zero_mem _
    | succ n ih =>
      intro hn Q hQ
      have hXmem : (X : K[X]) ^ (n + m) ∈ degreeLT K (d + 1) := by
        rw [Polynomial.mem_degreeLT, degree_X_pow]
        exact_mod_cast (by omega : n + m < d + 1)
      obtain ⟨hTX, hTXdeg⟩ := (hT (X ^ (n + m))).2 (pow_ne_zero _ X_ne_zero)
        (by rw [natDegree_X_pow]; omega)
      rw [natDegree_X_pow, Nat.add_sub_cancel] at hTXdeg
      set R := T (X ^ (n + m)) with hR
      have hc0 : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hTX
      set Q' := Q - C (Q.coeff n / R.leadingCoeff) * R with hQ'
      have hQ'mem : Q' ∈ degreeLT K n := by
        rw [Polynomial.mem_degreeLT, degree_lt_iff_coeff_zero]
        intro k hk
        rw [Polynomial.mem_degreeLT, degree_lt_iff_coeff_zero] at hQ
        simp only [hQ', coeff_sub, coeff_C_mul]
        rcases Nat.eq_or_lt_of_le hk with rfl | hlt
        · have hRn : R.coeff n = R.leadingCoeff := by rw [leadingCoeff, hTXdeg]
          rw [hRn]
          field_simp
          ring
        · rw [hQ k (by omega), coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < k)]
          ring
      have hQ'map := ih (by omega) Q' hQ'mem
      have hQeq : Q = Q' + T ((Q.coeff n / R.leadingCoeff) • X ^ (n + m)) := by
        rw [map_smul, smul_eq_C_mul, hQ']
        ring
      rw [hQeq]
      exact Submodule.add_mem _ hQ'map ⟨_, Submodule.smul_mem _ _ hXmem, rfl⟩

/-- Inside `V_d`, the kernel is `degreeLT (min m (d+1))`. -/
theorem ExactShift.ker_inf_degreeLT {T : K[X] →ₗ[K] K[X]} {m : ℕ} (hT : ExactShift T m)
    (d : ℕ) : degreeLT K (d + 1) ⊓ LinearMap.ker T = degreeLT K (min m (d + 1)) := by
  ext P
  simp only [Submodule.mem_inf, LinearMap.mem_ker, Polynomial.mem_degreeLT]
  constructor
  · rintro ⟨hP, hTP⟩
    by_cases h0 : P = 0
    · simp [h0]
    rw [← natDegree_lt_iff_degree_lt h0] at hP ⊢
    by_contra hge
    exact ((hT P).2 h0 (by omega)).1 hTP
  · intro hP
    have hle : (min m (d + 1) : WithBot ℕ) ≤ (d + 1 : ℕ) := by exact_mod_cast min_le_right _ _
    refine ⟨lt_of_lt_of_le hP (by exact_mod_cast min_le_right m (d + 1)), ?_⟩
    by_cases h0 : P = 0
    · simp [h0]
    rw [← natDegree_lt_iff_degree_lt h0] at hP
    exact (hT P).1 (by omega)

theorem finrank_degreeLT (n : ℕ) : Module.finrank K (degreeLT K n) = n := by
  rw [(degreeLTEquiv K n).finrank_eq, Module.finrank_fin_fun]

theorem ExactShift.finrank_map {T : K[X] →ₗ[K] K[X]} {m : ℕ} (hT : ExactShift T m) (d : ℕ) :
    Module.finrank K (Submodule.map T (degreeLT K (d + 1))) = d + 1 - m := by
  rw [hT.map_degreeLT, finrank_degreeLT]

theorem ExactShift.finrank_ker {T : K[X] →ₗ[K] K[X]} {m : ℕ} (hT : ExactShift T m) (d : ℕ) :
    Module.finrank K (degreeLT K (d + 1) ⊓ LinearMap.ker T : Submodule K K[X]) =
      min m (d + 1) := by
  rw [hT.ker_inf_degreeLT, finrank_degreeLT]

theorem ExactShift.vanish_iff {T : K[X] →ₗ[K] K[X]} {m : ℕ} (hT : ExactShift T m) (d : ℕ) :
    (∀ P ∈ degreeLT K (d + 1), T P = 0) ↔ d < m := by
  constructor
  · intro h
    by_contra hge
    have hX : (X : K[X]) ^ d ∈ degreeLT K (d + 1) := by
      rw [Polynomial.mem_degreeLT, degree_X_pow]
      exact_mod_cast Nat.lt_succ_self d
    exact ((hT (X ^ d)).2 (pow_ne_zero _ X_ne_zero) (by rw [natDegree_X_pow]; omega)).1
      (h _ hX)
  · intro hlt P hP
    by_cases h0 : P = 0
    · simp [h0]
    rw [Polynomial.mem_degreeLT, ← natDegree_lt_iff_degree_lt h0] at hP
    exact (hT P).1 (by omega)

end ExactShift

/-! ## The canonical deviation is an exact shift by `p + 1` -/

theorem canonicalDelta_exactShift (p : ℕ) (a : ℚ) (ha : a ≠ 0) :
    ExactShift (canonicalDelta p a) (p + 1) := by
  intro P
  refine ⟨fun hlt => canonicalDelta_zero_of_low_degree p a P (by omega), fun hP hle => ?_⟩
  set e := P.natDegree with he
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  -- split off the leading monomial
  have hsplit : canonicalDelta p a P =
      C P.leadingCoeff * canonicalDelta p a ((X : ℚ[X]) ^ e) +
        canonicalDelta p a P.eraseLead := by
    conv_lhs => rw [← eraseLead_add_C_mul_X_pow P]
    rw [map_add, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul, add_comm]
  have hlead : (C P.leadingCoeff * canonicalDelta p a ((X : ℚ[X]) ^ e)).degree =
      ((e - (p + 1) : ℕ) : WithBot ℕ) := by
    rw [degree_C_mul hlc, canonicalDelta_X_pow_exact_degree p e a ha hle]
  have hrest : (canonicalDelta p a P.eraseLead).degree <
      ((e - (p + 1) : ℕ) : WithBot ℕ) := by
    have herase : P.eraseLead.natDegree ≤ e - 1 := eraseLead_natDegree_le P
    rcases Nat.lt_or_ge (p + 1) e with hgt | heq
    · calc (canonicalDelta p a P.eraseLead).degree
          ≤ ((e - 1 - (p + 1) : ℕ) : WithBot ℕ) :=
            canonicalDelta_degree_bound p a (e - 1) _ herase
        _ < ((e - (p + 1) : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega)
    · rw [canonicalDelta_zero_of_low_degree p a _ (by omega), degree_zero]
      exact WithBot.bot_lt_coe _
  have hdeg : (canonicalDelta p a P).degree = ((e - (p + 1) : ℕ) : WithBot ℕ) := by
    rw [hsplit, degree_add_eq_left_of_degree_lt (hlead ▸ hrest), hlead]
  have hne : canonicalDelta p a P ≠ 0 := by
    intro h
    rw [h, degree_zero] at hdeg
    exact WithBot.bot_ne_coe hdeg
  exact ⟨hne, natDegree_eq_of_degree_eq_some hdeg⟩

/-! ## The rank formula -/

/-- **Rank formula**: `dim N^j(V_d) = max(0, d + 1 - j (p + 1))` for `a ≠ 0`. -/
theorem canonicalDelta_pow_rank (p : ℕ) (a : ℚ) (ha : a ≠ 0) (d j : ℕ) :
    Module.finrank ℚ (Submodule.map (canonicalDelta p a ^ j) (degreeLT ℚ (d + 1))) =
      d + 1 - j * (p + 1) :=
  ((canonicalDelta_exactShift p a ha).pow j).finrank_map d

/-- The image of `V_d` under `N^j` is exactly `V_{d - j(p+1)}`. -/
theorem canonicalDelta_pow_image (p : ℕ) (a : ℚ) (ha : a ≠ 0) (d j : ℕ) :
    Submodule.map (canonicalDelta p a ^ j) (degreeLT ℚ (d + 1)) =
      degreeLT ℚ (d + 1 - j * (p + 1)) :=
  ((canonicalDelta_exactShift p a ha).pow j).map_degreeLT d

/-- `dim (V_d ∩ ker N^j) = min (j (p+1)) (d + 1)`; for `j = 1` there are
`min (p+1) (d+1)` Jordan chains. -/
theorem canonicalDelta_pow_ker_rank (p : ℕ) (a : ℚ) (ha : a ≠ 0) (d j : ℕ) :
    Module.finrank ℚ (degreeLT ℚ (d + 1) ⊓ LinearMap.ker (canonicalDelta p a ^ j) :
      Submodule ℚ ℚ[X]) = min (j * (p + 1)) (d + 1) :=
  ((canonicalDelta_exactShift p a ha).pow j).finrank_ker d

theorem canonicalDelta_ker_rank (p : ℕ) (a : ℚ) (ha : a ≠ 0) (d : ℕ) :
    Module.finrank ℚ (degreeLT ℚ (d + 1) ⊓ LinearMap.ker (canonicalDelta p a) :
      Submodule ℚ ℚ[X]) = min (p + 1) (d + 1) :=
  (canonicalDelta_exactShift p a ha).finrank_ker d

/-- `N^j` vanishes on `V_d` exactly when `d < j (p + 1)`. -/
theorem canonicalDelta_pow_vanish_iff (p : ℕ) (a : ℚ) (ha : a ≠ 0) (d j : ℕ) :
    (∀ P ∈ degreeLT ℚ (d + 1), (canonicalDelta p a ^ j) P = 0) ↔ d < j * (p + 1) :=
  ((canonicalDelta_exactShift p a ha).pow j).vanish_iff d

/-- The nilpotency index of `N` on `V_d` is `d / (p + 1) + 1`. -/
theorem canonicalDelta_nilpotency_index (p : ℕ) (a : ℚ) (ha : a ≠ 0) (d : ℕ) :
    (∀ P ∈ degreeLT ℚ (d + 1), (canonicalDelta p a ^ (d / (p + 1) + 1)) P = 0) ∧
      ¬ (∀ P ∈ degreeLT ℚ (d + 1), (canonicalDelta p a ^ (d / (p + 1))) P = 0) := by
  rw [canonicalDelta_pow_vanish_iff p a ha, canonicalDelta_pow_vanish_iff p a ha]
  refine ⟨?_, ?_⟩
  · have := Nat.lt_div_mul_add (a := d) (Nat.succ_pos p)
    nlinarith [Nat.div_add_mod d (p + 1), Nat.mod_lt d (Nat.succ_pos p)]
  · have := Nat.div_mul_le_self d (p + 1)
    omega

/-- **Jordan chain count**: the number of Jordan chains of length `≥ j + 1`, which is
`rank N^j - rank N^(j+1)` on `V_d`, equals the number of residues `r ≤ p` whose
chain length `ℓ_r = ⌊(d - r)/(p+1)⌋ + 1` (`chainLength`) is at least `j + 1`. -/
theorem canonicalDelta_chain_count (p : ℕ) (a : ℚ) (ha : a ≠ 0) (d j : ℕ) :
    Module.finrank ℚ (Submodule.map (canonicalDelta p a ^ j) (degreeLT ℚ (d + 1))) -
        Module.finrank ℚ (Submodule.map (canonicalDelta p a ^ (j + 1)) (degreeLT ℚ (d + 1))) =
      ((Finset.range (p + 1)).filter fun r => j + 1 ≤ chainLength p d r).card := by
  rw [canonicalDelta_pow_rank p a ha, canonicalDelta_pow_rank p a ha]
  have hfilter : ((Finset.range (p + 1)).filter fun r => j + 1 ≤ chainLength p d r) =
      Finset.range (min (p + 1) (d + 1 - j * (p + 1))) := by
    ext r
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    unfold chainLength
    split_ifs with hr
    · rw [Nat.add_le_add_iff_right, Nat.le_div_iff_mul_le (by omega : 0 < p + 1)]
      omega
    · omega
  rw [hfilter, Finset.card_range]
  rw [Nat.succ_mul]
  omega

/-- The example of section 5: `p = 3, d = 11` gives ranks `12, 8, 4, 0`. -/
theorem rank_example_p3_d11 (a : ℚ) (ha : a ≠ 0) :
    (List.range 4).map (fun j =>
      Module.finrank ℚ (Submodule.map (canonicalDelta 3 a ^ j) (degreeLT ℚ 12))) =
      [12, 8, 4, 0] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  rw [show (12 : ℕ) = 11 + 1 from rfl]
  simp only [canonicalDelta_pow_rank 3 a ha 11]

#print axioms OrbitTrace.canonicalDelta_exactShift
#print axioms OrbitTrace.canonicalDelta_pow_rank
#print axioms OrbitTrace.canonicalDelta_pow_ker_rank
#print axioms OrbitTrace.canonicalDelta_nilpotency_index
#print axioms OrbitTrace.canonicalDelta_chain_count

end OrbitTrace
