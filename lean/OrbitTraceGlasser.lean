import OrbitTraceBoole

/-!
# Glasser's master theorem (orbit-trace section 3, general `S_m`)

Section 3 of `docs/research/2026-11-04-orbit-trace-integrals.md` states, by hand, that for
real poles `a_1 < ⋯ < a_{m-1}`, positive residues `b_j` and any `c`, the map
`S_m(x) = x + c - Σ_j b_j/(x - a_j)` preserves Lebesgue measure (statement (C)).
`OrbitTraceBoole.lean` proves the cases `m = 2` (Boole) and `m = 3` (the map of
section 1). This module proves the general statement, known as Glasser's master theorem.

* `glasser a b c` is the map, with `n` poles `a : Fin n → ℝ`; `gap a k`
  (`k : Fin (n + 1)`) are the open intervals between consecutive poles.
* `glasser_surj_gap`: on each gap the map is onto `ℝ`. It tends to `-∞` at the left end
  (`-∞` or just right of a pole) and to `+∞` at the right end, so the intermediate value
  theorem applies.
* `glasser_branch_sum`: the `n + 1` preimages of `t` sum to `t - c + Σ_j a_j`. Clearing
  denominators gives a monic polynomial of degree `n + 1` with these distinct roots
  (`glasser_root`); `sum_eq_of_roots` compares the coefficient of `X^n`.
* `glasser_measurePreserving` / `glasser_integral`: with increasing poles and positive
  residues, the map preserves Lebesgue measure, and `∫ g ∘ S = ∫ g` for every a.e. strongly
  measurable `g`. The `_of_injective` versions allow distinct poles in any order
  (sorted by `Tuple.sort`).
* `S3_eq_glasser`, `boole_eq_glasser`: the maps of `OrbitTraceBoole.lean` are instances.
* `not_measurePreserving_negative_residue`: the positivity of the residues is needed;
  `x + 1/x` (residue `-1`) misses `(-2, 2)` and is not measure preserving.
-/
namespace OrbitTrace

open MeasureTheory Set Filter Topology Polynomial

variable {n : ℕ} (a b : Fin n → ℝ) (c : ℝ)

/-- Glasser's map `x + c - Σ_j b_j/(x - a_j)`. -/
noncomputable def glasser (x : ℝ) : ℝ := x + c - ∑ j, b j / (x - a j)

/-- Its derivative `1 + Σ_j b_j/(x - a_j)²` away from the poles. -/
noncomputable def glasserDeriv (x : ℝ) : ℝ := 1 + ∑ j, b j / (x - a j) ^ 2

/-- The `k`-th gap between consecutive poles (`k = 0` and `k = n` are the unbounded ones). -/
def gap (k : Fin (n + 1)) : Set ℝ :=
  {x | ∀ j : Fin n, ((j : ℕ) < k → a j < x) ∧ ((k : ℕ) ≤ j → x < a j)}

variable {a b c}

theorem glasser_hasDerivAt {x : ℝ} (hx : ∀ j, x ≠ a j) :
    HasDerivAt (glasser a b c) (glasserDeriv a b x) x := by
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin n)), HasDerivAt (fun y => b j / (y - a j))
      (-(b j / (x - a j) ^ 2)) x := fun j _ => by
    have h := (((hasDerivAt_id x).sub_const (a j)).inv (sub_ne_zero.mpr (hx j))).const_mul (b j)
    convert h using 1
    · funext y; simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]
  have hs := HasDerivAt.sum hj
  have h := ((hasDerivAt_id x).add_const c).sub hs
  unfold glasser glasserDeriv
  convert h using 1
  · funext y; simp
  · simp [Finset.sum_neg_distrib]

theorem glasserDeriv_pos (hb : ∀ j, 0 < b j) (x : ℝ) : 0 < glasserDeriv a b x := by
  unfold glasserDeriv
  have : 0 ≤ ∑ j, b j / (x - a j) ^ 2 :=
    Finset.sum_nonneg fun j _ => div_nonneg (hb j).le (sq_nonneg _)
  linarith

theorem gap_isOpen (k : Fin (n + 1)) : IsOpen (gap a k) := by
  have : gap a k = ⋂ j : Fin n, {x | ((j : ℕ) < k → a j < x) ∧ ((k : ℕ) ≤ j → x < a j)} := by
    ext x; simp [gap]
  rw [this]
  refine isOpen_iInter_of_finite fun j => ?_
  by_cases h : (j : ℕ) < k
  · have e : {x | ((j : ℕ) < k → a j < x) ∧ ((k : ℕ) ≤ j → x < a j)} = Ioi (a j) := by
      ext x; simp only [mem_ofPred_eq, mem_Ioi]; constructor
      · exact fun hx => hx.1 h
      · exact fun hx => ⟨fun _ => hx, fun h' => absurd h (not_lt.mpr h')⟩
    rw [e]; exact isOpen_Ioi
  · have e : {x | ((j : ℕ) < k → a j < x) ∧ ((k : ℕ) ≤ j → x < a j)} = Iio (a j) := by
      ext x; simp only [mem_ofPred_eq, mem_Iio]; constructor
      · exact fun hx => hx.2 (not_lt.mp h)
      · exact fun hx => ⟨fun h' => absurd h' h, fun _ => hx⟩
    rw [e]; exact isOpen_Iio

instance gap_ordConnected (k : Fin (n + 1)) : OrdConnected (gap a k) :=
  ⟨fun _ hx _ hy _ hz => fun j =>
    ⟨fun h => lt_of_lt_of_le ((hx j).1 h) hz.1, fun h => lt_of_le_of_lt hz.2 ((hy j).2 h)⟩⟩

theorem ne_of_mem_gap {k : Fin (n + 1)} {x : ℝ} (hx : x ∈ gap a k) (j : Fin n) : x ≠ a j := by
  intro h
  rcases lt_or_ge (j : ℕ) k with hj | hj
  · exact absurd ((hx j).1 hj) (by rw [h]; exact lt_irrefl _)
  · exact absurd ((hx j).2 hj) (by rw [h]; exact lt_irrefl _)

theorem gap_disjoint {k l : Fin (n + 1)} (hkl : k ≠ l) : Disjoint (gap a k) (gap a l) := by
  have key : ∀ {k l : Fin (n + 1)}, (k : ℕ) < l → Disjoint (gap a k) (gap a l) := by
    intro k l h
    rw [Set.disjoint_left]
    intro x hk hl
    have hkn : (k : ℕ) < n := lt_of_lt_of_le h (Nat.lt_succ_iff.mp l.2)
    have h1 := (hk ⟨k, hkn⟩).2 le_rfl
    have h2 := (hl ⟨k, hkn⟩).1 h
    exact lt_asymm h1 h2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with h | h
  · exact key h
  · exact (key h).symm

theorem exists_mem_gap (ha : Monotone a) {x : ℝ} (hx : ∀ j, x ≠ a j) :
    ∃ k : Fin (n + 1), x ∈ gap a k := by
  classical
  let P : ℕ → Prop := fun m => m = n ∨ ∃ h : m < n, x < a ⟨m, h⟩
  have hP : ∃ m, P m := ⟨n, Or.inl rfl⟩
  let k := Nat.find hP
  have hkn : k ≤ n := Nat.find_min' hP (Or.inl rfl)
  refine ⟨⟨k, Nat.lt_succ_of_le hkn⟩, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
  · have hnot : ¬ P j := Nat.find_min hP hj
    simp only [P, not_or, not_exists, not_lt] at hnot
    exact lt_of_le_of_ne (hnot.2 j.2) (hx j).symm
  · have hk : P k := Nat.find_spec hP
    rcases hk with hk | ⟨hk, hlt⟩
    · exact absurd j.2 (by simp only at hj; omega)
    · exact lt_of_lt_of_le hlt (ha (Fin.mk_le_mk.mpr hj))

theorem tendsto_sum_poles_zero {l : Filter ℝ}
    (hshift : ∀ j : Fin n, Tendsto (fun x => (x - a j)⁻¹) l (𝓝 0)) :
    Tendsto (fun x => ∑ j, b j / (x - a j)) l (𝓝 0) := by
  have := tendsto_finsetSum (Finset.univ : Finset (Fin n))
    fun j _ => (hshift j).const_mul (b j)
  simpa [div_eq_mul_inv] using this

theorem tendsto_glasser_atBot : Tendsto (glasser a b c) atBot atBot := by
  have hs : Tendsto (fun x => ∑ j, b j / (x - a j)) atBot (𝓝 0) :=
    tendsto_sum_poles_zero fun j =>
      tendsto_inv_atBot_zero.comp (tendsto_atBot_add_const_right _ (-a j) tendsto_id)
  have h := (tendsto_atBot_add_const_right _ c tendsto_id).atBot_add hs.neg
  convert h using 1
  funext x; simp [glasser, sub_eq_add_neg]

theorem tendsto_glasser_atTop : Tendsto (glasser a b c) atTop atTop := by
  have hs : Tendsto (fun x => ∑ j, b j / (x - a j)) atTop (𝓝 0) :=
    tendsto_sum_poles_zero fun j =>
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-a j) tendsto_id)
  have h := (tendsto_atTop_add_const_right _ c tendsto_id).atTop_add hs.neg
  convert h using 1
  funext x; simp [glasser, sub_eq_add_neg]

/-- Splitting off the pole `a j`. -/
theorem glasser_eq_split (ha : Function.Injective a) (j : Fin n) :
    ∃ H : ℝ → ℝ, ContinuousAt H (a j) ∧ ∀ x, glasser a b c x = H x - b j * (x - a j)⁻¹ := by
  classical
  refine ⟨fun x => x + c - ∑ i ∈ Finset.univ.erase j, b i / (x - a i), ?_, fun x => ?_⟩
  · have hsum : ContinuousAt (fun x : ℝ => ∑ i ∈ Finset.univ.erase j, b i / (x - a i)) (a j) := by
      refine tendsto_finsetSum _ fun i hi => ?_
      have hne : a j - a i ≠ 0 :=
        sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hi) (ha h).symm
      exact continuousAt_const.div (continuousAt_id.sub continuousAt_const) hne
    exact ContinuousAt.sub (ContinuousAt.add continuousAt_id continuousAt_const) hsum
  · simp only [glasser]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), div_eq_mul_inv]
    ring

theorem tendsto_glasser_right_of_pole (ha : Function.Injective a) (hb : ∀ j, 0 < b j)
    (j : Fin n) : Tendsto (glasser a b c) (𝓝[>] a j) atBot := by
  obtain ⟨H, hH, hsplit⟩ := glasser_eq_split (b := b) (c := c) ha j
  have hsub : Tendsto (fun x => x - a j) (𝓝[>] a j) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
    · have : Tendsto (fun x => x - a j) (𝓝 (a j)) (𝓝 (a j - a j)) :=
        (continuous_sub_right (a j)).tendsto (a j)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact sub_pos.mpr (show a j < x from hx)
  have hinv := (tendsto_inv_nhdsGT_zero.comp hsub).const_mul_atTop (hb j)
  have h := (hH.tendsto.mono_left nhdsWithin_le_nhds).add_atBot (tendsto_neg_atTop_atBot.comp hinv)
  convert h using 1
  funext x; simp [hsplit, sub_eq_add_neg]

theorem tendsto_glasser_left_of_pole (ha : Function.Injective a) (hb : ∀ j, 0 < b j)
    (j : Fin n) : Tendsto (glasser a b c) (𝓝[<] a j) atTop := by
  obtain ⟨H, hH, hsplit⟩ := glasser_eq_split (b := b) (c := c) ha j
  have hsub : Tendsto (fun x => x - a j) (𝓝[<] a j) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
    · have : Tendsto (fun x => x - a j) (𝓝 (a j)) (𝓝 (a j - a j)) :=
        (continuous_sub_right (a j)).tendsto (a j)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact sub_neg.mpr (show x < a j from hx)
  have hinv := (tendsto_inv_nhdsLT_zero.comp hsub).const_mul_atBot (hb j)
  have h := (hH.tendsto.mono_left nhdsWithin_le_nhds).add_atTop (tendsto_neg_atBot_atTop.comp hinv)
  convert h using 1
  funext x; simp [hsplit, sub_eq_add_neg]

theorem exists_mem_gap_lt (ha : StrictMono a) (hb : ∀ j, 0 < b j) (k : Fin (n + 1)) (t : ℝ) :
    ∃ x ∈ gap a k, glasser a b c x < t := by
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk | hk
  · have hev : ∀ᶠ x in atBot, x ∈ gap a k := by
      refine eventually_all.mpr fun j => ?_
      filter_upwards [eventually_lt_atBot (a j)] with x hx
      exact ⟨fun h => absurd h (by omega), fun _ => hx⟩
    exact (hev.and (tendsto_glasser_atBot.eventually (eventually_lt_atBot t))).exists
  · have hm : (k : ℕ) - 1 < n := by have := k.2; omega
    set j0 : Fin n := ⟨(k : ℕ) - 1, hm⟩
    have hev : ∀ᶠ x in 𝓝[>] a j0, x ∈ gap a k := by
      refine eventually_all.mpr fun j => ?_
      by_cases hj : (j : ℕ) < k
      · filter_upwards [self_mem_nhdsWithin] with x (hx : a j0 < x)
        refine ⟨fun _ => lt_of_le_of_lt (ha.monotone (Fin.le_iff_val_le_val.mpr ?_)) hx,
          fun h => absurd hj (not_lt.mpr h)⟩
        show (j : ℕ) ≤ (k : ℕ) - 1
        omega
      · have hlt : a j0 < a j := ha (Fin.lt_def.mpr (show (k : ℕ) - 1 < j by omega))
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with x (hx : x < a j)
        exact ⟨fun h => absurd h hj, fun _ => hx⟩
    exact (hev.and ((tendsto_glasser_right_of_pole ha.injective hb j0).eventually
      (eventually_lt_atBot t))).exists

theorem exists_mem_gap_gt (ha : StrictMono a) (hb : ∀ j, 0 < b j) (k : Fin (n + 1)) (t : ℝ) :
    ∃ x ∈ gap a k, t < glasser a b c x := by
  rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp k.2) with hk | hk
  · have hev : ∀ᶠ x in atTop, x ∈ gap a k := by
      refine eventually_all.mpr fun j => ?_
      filter_upwards [eventually_gt_atTop (a j)] with x hx
      exact ⟨fun _ => hx, fun h => absurd j.2 (by omega)⟩
    exact (hev.and (tendsto_glasser_atTop.eventually (eventually_gt_atTop t))).exists
  · set j0 : Fin n := ⟨k, hk⟩
    have hev : ∀ᶠ x in 𝓝[<] a j0, x ∈ gap a k := by
      refine eventually_all.mpr fun j => ?_
      by_cases hj : (j : ℕ) < k
      · have hlt : a j < a j0 := ha (Fin.lt_def.mpr (show (j : ℕ) < k from hj))
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt)] with x (hx : a j < x)
        exact ⟨fun _ => hx, fun h => absurd hj (not_lt.mpr h)⟩
      · filter_upwards [self_mem_nhdsWithin] with x (hx : x < a j0)
        exact ⟨fun h => absurd h hj,
          fun h => lt_of_lt_of_le hx (ha.monotone (Fin.le_iff_val_le_val.mpr (show (k : ℕ) ≤ j from h)))⟩
    exact (hev.and ((tendsto_glasser_left_of_pole ha.injective hb j0).eventually
      (eventually_gt_atTop t))).exists

theorem glasser_surj_gap (ha : StrictMono a) (hb : ∀ j, 0 < b j) (k : Fin (n + 1)) (t : ℝ) :
    ∃ x ∈ gap a k, glasser a b c x = t := by
  obtain ⟨p, hp, hpt⟩ := exists_mem_gap_lt (c := c) ha hb k t
  obtain ⟨q, hq, hqt⟩ := exists_mem_gap_gt (c := c) ha hb k t
  have hsub : uIcc p q ⊆ gap a k := (gap_ordConnected k).uIcc_subset hp hq
  have hcont : ContinuousOn (glasser a b c) (uIcc p q) := fun x hx =>
    (glasser_hasDerivAt (ne_of_mem_gap (hsub hx))).continuousAt.continuousWithinAt
  obtain ⟨x, hx, hxt⟩ := intermediate_value_uIcc hcont
    (show t ∈ uIcc (glasser a b c p) (glasser a b c q) from
      Set.mem_uIcc.mpr (Or.inl ⟨hpt.le, hqt.le⟩))
  exact ⟨x, hsub hx, hxt⟩

/-- **Vieta for a monic polynomial with all roots given**: if `Π_i (X - α_i) - R`
(`deg R < m`) vanishes at `m + 1` distinct points `r_k`, then `Σ r_k = Σ α_i`. -/
theorem sum_eq_of_roots {m : ℕ} (α : Fin (m + 1) → ℝ) (R : ℝ[X]) (hR : R.degree < m)
    (r : Fin (m + 1) → ℝ) (hr : Function.Injective r)
    (hroot : ∀ k, (∏ i, (X - C (α i)) - R).eval (r k) = 0) : ∑ k, r k = ∑ i, α i := by
  classical
  set Q : ℝ[X] := ∏ i, (X - C (α i)) with hQ
  set P : ℝ[X] := Q - R with hP
  have hQm : Q.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (α i)
  have hQdeg : Q.natDegree = m + 1 := by
    rw [hQ, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (α i)]
    simp
  have hRQ : R.degree < Q.degree := by
    rw [degree_eq_natDegree hQm.ne_zero, hQdeg]
    exact lt_trans hR (by exact_mod_cast Nat.lt_succ_self m)
  have hPm : P.Monic := hQm.sub_of_left hRQ
  have hPdeg : P.natDegree = m + 1 := by
    rw [hP, natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hRQ), hQdeg]
  have hP0 : P ≠ 0 := hPm.ne_zero
  -- the given points are all the roots
  have hle : (Finset.univ.val.map r) ≤ P.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hr Finset.univ.nodup)]
    intro x hx
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hx
    exact (mem_roots hP0).mpr (hroot k)
  have hcard : Multiset.card (Finset.univ.val.map r) = m + 1 := by simp
  have hroots : Finset.univ.val.map r = P.roots :=
    Multiset.eq_of_le_of_card_le hle (by rw [hcard, ← hPdeg]; exact card_roots' P)
  have hsplit : (P.roots.map fun x => X - C x).prod = P :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm (by rw [← hroots, hcard, hPdeg])
  have hPprod : P = ∏ k, (X - C (r k)) := by
    rw [← hsplit, ← hroots, Multiset.map_map]
    rfl
  -- compare the coefficients of `X^m`
  have h1 : P.coeff m = -∑ k, r k := by
    have := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (m + 1))) r (by simp)
    simpa [hPprod] using this
  have h2 : P.coeff m = -∑ i, α i := by
    have := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (m + 1))) α (by simp)
    rw [hP, coeff_sub, coeff_eq_zero_of_degree_lt hR, sub_zero]
    simpa using this
  linarith

/-- The remainder `Σ_j b_j Π_{i ≠ j} (X - a_i)` of Glasser's equation cleared of denominators. -/
noncomputable def glasserRem (a b : Fin n → ℝ) : ℝ[X] :=
  ∑ j, C (b j) * ∏ i ∈ Finset.univ.erase j, (X - C (a i))

theorem glasserRem_degree_lt (a b : Fin n → ℝ) : (glasserRem a b).degree < n := by
  classical
  unfold glasserRem
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (Ne.bot_lt (by simp))).mpr fun j _ => ?_
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  have hprod : (∏ i ∈ Finset.univ.erase j, (X - C (a i))).degree = ((n - 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (a i)).ne_zero,
      natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (a i)]
    simp [Finset.card_erase_of_mem]
  rw [hprod]
  have hn : 0 < n := j.pos
  refine lt_of_le_of_lt (add_le_add_left degree_C_le _) ?_
  rw [zero_add]
  exact_mod_cast (show n - 1 < n by omega)

theorem glasser_root {x t : ℝ} (hx : ∀ j, x ≠ a j) (h : glasser a b c x = t) :
    (∏ i, (X - C ((Fin.cons (t - c) a : Fin (n + 1) → ℝ) i)) - glasserRem a b).eval x = 0 := by
  classical
  have hne : ∀ j, x - a j ≠ 0 := fun j => sub_ne_zero.mpr (hx j)
  rw [eval_sub, eval_prod, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, eval_sub, eval_X, eval_C, glasserRem, eval_finsetSum,
    eval_mul, eval_prod]
  have key : ∀ j, b j * ∏ i ∈ Finset.univ.erase j, (x - a i) =
      b j / (x - a j) * ∏ i, (x - a i) := fun j => by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    field_simp [hne j]
  simp only [key, ← Finset.sum_mul]
  unfold glasser at h
  have : x - (t - c) = ∑ j, b j / (x - a j) := by linarith
  rw [this, sub_self]

theorem glasser_branch_sum {r : Fin (n + 1) → ℝ} (hr : Function.Injective r) (t : ℝ)
    (hx : ∀ k j, r k ≠ a j) (h : ∀ k, glasser a b c (r k) = t) :
    ∑ k, r k = t - c + ∑ j, a j := by
  rw [sum_eq_of_roots (Fin.cons (t - c) a) (glasserRem a b) (glasserRem_degree_lt a b) r hr
    fun k => glasser_root (hx k) (h k), Fin.sum_univ_succ]
  simp

/-- **Inverse branches of Glasser's map**, one on each gap. -/
theorem glasser_branches (ha : StrictMono a) (hb : ∀ j, 0 < b j) : ∃ r : Fin (n + 1) → ℝ → ℝ,
    (∀ k t, HasDerivAt (r k) (glasserDeriv a b (r k t))⁻¹ t) ∧
    (∀ k t, glasser a b c (r k t) = t) ∧
    Pairwise (Function.onFun Disjoint fun k => Set.range (r k)) ∧
    volume (⋃ k, Set.range (r k))ᶜ = 0 ∧ ∀ t, ∑ k, (glasserDeriv a b (r k t))⁻¹ = 1 := by
  have hex := fun k : Fin (n + 1) => exists_inverse_branch (I := gap a k) (gap_isOpen k)
    (glasser a b c) (glasserDeriv a b) (fun x hx => glasser_hasDerivAt (ne_of_mem_gap hx))
    (fun x _ => glasserDeriv_pos hb x) (glasser_surj_gap ha hb k)
  choose r hmem hinv hleft hderiv using hex
  have hinj : ∀ t, Function.Injective fun k => r k t := by
    intro t k l hkl
    by_contra hne
    exact Set.disjoint_left.mp (gap_disjoint hne) (hmem k t) (by simp only at hkl; rw [hkl]; exact hmem l t)
  have hsum_eq : ∀ t, ∑ k, r k t = t - c + ∑ j, a j := fun t =>
    glasser_branch_sum (hinj t) t (fun k j => ne_of_mem_gap (hmem k t) j) fun k => hinv k t
  refine ⟨r, hderiv, hinv, ?_, ?_, ?_⟩
  · intro k l hkl
    exact (gap_disjoint hkl).mono (Set.range_subset_iff.mpr (hmem k))
      (Set.range_subset_iff.mpr (hmem l))
  · refine measure_mono_null (t := Set.range a) ?_ ((Set.finite_range a).measure_zero volume)
    intro x hx
    by_contra hxa
    have hxa' : ∀ j, x ≠ a j := fun j h => hxa ⟨j, h.symm⟩
    obtain ⟨k, hk⟩ := exists_mem_gap ha.monotone hxa'
    exact hx (Set.mem_iUnion.mpr ⟨k, glasser a b c x, hleft k x hk⟩)
  · intro t
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hderiv k t
    have hid : (fun t => ∑ k ∈ Finset.univ, r k t) = fun t => t + (-c + ∑ j, a j) := by
      funext t; rw [hsum_eq]; ring
    rw [hid] at h
    exact h.unique ((hasDerivAt_id t).add_const _) |>.trans (by simp)

theorem glasser_measurable : Measurable (glasser a b c) := by
  unfold glasser; fun_prop

/-- **Glasser's master theorem** (measure-preserving form): for increasing poles `a_j` and
positive residues `b_j`, `x ↦ x + c - Σ_j b_j/(x - a_j)` preserves Lebesgue measure. -/
theorem glasser_measurePreserving (ha : StrictMono a) (hb : ∀ j, 0 < b j) :
    MeasurePreserving (glasser a b c) volume volume := by
  obtain ⟨r, hd, hinv, hdisj, hnull, hsum⟩ := glasser_branches (c := c) ha hb
  exact measurePreserving_of_branches _ glasser_measurable r _ hd
    (fun k t => (inv_pos.mpr (glasserDeriv_pos hb _)).le) hinv hdisj hnull hsum

/-- **Glasser's master theorem**: `∫ g (x + c - Σ_j b_j/(x - a_j)) dx = ∫ g x dx` for every
(a.e. strongly) measurable `g`; both sides are `0` together when `g` is not integrable. -/
theorem glasser_integral (ha : StrictMono a) (hb : ∀ j, 0 < b j) (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g volume) :
    ∫ x, g (glasser a b c x) = ∫ x, g x := by
  have hmp := glasser_measurePreserving (c := c) ha hb
  rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hg), hmp.map_eq]

theorem glasser_comp_perm (σ : Equiv.Perm (Fin n)) :
    glasser (a ∘ σ) (b ∘ σ) c = glasser a b c := by
  funext x
  simp only [glasser, Function.comp_apply]
  rw [Equiv.sum_comp σ (fun j => b j / (x - a j))]

/-- **Glasser's master theorem for distinct poles in any order.** -/
theorem glasser_measurePreserving_of_injective (ha : Function.Injective a)
    (hb : ∀ j, 0 < b j) : MeasurePreserving (glasser a b c) volume volume := by
  set σ := Tuple.sort a
  have hmono : StrictMono (a ∘ σ) :=
    (Tuple.monotone_sort a).strictMono_of_injective (ha.comp σ.injective)
  rw [← glasser_comp_perm σ]
  exact glasser_measurePreserving hmono fun j => hb (σ j)

theorem glasser_integral_of_injective (ha : Function.Injective a) (hb : ∀ j, 0 < b j)
    (g : ℝ → ℝ) (hg : AEStronglyMeasurable g volume) :
    ∫ x, g (glasser a b c x) = ∫ x, g x := by
  have hmp := glasser_measurePreserving_of_injective (c := c) ha hb
  rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hg), hmp.map_eq]

/-- The map of section 1 is Glasser's map with poles `0, 1`, residues `1, 1` and `c = 1`. -/
theorem S3_eq_glasser : S3 = glasser ![0, 1] ![1, 1] 1 := by
  funext x
  simp [S3, glasser, Fin.sum_univ_two]
  ring

/-- Boole's map is Glasser's map with one pole at `0`, residue `1` and `c = 0`. -/
theorem boole_eq_glasser : (fun x : ℝ => x - 1 / x) = glasser ![0] ![1] 0 := by
  funext x
  simp [glasser]

/-- **The positivity of the residues is necessary**: with residue `-1` (`b = -1`),
`x ↦ x + 1/x = glasser ![0] ![-1] 0` does not preserve Lebesgue measure, since it never takes
values in `(-2, 2)` away from the pole (`|x + 1/x| ≥ 2`). -/
theorem not_measurePreserving_negative_residue :
    ¬ MeasurePreserving (glasser ![(0 : ℝ)] ![-1] 0) volume volume := by
  intro h
  have hpre : glasser ![(0 : ℝ)] ![-1] 0 ⁻¹' Ioo (-2) 2 ⊆ {0} := by
    intro x hx
    simp only [mem_preimage, mem_Ioo, glasser, Fin.sum_univ_one, Matrix.cons_val_zero, sub_zero,
      add_zero] at hx
    by_contra hx0
    have hx0' : x ≠ 0 := hx0
    have e : x - -1 / x = x + 1 / x := by ring
    rw [e] at hx
    rcases lt_or_gt_of_ne hx0' with hneg | hpos
    · have h1 : x + 1 / x + 2 = (x + 1) ^ 2 / x := by field_simp; ring
      have h2 : (x + 1) ^ 2 / x ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg.le
      linarith [hx.1]
    · have h1 : x + 1 / x - 2 = (x - 1) ^ 2 / x := by field_simp; ring
      have h2 : 0 ≤ (x - 1) ^ 2 / x := div_nonneg (sq_nonneg _) hpos.le
      linarith [hx.2]
  have hmeas := h.measure_preimage (s := Ioo (-2 : ℝ) 2) measurableSet_Ioo.nullMeasurableSet
  have h0 : volume (glasser ![(0 : ℝ)] ![-1] 0 ⁻¹' Ioo (-2) 2) = 0 :=
    measure_mono_null hpre (measure_singleton 0)
  rw [h0, Real.volume_Ioo] at hmeas
  norm_num at hmeas

end OrbitTrace

#print axioms OrbitTrace.glasser_surj_gap
#print axioms OrbitTrace.glasser_branch_sum
#print axioms OrbitTrace.sum_eq_of_roots
#print axioms OrbitTrace.glasser_branches
#print axioms OrbitTrace.glasser_measurePreserving
#print axioms OrbitTrace.glasser_integral
#print axioms OrbitTrace.glasser_measurePreserving_of_injective
#print axioms OrbitTrace.glasser_integral_of_injective
#print axioms OrbitTrace.S3_eq_glasser
#print axioms OrbitTrace.boole_eq_glasser
#print axioms OrbitTrace.not_measurePreserving_negative_residue
