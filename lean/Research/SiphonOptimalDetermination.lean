import Research.SiphonFiniteDetermination

/-!
# The optimal number of siphon measurements is `(d+1)(d+2)/2`

`docs/research/2026-11-17-siphon-finite-determination.md` proves in Lean
(`Research/SiphonFiniteDetermination.lean`) that at most `(d+1)(3d+1)` reachable points
determine every real polynomial in two variables of total degree at most `d`. It proves only
by hand that exactly `N(d) = (d+1)(d+2)/2` points suffice and that fewer never do. This module
formalizes both statements.

* `finrank_V`: the space `V d` of polynomials of total degree `≤ d` in `u, v` has dimension
  `N(d)` (`card_expSet`: the exponents `i + j ≤ d` are counted by antidiagonals).
* `exists_vanishing_of_card_lt`, `not_determining_of_card_lt`: for any `T` with fewer than
  `N(d)` points, a nonzero polynomial of degree `≤ d` vanishes on `T` (kernel of the
  evaluation map), so `T` cannot determine.
* `adaptive_not_determining`: the same holds for adaptive strategies (the next point may
  depend on the previous answers): the nonzero polynomial vanishing on the points chosen for
  the zero polynomial produces the same transcript.
* `exists_optimal_determining_set`: from any nonzero seed, exactly `N(d)` of the reachable
  points `E^m L E^n` of the existing theorem determine. The point evaluations at the existing
  determining set separate `V d`, so they span its dual
  (`Submodule.span_eq_top_of_ne_zero`); a linearly independent subfamily
  (`exists_linearIndependent'`) is a basis of the dual, of size `N(d)`.
* `minimum_is_N` packages the two directions; `no_uniform_finite_cutoff`: no finite set of
  readings determines polynomials of unbounded degree.

The choice of the `N(d)` points depends on the seed; no seed-independent fixed set of
operation words is claimed, matching the note.
-/
namespace SiphonOptimalDetermination

open MvPolynomial

noncomputable section

/-- `N(d) = (d+1)(d+2)/2`, the number of monomials `u^i v^j` with `i + j ≤ d`. -/
def N (d : ℕ) : ℕ := (d + 1) * (d + 2) / 2

/-- The exponent set `{(i, j) : i + j ≤ d}` as a finset of `ℕ × ℕ`. -/
def expSet (d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (d + 1)).biUnion Finset.HasAntidiagonal.antidiagonal

theorem mem_expSet {d : ℕ} {p : ℕ × ℕ} : p ∈ expSet d ↔ p.1 + p.2 ≤ d := by
  simp only [expSet, Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨p.1 + p.2, by omega, rfl⟩

theorem card_expSet (d : ℕ) : (expSet d).card = N d := by
  rw [expSet, Finset.card_biUnion]
  · simp only [Finset.Nat.card_antidiagonal]
    rw [N]
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : 2 ∣ (d + 1) * (d + 2) := by
        rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
        · exact ⟨(2 * k + 1) * (k + 1), by ring⟩
        · exact ⟨(k + 1) * (2 * k + 3), by ring⟩
      obtain ⟨c, hc⟩ := h2
      have h3 : (d + 1 + 1) * (d + 1 + 2) = 2 * (c + (d + 2)) := by nlinarith [hc]
      rw [hc, h3, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
  · intro i _ j _ hij
    exact Finset.disjoint_left.mpr fun p hi hj => hij
      ((Finset.HasAntidiagonal.mem_antidiagonal.mp hi).symm.trans
        (Finset.HasAntidiagonal.mem_antidiagonal.mp hj))

/-- Polynomials in two variables (`false ↦ u`, `true ↦ v`) of total degree at most `d`. -/
abbrev V (d : ℕ) : Submodule ℝ (MvPolynomial Bool ℝ) := restrictTotalDegree Bool ℝ d

/-- The exponent set of `V d`. -/
def expSupport (d : ℕ) : Set (Bool →₀ ℕ) := {n | (n.sum fun _ e => e) ≤ d}

/-- `Bool →₀ ℕ ≃ ℕ × ℕ`, `n ↦ (n false, n true)`. -/
def finsuppEquiv : (Bool →₀ ℕ) ≃ ℕ × ℕ :=
  Finsupp.equivFunOnFinite.trans (Equiv.boolArrowEquivProd ℕ)

theorem finsupp_sum_bool (n : Bool →₀ ℕ) :
    (n.sum fun _ e => e) = (finsuppEquiv n).1 + (finsuppEquiv n).2 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_bool]
  simp [finsuppEquiv, Equiv.boolArrowEquivProd, add_comm]

/-- `expSupport d ≃ expSet d`. -/
def expEquiv (d : ℕ) : expSupport d ≃ expSet d where
  toFun n := ⟨finsuppEquiv n.1, mem_expSet.mpr (by rw [← finsupp_sum_bool]; exact n.2)⟩
  invFun p := ⟨finsuppEquiv.symm p.1, by
    show _ ≤ d
    rw [finsupp_sum_bool, Equiv.apply_symm_apply]; exact mem_expSet.mp p.2⟩
  left_inv n := by simp
  right_inv p := by simp

/-- **`dim V_d = (d+1)(d+2)/2`.** -/
theorem finrank_V (d : ℕ) : Module.finrank ℝ (V d) = N d := by
  rw [show V d = restrictSupport ℝ (expSupport d) from rfl,
    Module.finrank_eq_nat_card_basis (basisRestrictSupport ℝ (expSupport d)),
    Nat.card_congr (expEquiv d), Nat.card_eq_finsetCard, card_expSet]

instance (d : ℕ) : FiniteDimensional ℝ (V d) :=
  Module.finite_of_finrank_pos (by rw [finrank_V, N]; exact Nat.div_pos (by nlinarith) (by norm_num))

open SiphonFiniteDetermination

/-- Evaluation at a point, as a linear functional on `V d`. -/
def evalAt (d : ℕ) (x : ℝ × ℝ) : Module.Dual ℝ (V d) :=
  (MvPolynomial.aeval (fun i : Bool => if i then x.2 else x.1)).toLinearMap.comp (V d).subtype

theorem evalAt_apply (d : ℕ) (x : ℝ × ℝ) (p : V d) : evalAt d x p = readPoly p.1 x := by
  show MvPolynomial.aeval _ p.1 = MvPolynomial.eval _ p.1
  exact RingHom.congr_fun (MvPolynomial.coe_aeval_eq_eval _) p.1

/-- **Lower bound**: any set of fewer than `N(d)` points admits a nonzero polynomial of total
degree at most `d` vanishing on it. -/
theorem exists_vanishing_of_card_lt (d : ℕ) (T : Finset (ℝ × ℝ)) (hT : T.card < N d) :
    ∃ p : MvPolynomial Bool ℝ, p ≠ 0 ∧ p.totalDegree ≤ d ∧ ∀ x ∈ T, readPoly p x = 0 := by
  have hlt : Module.finrank ℝ (T → ℝ) < Module.finrank ℝ (V d) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, finrank_V]; exact hT
  obtain ⟨⟨p, hpV⟩, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := LinearMap.pi fun x : T => evalAt d x.1) hlt)
  refine ⟨p, fun h => hp0 (by simp [h]), (mem_restrictTotalDegree Bool d p).mp hpV,
    fun x hx => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hp) ⟨x, hx⟩
  rw [LinearMap.pi_apply, evalAt_apply] at this
  exact this

/-- Fewer than `N(d)` exact evaluations never determine all polynomials of degree `≤ d`. -/
theorem not_determining_of_card_lt (d : ℕ) (T : Finset (ℝ × ℝ)) (hT : T.card < N d) :
    ∃ p q : MvPolynomial Bool ℝ, p.totalDegree ≤ d ∧ q.totalDegree ≤ d ∧ p ≠ q ∧
      ∀ x ∈ T, readPoly p x = readPoly q x := by
  obtain ⟨p, hp, hd, hT⟩ := exists_vanishing_of_card_lt d T hT
  refine ⟨p, 0, hd, by simp, hp, fun x hx => ?_⟩
  rw [hT x hx]; simp [readPoly]

/-- An adaptive measurement strategy: the next point depends on the answers so far. -/
def transcript (strat : List ℝ → ℝ × ℝ) (p : MvPolynomial Bool ℝ) : ℕ → List ℝ
  | 0 => []
  | k + 1 => transcript strat p k ++ [readPoly p (strat (transcript strat p k))]

/-- **Adaptive lower bound**: no adaptive strategy with fewer than `N(d)` exact evaluations
distinguishes all polynomials of degree `≤ d`. -/
theorem adaptive_not_determining (d M : ℕ) (hM : M < N d) (strat : List ℝ → ℝ × ℝ) :
    ∃ p : MvPolynomial Bool ℝ, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      transcript strat p M = transcript strat 0 M := by
  classical
  let T : Finset (ℝ × ℝ) := (Finset.range M).image fun k => strat (transcript strat 0 k)
  have hT : T.card < N d := lt_of_le_of_lt (Finset.card_image_le.trans (by simp)) hM
  obtain ⟨p, hp, hd, hvan⟩ := exists_vanishing_of_card_lt d T hT
  refine ⟨p, hp, hd, ?_⟩
  have key : ∀ k ≤ M, transcript strat p k = transcript strat 0 k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have ih' := ih (by omega)
      simp only [transcript, ih']
      congr 2
      rw [hvan _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩)]
      simp [readPoly]
  exact key M le_rfl

/-- **Upper bound, attained**: from any nonzero seed, exactly `N(d)` reachable points
(of the form `E^m L E^n` applied to the regularized seed) determine every polynomial of
total degree at most `d`. -/
theorem exists_optimal_determining_set (z : ℝ × ℝ) (hz : z ≠ (0, 0)) (d : ℕ) :
    ∃ T : Finset (ℝ × ℝ), T.card = N d ∧
      (∀ x ∈ T, ∃ n < d + 2, ∃ m < 3 * d + 1, x = sample (regularSeed z) n m) ∧
      ∀ p q : MvPolynomial Bool ℝ, p.totalDegree ≤ d → q.totalDegree ≤ d →
        (∀ x ∈ T, readPoly p x = readPoly q x) → p = q := by
  classical
  obtain ⟨T0, -, hreach, hdet⟩ := exists_finite_determining_set z hz d
  let v : T0 → Module.Dual ℝ (V d) := fun x => evalAt d x.1
  -- the evaluations at `T0` span the dual of `V d`
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro r hr
    by_contra hall
    push Not at hall
    apply hr
    have hrd : r.1.totalDegree ≤ d := (mem_restrictTotalDegree Bool d r.1).mp r.2
    have h0 : r.1 = 0 := hdet r.1 0 hrd (by simp) fun x hx => by
      have := hall (v ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
      rw [evalAt_apply] at this
      rw [this]; simp [readPoly]
    exact Subtype.ext h0
  -- extract a basis of the dual among them
  obtain ⟨κ, a, ha, hspan', hli⟩ := exists_linearIndependent' ℝ v
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  let B : Module.Basis κ ℝ (Module.Dual ℝ (V d)) :=
    Module.Basis.mk hli (by rw [hspan', hspan])
  have hcard : Fintype.card κ = N d := by
    rw [← Module.finrank_eq_card_basis B, Subspace.dual_finrank_eq, finrank_V]
  refine ⟨Finset.univ.image fun k => (a k).1, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun k l h => ha (Subtype.ext h)), Finset.card_univ, hcard]
  · intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    exact hreach _ (a k).2
  · intro p q hp hq hpq
    have hr : (p - q).totalDegree ≤ d := (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq)
    let r : V d := ⟨p - q, (mem_restrictTotalDegree Bool d _).mpr hr⟩
    have hvan : ∀ φ : Module.Dual ℝ (V d), φ r = 0 := by
      intro φ
      have hφ : φ ∈ Submodule.span ℝ (Set.range (v ∘ a)) := by rw [hspan', hspan]; trivial
      refine Submodule.span_induction (p := fun φ _ => φ r = 0) ?_ (by simp)
        (fun _ _ _ _ h1 h2 => by simp [h1, h2]) (fun c _ _ h => by simp [h]) hφ
      rintro _ ⟨k, rfl⟩
      show evalAt d (a k).1 r = 0
      rw [evalAt_apply]
      have := hpq (a k).1 (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
      simp only [r, readPoly, map_sub] at this ⊢
      rw [this, sub_self]
    have : r = 0 := (Module.forall_dual_apply_eq_zero_iff ℝ r).mp hvan
    exact sub_eq_zero.mp (congrArg Subtype.val this)

/-- **The minimum number of exact evaluations is `N(d)`**: `N(d)` reachable points suffice,
and no set of fewer points (nor any adaptive strategy with fewer evaluations) does. -/
theorem minimum_is_N (z : ℝ × ℝ) (hz : z ≠ (0, 0)) (d : ℕ) :
    (∃ T : Finset (ℝ × ℝ), T.card = N d ∧
      ∀ p q : MvPolynomial Bool ℝ, p.totalDegree ≤ d → q.totalDegree ≤ d →
        (∀ x ∈ T, readPoly p x = readPoly q x) → p = q) ∧
    ∀ T : Finset (ℝ × ℝ), T.card < N d →
      ∃ p q : MvPolynomial Bool ℝ, p.totalDegree ≤ d ∧ q.totalDegree ≤ d ∧ p ≠ q ∧
        ∀ x ∈ T, readPoly p x = readPoly q x := by
  obtain ⟨T, hT, -, hdet⟩ := exists_optimal_determining_set z hz d
  exact ⟨⟨T, hT, hdet⟩, fun T hT => not_determining_of_card_lt d T hT⟩

/-- **No finite cutoff works for all degrees**: every finite set of exact readings is
shared by the zero polynomial and some nonzero polynomial (of degree `|T|`). -/
theorem no_uniform_finite_cutoff (T : Finset (ℝ × ℝ)) :
    ∃ p : MvPolynomial Bool ℝ, p ≠ 0 ∧ ∀ x ∈ T, readPoly p x = 0 := by
  have hN : T.card < N T.card := by
    rw [N]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by nlinarith))
  obtain ⟨p, hp, -, hvan⟩ := exists_vanishing_of_card_lt T.card T hN
  exact ⟨p, hp, hvan⟩

end

end SiphonOptimalDetermination

#print axioms SiphonOptimalDetermination.card_expSet
#print axioms SiphonOptimalDetermination.finrank_V
#print axioms SiphonOptimalDetermination.exists_vanishing_of_card_lt
#print axioms SiphonOptimalDetermination.not_determining_of_card_lt
#print axioms SiphonOptimalDetermination.adaptive_not_determining
#print axioms SiphonOptimalDetermination.exists_optimal_determining_set
#print axioms SiphonOptimalDetermination.minimum_is_N
#print axioms SiphonOptimalDetermination.no_uniform_finite_cutoff
