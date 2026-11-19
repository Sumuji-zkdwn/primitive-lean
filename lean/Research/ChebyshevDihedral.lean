import Mathlib

/-!
# The dihedral Galois group of `k(z) / k(z^m + z^{-m})`

`docs/verification/2026-10-31-kummer-dihedral.md` proves on paper (section
"全二面体ガロア群同型へ進むための数学的証明") that for a primitive `m`-th root of unity `ζ`,
`F = ℂ(z)` is Galois over `K = ℂ(t)`, `t = (z^m + z^{-m})/2`, with group `D_m`, and that `F` is
the splitting field of `T_m(X) - t`. It lists four steps that were not formalized. This
module proves them over any field `k` containing a primitive `m`-th root of unity `ζ`, with
`F = k⟮X⟯ = RatFunc k`.

* `baseField k m = k⟮X^m + X^{-m}⟯` as an intermediate field (`adjoin_half_eq`: the same
  field as `k⟮(X^m + X^{-m})/2⟯` when `2 ≠ 0`).
* `sigma`: the dihedral group acts by `r i : X ↦ ζ^i X` and `sr i : X ↦ ζ^i / X`
  (`subst` substitutes a transcendental element for `X`, so `f(X) ↦ f(g·X)`; composing
  automorphisms `g` then `h` composes the point maps as `h` after `g`); the action is
  faithful (`sigma_injective`) and fixes `X^m + X^{-m}` (`sigma_tInv`).
* `finrank_le`: `X` is a root of `Y^(2m) - t Y^m + 1`, so `[k(X) : k(t)] ≤ 2m`.
* `galEquiv : DihedralGroup m ≃* Gal(k(X)/k(t))`, `finrank_baseField` (`= 2m`) and
  `isGalois_baseField`: the `2m` automorphisms fix `k(t)`, so
  `2m ≤ |Gal| ≤ [k(X):k(t)] ≤ 2m`.
* `isSplittingField` (`m ≥ 3`): `k(X)` is the splitting field over `k(t)` of the
  Dickson polynomial `D_m(Y, 1) - t`, whose roots are `ζ^j X + ζ^{-j} X⁻¹`
  (`aeval_root`, `root_injective`); `X` is recovered from two of them.
  `chebyshev_T_root_half` restates the roots in the note's normalization
  `T_m(x_j) = (X^m + X^{-m})/2` with `x_j = (ζ^j X + ζ^{-j} X⁻¹)/2`.
-/
namespace ChebyshevDihedral

open RatFunc
open scoped RatFunc Polynomial

variable {k : Type*} [Field k]

/-- The `k`-algebra endomorphism of `k(X)` substituting a transcendental `g` for `X`. -/
noncomputable def subst (g : k⟮X⟯) (hg : Transcendental k g) : k⟮X⟯ →ₐ[k] k⟮X⟯ :=
  RatFunc.liftAlgHom (Polynomial.aeval g)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (transcendental_iff_injective.mp hg))

theorem subst_X (g : k⟮X⟯) (hg : Transcendental k g) : subst g hg X = g := by
  rw [subst, RatFunc.liftAlgHom_apply, num_X, denom_X]
  simp

/-- `k`-algebra maps out of `k(X)` are determined by the image of `X`. -/
theorem algHom_ext_X {L : Type*} [Field L] [Algebra k L] {φ ψ : k⟮X⟯ →ₐ[k] L}
    (h : φ X = ψ X) : φ = ψ := by
  have hpoly : φ.comp (IsScalarTower.toAlgHom k k[X] k⟮X⟯) =
      ψ.comp (IsScalarTower.toAlgHom k k[X] k⟮X⟯) := by
    apply Polynomial.algHom_ext
    simpa [RatFunc.algebraMap_X] using h
  have hring : (φ : k⟮X⟯ →+* L) = (ψ : k⟮X⟯ →+* L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
    ext p
    · simpa using congrArg (fun f => f (Polynomial.C p)) hpoly
    · simpa using congrArg (fun f => f Polynomial.X) hpoly
  exact AlgHom.toRingHom_injective hring

theorem transcendental_of_intDegree_ne_zero {g : k⟮X⟯} (hg : g.intDegree ≠ 0) :
    Transcendental k g := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c, rfl⟩
  exact hg (intDegree_C c)

theorem intDegree_C_mul_X {c : k} (hc : c ≠ 0) : (C c * X : k⟮X⟯).intDegree = 1 := by
  rw [intDegree_mul (by simpa using hc) X_ne_zero, intDegree_C, intDegree_X, zero_add]

theorem intDegree_C_mul_X_inv {c : k} (hc : c ≠ 0) : (C c * X⁻¹ : k⟮X⟯).intDegree = -1 := by
  rw [intDegree_mul (by simpa using hc) (inv_ne_zero X_ne_zero), intDegree_C, intDegree_inv,
    intDegree_X, zero_add]

theorem subst_C_mul_X (g : k⟮X⟯) (hg : Transcendental k g) (c : k) :
    subst g hg (C c * X) = C c * g := by
  rw [map_mul, ← algebraMap_eq_C, AlgHom.commutes, subst_X, algebraMap_eq_C]

theorem subst_C_mul_X_inv (g : k⟮X⟯) (hg : Transcendental k g) (c : k) :
    subst g hg (C c * X⁻¹) = C c * g⁻¹ := by
  rw [map_mul, map_inv₀, ← algebraMap_eq_C, AlgHom.commutes, subst_X, algebraMap_eq_C]

theorem subst_comp (g h : k⟮X⟯) (hg : Transcendental k g) (hh : Transcendental k h)
    (hgh : Transcendental k (subst g hg h)) :
    (subst g hg).comp (subst h hh) = subst (subst g hg h) hgh :=
  algHom_ext_X (by simp [subst_X])

theorem subst_X_self : subst (X : k⟮X⟯) (transcendental_of_intDegree_ne_zero (by simp)) =
    AlgHom.id k k⟮X⟯ :=
  algHom_ext_X (by simp [subst_X])

variable {m : ℕ} [NeZero m] {ζ : k}

/-- `i ↦ ζ ^ i` on `ZMod m`. -/
def u (ζ : k) (i : ZMod m) : k := ζ ^ i.val

theorem u_add (hζ : IsPrimitiveRoot ζ m) (i j : ZMod m) : u ζ (i + j) = u ζ i * u ζ j := by
  unfold u
  rw [ZMod.val_add, ← pow_add]
  have := pow_mod_orderOf ζ (i.val + j.val)
  rwa [← hζ.eq_orderOf] at this

theorem u_ne_zero (hζ : IsPrimitiveRoot ζ m) (i : ZMod m) : u ζ i ≠ 0 :=
  pow_ne_zero _ (hζ.ne_zero (NeZero.ne m))

omit [NeZero m] in
theorem u_zero : u ζ (0 : ZMod m) = 1 := by simp [u]

theorem u_eq_one_iff (hζ : IsPrimitiveRoot ζ m) (i : ZMod m) : u ζ i = 1 ↔ i = 0 := by
  unfold u
  rw [hζ.pow_eq_one_iff_dvd, ← ZMod.val_eq_zero]
  constructor
  · intro h
    exact Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt i)
  · intro h; rw [h]; exact dvd_zero m

omit [NeZero m] in
theorem u_pow (hζ : IsPrimitiveRoot ζ m) (i : ZMod m) : u ζ i ^ m = 1 := by
  unfold u
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem u_sub (hζ : IsPrimitiveRoot ζ m) (i j : ZMod m) : u ζ (j - i) = u ζ j / u ζ i := by
  rw [eq_div_iff (u_ne_zero hζ i), ← u_add hζ, sub_add_cancel]

/-- Image of `X` under the dihedral element: `r i ↦ ζⁱ X`, `sr i ↦ ζⁱ / X`. -/
noncomputable def img (ζ : k) : DihedralGroup m → k⟮X⟯
  | .r i => C (u ζ i) * X
  | .sr i => C (u ζ i) * X⁻¹

theorem img_transcendental (hζ : IsPrimitiveRoot ζ m) (g : DihedralGroup m) :
    Transcendental k (img ζ g) := by
  apply transcendental_of_intDegree_ne_zero
  cases g with
  | r i => rw [img, intDegree_C_mul_X (u_ne_zero hζ i)]; decide
  | sr i => rw [img, intDegree_C_mul_X_inv (u_ne_zero hζ i)]; decide

/-- The substitution attached to a dihedral element. -/
noncomputable def rho (hζ : IsPrimitiveRoot ζ m) (g : DihedralGroup m) : k⟮X⟯ →ₐ[k] k⟮X⟯ :=
  subst (img ζ g) (img_transcendental hζ g)

theorem rho_X (hζ : IsPrimitiveRoot ζ m) (g : DihedralGroup m) : rho hζ g X = img ζ g :=
  subst_X _ _

theorem rho_mul (hζ : IsPrimitiveRoot ζ m) (g h : DihedralGroup m) :
    rho hζ (g * h) = (rho hζ g).comp (rho hζ h) := by
  apply algHom_ext_X
  rw [AlgHom.comp_apply, rho_X, rho_X]
  have hC : ∀ i, (C (u ζ i) : k⟮X⟯) ≠ 0 := fun i => by simpa using u_ne_zero hζ i
  cases g with
  | r i =>
    cases h with
    | r j =>
      rw [DihedralGroup.r_mul_r, img, img, rho, subst_C_mul_X, img, u_add hζ, map_mul]; ring
    | sr j =>
      rw [DihedralGroup.r_mul_sr, img, img, rho, subst_C_mul_X_inv, img, u_sub hζ, map_div₀]
      field_simp
  | sr i =>
    cases h with
    | r j =>
      rw [DihedralGroup.sr_mul_r, img, img, rho, subst_C_mul_X, img, u_add hζ, map_mul]; ring
    | sr j =>
      rw [DihedralGroup.sr_mul_sr, img, img, rho, subst_C_mul_X_inv, img, u_sub hζ, map_div₀]
      field_simp

theorem rho_one (hζ : IsPrimitiveRoot ζ m) : rho hζ (1 : DihedralGroup m) = AlgHom.id k k⟮X⟯ := by
  apply algHom_ext_X
  rw [rho_X, DihedralGroup.one_def, img, u_zero]
  simp

/-- The dihedral group acting on `k(X)` by `k`-algebra automorphisms. -/
noncomputable def sigma (hζ : IsPrimitiveRoot ζ m) : DihedralGroup m →* (k⟮X⟯ ≃ₐ[k] k⟮X⟯) where
  toFun g := AlgEquiv.ofAlgHom (rho hζ g) (rho hζ g⁻¹)
    (by rw [← rho_mul, _root_.mul_inv_cancel, rho_one])
    (by rw [← rho_mul, _root_.inv_mul_cancel, rho_one])
  map_one' := by ext x; simp [rho_one]
  map_mul' g h := by ext x; simp [rho_mul]

theorem sigma_apply (hζ : IsPrimitiveRoot ζ m) (g : DihedralGroup m) (x : k⟮X⟯) :
    sigma hζ g x = rho hζ g x := rfl

theorem sigma_injective (hζ : IsPrimitiveRoot ζ m) : Function.Injective (sigma hζ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hX : img ζ g = X := by
    rw [← rho_X hζ, ← sigma_apply, hg]; rfl
  cases g with
  | r i =>
    rw [img] at hX
    have : C (u ζ i) = (1 : k⟮X⟯) := by
      have h := mul_right_cancel₀ X_ne_zero (hX.trans (one_mul X).symm)
      exact h
    rw [← map_one C] at this
    have hi := (u_eq_one_iff hζ i).mp (C_injective this)
    rw [hi, ← DihedralGroup.one_def]
  | sr i =>
    rw [img] at hX
    have h1 := intDegree_C_mul_X_inv (u_ne_zero hζ i)
    rw [hX, intDegree_X] at h1
    exact absurd h1 (by decide)

/-- The invariant `X^m + X^{-m}`. -/
noncomputable def tInv (m : ℕ) : k⟮X⟯ := X ^ m + X⁻¹ ^ m

theorem sigma_tInv (hζ : IsPrimitiveRoot ζ m) (g : DihedralGroup m) :
    sigma hζ g (tInv m) = tInv m := by
  rw [sigma_apply, tInv, map_add, map_pow, map_pow, map_inv₀, rho_X]
  have hpow : ∀ i, (C (u ζ i) : k⟮X⟯) ^ m = 1 := fun i => by rw [← map_pow, u_pow hζ, map_one]
  cases g with
  | r i => rw [img, mul_pow, mul_inv, mul_pow, inv_pow (C _), hpow]; simp
  | sr i => rw [img, mul_pow, mul_inv, mul_pow, inv_pow (C _), hpow, inv_inv]; simp; ring

/-- The subfield `k(X^m + X^{-m})` of `k(X)`. -/
noncomputable def baseField (k : Type*) [Field k] (m : ℕ) : IntermediateField k k⟮X⟯ :=
  IntermediateField.adjoin k {tInv m}

theorem tInv_mem (m : ℕ) : tInv m ∈ baseField k m :=
  IntermediateField.mem_adjoin_simple_self k _

/-- `X` is a root of `Y^(2m) - t Y^m + 1` over `k(t)`. -/
noncomputable def annPoly (m : ℕ) : (baseField k m)[X] :=
  Polynomial.X ^ (2 * m) - Polynomial.C ⟨tInv m, tInv_mem m⟩ * Polynomial.X ^ m + 1

theorem annPoly_aeval (m : ℕ) : Polynomial.aeval (X : k⟮X⟯) (annPoly (k := k) m) = 0 := by
  simp only [annPoly, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    map_one, IntermediateField.algebraMap_apply, tInv]
  have hX : (X : k⟮X⟯) ≠ 0 := X_ne_zero
  have e1 : (X * X : k⟮X⟯) ^ m = X ^ (2 * m) := by rw [← sq, ← pow_mul]
  have e2 : (X⁻¹ : k⟮X⟯) ^ m * X ^ m = 1 := by rw [← mul_pow, inv_mul_cancel₀ hX, one_pow]
  rw [add_mul, ← mul_pow, e1, e2]
  ring

theorem annPoly_monic (m : ℕ) [NeZero m] : (annPoly (k := k) m).Monic := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  unfold annPoly
  set a : baseField k m := ⟨tInv m, tInv_mem m⟩
  have hlt : (Polynomial.C a * Polynomial.X ^ m).degree <
      ((Polynomial.X : (baseField k m)[X]) ^ (2 * m)).degree := by
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast (show m < 2 * m by omega)
  have h1 := (Polynomial.monic_X_pow (R := baseField k m) (2 * m)).sub_of_left hlt
  have hdeg : ((Polynomial.X : (baseField k m)[X]) ^ (2 * m) -
      Polynomial.C a * Polynomial.X ^ m).degree = ((2 * m : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
  apply h1.add_of_left
  rw [Polynomial.degree_one, hdeg]
  exact_mod_cast (show 0 < 2 * m by omega)

theorem annPoly_natDegree (m : ℕ) [NeZero m] : (annPoly (k := k) m).natDegree = 2 * m := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  unfold annPoly
  set a : baseField k m := ⟨tInv m, tInv_mem m⟩
  have hlt : (Polynomial.C a * Polynomial.X ^ m).degree <
      ((Polynomial.X : (baseField k m)[X]) ^ (2 * m)).degree := by
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast (show m < 2 * m by omega)
  have hdeg : ((Polynomial.X : (baseField k m)[X]) ^ (2 * m) -
      Polynomial.C a * Polynomial.X ^ m).degree = ((2 * m : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
  have hlt2 : (1 : (baseField k m)[X]).degree <
      (Polynomial.X ^ (2 * m) - Polynomial.C a * Polynomial.X ^ m).degree := by
    rw [Polynomial.degree_one, hdeg]; exact_mod_cast (show 0 < 2 * m by omega)
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt hlt2, Polynomial.natDegree_eq_of_degree_eq_some hdeg]

theorem isIntegral_X (m : ℕ) [NeZero m] : IsIntegral (baseField k m) (X : k⟮X⟯) :=
  ⟨annPoly m, annPoly_monic m, by rw [← Polynomial.aeval_def]; exact annPoly_aeval m⟩

theorem finrank_le (m : ℕ) [NeZero m] : Module.finrank (baseField k m) k⟮X⟯ ≤ 2 * m := by
  have htop := RatFunc.IntermediateField.adjoin_X (baseField k m)
  have h1 : Module.finrank (baseField k m) k⟮X⟯ =
      Module.finrank (baseField k m) (IntermediateField.adjoin (baseField k m) {(X : k⟮X⟯)}) := by
    rw [htop, IntermediateField.finrank_top']
  rw [h1, IntermediateField.adjoin.finrank (isIntegral_X (k := k) m), ← annPoly_natDegree (k := k) m]
  exact Polynomial.natDegree_le_natDegree
    (minpoly.min _ _ (annPoly_monic (k := k) m) (annPoly_aeval (k := k) m))

instance finiteDimensional (m : ℕ) [NeZero m] :
    FiniteDimensional (baseField k m) k⟮X⟯ := by
  have htop := RatFunc.IntermediateField.adjoin_X (baseField k m)
  have : FiniteDimensional (baseField k m) (IntermediateField.adjoin (baseField k m) {(X : k⟮X⟯)}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_X (k := k) m)
  rw [htop] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

theorem sigma_mem_fixingSubgroup (hζ : IsPrimitiveRoot ζ m) (g : DihedralGroup m) :
    sigma hζ g ∈ (baseField k m).fixingSubgroup := by
  have hle : baseField k m ≤ IntermediateField.fixedField (sigma hζ).range := by
    rw [baseField, IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
    rintro f ⟨g, rfl⟩
    exact sigma_tInv hζ g
  exact (IntermediateField.le_fixedField_iff_le_fixingSubgroup _ _).mp hle ⟨g, rfl⟩

/-- The dihedral group mapped into `Gal(k(X)/k(X^m + X^{-m}))`. -/
noncomputable def toGal (hζ : IsPrimitiveRoot ζ m) :
    DihedralGroup m →* Gal(k⟮X⟯/baseField k m) :=
  (IntermediateField.fixingSubgroupEquiv (baseField k m)).toMonoidHom.comp
    ((sigma hζ).codRestrict _ (sigma_mem_fixingSubgroup hζ))

theorem toGal_apply (hζ : IsPrimitiveRoot ζ m) (g : DihedralGroup m) (x : k⟮X⟯) :
    toGal hζ g x = sigma hζ g x := rfl

theorem toGal_injective (hζ : IsPrimitiveRoot ζ m) : Function.Injective (toGal hζ) := by
  intro g h hgh
  apply sigma_injective hζ
  ext x
  have := congrArg (fun e : Gal(k⟮X⟯/baseField k m) => e x) hgh
  simpa [toGal_apply] using this

theorem card_gal_and_finrank (hζ : IsPrimitiveRoot ζ m) :
    Fintype.card Gal(k⟮X⟯/baseField k m) = 2 * m ∧
      Module.finrank (baseField k m) k⟮X⟯ = 2 * m := by
  have h1 : Fintype.card (DihedralGroup m) ≤ Fintype.card Gal(k⟮X⟯/baseField k m) :=
    Fintype.card_le_of_injective _ (toGal_injective hζ)
  have h2 : Fintype.card Gal(k⟮X⟯/baseField k m) ≤ Module.finrank (baseField k m) k⟮X⟯ :=
    AlgEquiv.card_le
  have h3 := finrank_le (k := k) m
  rw [DihedralGroup.card] at h1
  omega

/-- **`[k(X) : k(X^m + X^{-m})] = 2m`.** -/
theorem finrank_baseField (hζ : IsPrimitiveRoot ζ m) :
    Module.finrank (baseField k m) k⟮X⟯ = 2 * m :=
  (card_gal_and_finrank hζ).2

/-- **`k(X)` is Galois over `k(X^m + X^{-m})`.** -/
theorem isGalois_baseField (hζ : IsPrimitiveRoot ζ m) : IsGalois (baseField k m) k⟮X⟯ := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_eq_fintype_card, (card_gal_and_finrank hζ).1, (card_gal_and_finrank hζ).2]

theorem toGal_bijective (hζ : IsPrimitiveRoot ζ m) : Function.Bijective (toGal hζ) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨toGal_injective hζ, by rw [DihedralGroup.card, (card_gal_and_finrank hζ).1]⟩

/-- **The Galois group of `k(X)` over `k(X^m + X^{-m})` is the dihedral group of order `2m`**,
with `r i` acting by `X ↦ ζ^i X` and `sr i` by `X ↦ ζ^i / X`. -/
noncomputable def galEquiv (hζ : IsPrimitiveRoot ζ m) :
    DihedralGroup m ≃* Gal(k⟮X⟯/baseField k m) :=
  MulEquiv.ofBijective (toGal hζ) (toGal_bijective hζ)

theorem galEquiv_r_X (hζ : IsPrimitiveRoot ζ m) (i : ZMod m) :
    galEquiv hζ (.r i) X = C (ζ ^ i.val) * X := by
  show rho hζ (.r i) X = _
  rw [rho_X, img, u]

theorem galEquiv_sr_X (hζ : IsPrimitiveRoot ζ m) (i : ZMod m) :
    galEquiv hζ (.sr i) X = C (ζ ^ i.val) * X⁻¹ := by
  show rho hζ (.sr i) X = _
  rw [rho_X, img, u]

/-- `D_n(Y, 1)` is monic of degree `n` for `n ≥ 1`. -/
theorem dickson_one_one_monic_natDegree {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    (Polynomial.dickson 1 (1 : R) (n + 1)).Monic ∧
      (Polynomial.dickson 1 (1 : R) (n + 1)).natDegree = n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [Polynomial.dickson_one]
    · rw [Polynomial.dickson_two]
      have h : (Polynomial.X ^ 2 - Polynomial.C (1 : R) * (3 - ((1 : ℕ) : R[X])) : R[X]) =
          Polynomial.X ^ 2 - Polynomial.C 2 := by
        rw [map_one, one_mul]; norm_num
        exact (map_ofNat Polynomial.C 2).symm
      rw [h]
      exact ⟨Polynomial.monic_X_pow_sub_C _ (by norm_num),
        Polynomial.natDegree_X_pow_sub_C _⟩
    · obtain ⟨hm1, hd1⟩ := ih n (by omega)
      obtain ⟨hm2, hd2⟩ := ih (n + 1) (by omega)
      rw [show n + 2 + 1 = (n + 1) + 2 by ring, Polynomial.dickson_add_two, map_one, one_mul]
      have hX : (Polynomial.X * Polynomial.dickson 1 (1 : R) (n + 1 + 1)).Monic :=
        Polynomial.monic_X.mul hm2
      have hXd : (Polynomial.X * Polynomial.dickson 1 (1 : R) (n + 1 + 1)).natDegree = n + 3 := by
        rw [Polynomial.natDegree_X_mul hm2.ne_zero, hd2]
      have hlt : (Polynomial.dickson 1 (1 : R) (n + 1)).natDegree <
          (Polynomial.X * Polynomial.dickson 1 (1 : R) (n + 1 + 1)).natDegree := by
        rw [hd1, hXd]; omega
      refine ⟨hX.sub_of_left (Polynomial.degree_lt_degree hlt), ?_⟩
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hXd]

/-- The Dickson–Chebyshev equation `D_m(Y, 1) = t` over `k(t)`; `D_m(z + z⁻¹, 1) = z^m + z^{-m}`
and `D_m(2Y, 1) = 2 T_m(Y)`. -/
noncomputable def chebPoly (m : ℕ) : (baseField k m)[X] :=
  Polynomial.dickson 1 (1 : baseField k m) m - Polynomial.C ⟨tInv m, tInv_mem m⟩

theorem chebPoly_natDegree (m : ℕ) [NeZero m] : (chebPoly (k := k) m).natDegree = m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.ne m; omega⟩
  rw [chebPoly, Polynomial.natDegree_sub_C, (dickson_one_one_monic_natDegree n).2]

theorem chebPoly_ne_zero (m : ℕ) [NeZero m] : chebPoly (k := k) m ≠ 0 := by
  intro h
  have := chebPoly_natDegree (k := k) m
  rw [h, Polynomial.natDegree_zero] at this
  exact NeZero.ne m this.symm

/-- The roots `ζ^j X + (ζ^j X)⁻¹`. -/
noncomputable def root (ζ : k) (j : ZMod m) : k⟮X⟯ := C (u ζ j) * X + (C (u ζ j) * X)⁻¹

theorem u_injective (hζ : IsPrimitiveRoot ζ m) : Function.Injective (u ζ : ZMod m → k) := by
  intro i j h
  have : u ζ (i - j) = 1 := by rw [u_sub hζ, h, div_self (u_ne_zero hζ j)]
  exact sub_eq_zero.mp ((u_eq_one_iff hζ _).mp this)

theorem aeval_root (hζ : IsPrimitiveRoot ζ m) (j : ZMod m) :
    Polynomial.aeval (root ζ j) (chebPoly (k := k) m) = 0 := by
  have hx : (C (u ζ j) * X : k⟮X⟯) ≠ 0 :=
    mul_ne_zero (by simpa using u_ne_zero hζ j) X_ne_zero
  rw [chebPoly, map_sub, Polynomial.aeval_C, IntermediateField.algebraMap_apply,
    ← Polynomial.eval_map_algebraMap, Polynomial.map_dickson, map_one, root,
    Polynomial.dickson_one_one_eval_add_inv _ _ (mul_inv_cancel₀ hx)]
  have hpow : (C (u ζ j) : k⟮X⟯) ^ m = 1 := by rw [← map_pow, u_pow hζ, map_one]
  simp only [tInv, mul_pow, hpow, one_mul, mul_inv, inv_pow, inv_one, sub_self]

theorem root_injective (hζ : IsPrimitiveRoot ζ m) : Function.Injective (root (m := m) ζ) := by
  intro i j h
  set a : k⟮X⟯ := C (u ζ i) * X
  set b : k⟮X⟯ := C (u ζ j) * X
  have ha : a ≠ 0 := mul_ne_zero (by simpa using u_ne_zero hζ i) X_ne_zero
  have hb : b ≠ 0 := mul_ne_zero (by simpa using u_ne_zero hζ j) X_ne_zero
  have hab : (a - b) * (a * b - 1) = 0 := by
    have h' : a + a⁻¹ = b + b⁻¹ := h
    field_simp at h'
    linear_combination h'
  rcases mul_eq_zero.mp hab with h1 | h1
  · have : C (u ζ i) = (C (u ζ j) : k⟮X⟯) := mul_right_cancel₀ X_ne_zero (sub_eq_zero.mp h1)
    exact u_injective hζ (C_injective this)
  · exfalso
    have h2 : a * b = 1 := sub_eq_zero.mp h1
    have hdeg := congrArg intDegree h2
    rw [intDegree_mul ha hb, intDegree_C_mul_X (u_ne_zero hζ i), intDegree_C_mul_X (u_ne_zero hζ j),
      intDegree_one] at hdeg
    exact absurd hdeg (by decide)

theorem root_mem_rootSet (hζ : IsPrimitiveRoot ζ m) (j : ZMod m) :
    root ζ j ∈ (chebPoly (k := k) m).rootSet k⟮X⟯ :=
  (Polynomial.mem_rootSet_of_ne (chebPoly_ne_zero m)).mpr (aeval_root hζ j)

theorem chebPoly_splits (hζ : IsPrimitiveRoot ζ m) :
    ((chebPoly (k := k) m).map (algebraMap (baseField k m) k⟮X⟯)).Splits := by
  classical
  have hdeg : ((chebPoly (k := k) m).map (algebraMap (baseField k m) k⟮X⟯)).natDegree = m := by
    rw [Polynomial.natDegree_map, chebPoly_natDegree]
  rw [Polynomial.splits_iff_card_roots, hdeg]
  apply le_antisymm
  · exact (Polynomial.card_roots' _).trans hdeg.le
  · have hle : (Finset.univ.image (root (m := m) ζ)).val ≤
        ((chebPoly (k := k) m).map (algebraMap (baseField k m) k⟮X⟯)).roots := by
      rw [Multiset.le_iff_subset (Finset.nodup _)]
      intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      have := root_mem_rootSet (k := k) hζ j
      rw [Polynomial.rootSet_def, Finset.mem_coe, Multiset.mem_toFinset] at this
      exact this
    have := Multiset.card_le_card hle
    rwa [Finset.card_val, Finset.card_image_of_injective _ (root_injective hζ), Finset.card_univ,
      ZMod.card] at this

omit [NeZero m] in
theorem algebraMap_k_mem {S : IntermediateField (baseField k m) k⟮X⟯} (c : k) :
    (C c : k⟮X⟯) ∈ S := by
  have : (C c : k⟮X⟯) = algebraMap (baseField k m) k⟮X⟯ (algebraMap k (baseField k m) c) := by
    rw [← IsScalarTower.algebraMap_apply, algebraMap_eq_C]
  rw [this]
  exact S.algebraMap_mem _

theorem adjoin_rootSet (hζ : IsPrimitiveRoot ζ m) (hm : 3 ≤ m) :
    IntermediateField.adjoin (baseField k m) ((chebPoly (k := k) m).rootSet k⟮X⟯) = ⊤ := by
  set S := IntermediateField.adjoin (baseField k m) ((chebPoly (k := k) m).rootSet k⟮X⟯)
  have h0 : root ζ (0 : ZMod m) ∈ S := IntermediateField.subset_adjoin _ _ (root_mem_rootSet hζ 0)
  have h1 : root ζ (1 : ZMod m) ∈ S := IntermediateField.subset_adjoin _ _ (root_mem_rootSet hζ 1)
  have hu1 : u ζ (1 : ZMod m) = ζ := by
    have : Fact (1 < m) := ⟨by omega⟩
    simp [u, ZMod.val_one]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  have hsq : ζ - ζ⁻¹ ≠ 0 := by
    intro h
    have : ζ ^ 2 = 1 := by
      have := sub_eq_zero.mp h
      field_simp at this
      linear_combination this
    have := hζ.dvd_of_pow_eq_one 2 this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hdiff : root (m := m) ζ 1 - C ζ⁻¹ * root (m := m) ζ 0 = C (ζ - ζ⁻¹) * X := by
    simp only [root, hu1, u_zero, map_one, one_mul, mul_inv, map_inv₀, map_sub]
    ring
  have hX : (X : k⟮X⟯) = (root (m := m) ζ 1 - C ζ⁻¹ * root (m := m) ζ 0) * C (ζ - ζ⁻¹)⁻¹ := by
    rw [hdiff, mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hsq, map_one, one_mul]
  have hXS : (X : k⟮X⟯) ∈ S := by
    rw [hX]
    exact S.mul_mem (S.sub_mem h1 (S.mul_mem (algebraMap_k_mem _) h0)) (algebraMap_k_mem _)
  rw [eq_top_iff, ← RatFunc.IntermediateField.adjoin_X (baseField k m),
    IntermediateField.adjoin_simple_le_iff]
  exact hXS

/-- **`k(X)` is the splitting field of `D_m(Y, 1) - (X^m + X^{-m})` over `k(X^m + X^{-m})`**
(for `m ≥ 3`), so `galEquiv` is the Galois group of that polynomial. -/
theorem isSplittingField (hζ : IsPrimitiveRoot ζ m) (hm : 3 ≤ m) :
    Polynomial.IsSplittingField (baseField k m) k⟮X⟯ (chebPoly m) :=
  isSplittingField_iff_intermediateField.mpr ⟨chebPoly_splits hζ, adjoin_rootSet hζ hm⟩

/-! ## The normalization of the note: `t = (z^m + z^{-m})/2` and Chebyshev's `T_m` -/

omit [NeZero m] in
/-- When `2 ≠ 0`, `k((X^m + X^{-m})/2) = k(X^m + X^{-m})`. -/
theorem adjoin_half_eq (h2 : (2 : k) ≠ 0) :
    IntermediateField.adjoin k {tInv m / 2} = baseField k m := by
  have h2' : (2 : k⟮X⟯) ≠ 0 := by
    intro h; apply h2; apply C_injective; rw [map_ofNat, h, map_zero]
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    rw [div_eq_mul_inv, show (2 : k⟮X⟯)⁻¹ = algebraMap k k⟮X⟯ 2⁻¹ by
      rw [map_inv₀, algebraMap_eq_C, map_ofNat]]
    exact (baseField k m).mul_mem (tInv_mem m) ((baseField k m).algebraMap_mem _)
  · rw [baseField, IntermediateField.adjoin_simple_le_iff]
    have hmem := IntermediateField.mem_adjoin_simple_self k (tInv (k := k) m / 2)
    have key : algebraMap k k⟮X⟯ 2 * (tInv m / 2) ∈ IntermediateField.adjoin k {tInv (k := k) m / 2} :=
      IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _) hmem
    rwa [algebraMap_eq_C, map_ofNat, mul_div_cancel₀ _ h2'] at key

/-- The roots `x_j = (ζ^j z + ζ^{-j} z^{-1})/2` of the note satisfy `T_m(x_j) = t`. -/
theorem chebyshev_T_root_half (hζ : IsPrimitiveRoot ζ m) (h2 : (2 : k) ≠ 0) (j : ZMod m) :
    (Polynomial.Chebyshev.T k⟮X⟯ m).eval (root ζ j / 2) = tInv m / 2 := by
  have h2' : (2 : k⟮X⟯) ≠ 0 := by
    intro h; apply h2; apply C_injective; rw [map_ofNat, h, map_zero]
  have : Invertible (2 : k⟮X⟯) := invertibleOfNonzero h2'
  have hx : (C (u ζ j) * X : k⟮X⟯) ≠ 0 :=
    mul_ne_zero (by simpa using u_ne_zero hζ j) X_ne_zero
  have hpow : (C (u ζ j) : k⟮X⟯) ^ m = 1 := by rw [← map_pow, u_pow hζ, map_one]
  rw [Polynomial.chebyshev_T_eq_dickson_one_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
    mul_div_cancel₀ _ h2', root, Polynomial.dickson_one_one_eval_add_inv _ _ (mul_inv_cancel₀ hx)]
  simp only [tInv, mul_pow, hpow, one_mul, mul_inv, inv_pow, inv_one]
  rw [invOf_eq_inv, inv_mul_eq_div]

end ChebyshevDihedral

#print axioms ChebyshevDihedral.subst_X
#print axioms ChebyshevDihedral.algHom_ext_X
#print axioms ChebyshevDihedral.sigma_injective
#print axioms ChebyshevDihedral.sigma_tInv
#print axioms ChebyshevDihedral.finrank_le
#print axioms ChebyshevDihedral.finrank_baseField
#print axioms ChebyshevDihedral.isGalois_baseField
#print axioms ChebyshevDihedral.toGal_bijective
#print axioms ChebyshevDihedral.galEquiv_r_X
#print axioms ChebyshevDihedral.galEquiv_sr_X
#print axioms ChebyshevDihedral.dickson_one_one_monic_natDegree
#print axioms ChebyshevDihedral.chebPoly_splits
#print axioms ChebyshevDihedral.adjoin_rootSet
#print axioms ChebyshevDihedral.isSplittingField
#print axioms ChebyshevDihedral.adjoin_half_eq
#print axioms ChebyshevDihedral.chebyshev_T_root_half
#print axioms ChebyshevDihedral.galEquiv
