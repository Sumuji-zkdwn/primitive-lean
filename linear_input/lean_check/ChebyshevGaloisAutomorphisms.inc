/-!
# Base-field rotation and reflection automorphisms for ternary Chebyshev

For k ≥ 1, the preceding supplement proves that C(X)/C(J(X^(3^k))) is the
actual splitting field. This file constructs the model's rotation and inversion
automorphisms and proves an injective dihedral representation. It does not claim
that this representation exhausts every automorphism; the k = 0 splitting
field case remains excluded because the polynomial is linear.
-/

noncomputable section

namespace LinearInputChebyshevAutomorphisms

open Polynomial
open IntermediateField
open LinearInputChebyshevDescent
open LinearInputChebyshevSplitting
open LinearInputChebyshevTower

abbrev E := RatFunc ℂ
abbrev Base (k : ℕ) := LinearInputChebyshevSplitting.parameterField k
abbrev Aut (k : ℕ) := E ≃ₐ[Base k] E

/-- A nonzero scalar multiple of the rational variable still generates C(X). -/
theorem adjoin_scaled_X (c : ℂ) (hc : c ≠ 0) :
    IntermediateField.adjoin ℂ
      ({RatFunc.C c * (RatFunc.X : E)} : Set E) = ⊤ := by
  let F : IntermediateField ℂ E :=
    IntermediateField.adjoin ℂ
      ({RatFunc.C c * (RatFunc.X : E)} : Set E)
  have hgen : RatFunc.C c * (RatFunc.X : E) ∈ F :=
    IntermediateField.subset_adjoin ℂ _ (by simp)
  have hcF : RatFunc.C c ∈ F := F.algebraMap_mem c
  have hciF : RatFunc.C c⁻¹ ∈ F := F.algebraMap_mem c⁻¹
  have hXeq : (RatFunc.X : E) =
      RatFunc.C c⁻¹ * (RatFunc.C c * (RatFunc.X : E)) := by
    calc
      (RatFunc.X : E) =
          (RatFunc.C c⁻¹ * RatFunc.C c) * (RatFunc.X : E) := by
            simp [hc]
      _ = RatFunc.C c⁻¹ * (RatFunc.C c * (RatFunc.X : E)) := by ring
  have hX : (RatFunc.X : E) ∈ F := by
    rw [hXeq]
    exact F.mul_mem hciF hgen
  have hle : IntermediateField.adjoin ℂ ({(RatFunc.X : E)} : Set E) ≤ F := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = (RatFunc.X : E) := by simpa using hx
    simpa [hx'] using hX
  have htopX : IntermediateField.adjoin ℂ ({(RatFunc.X : E)} : Set E) = ⊤ := by
    simpa using (RatFunc.adjoin_X (K := ℂ))
  change F = ⊤
  apply le_antisymm le_top
  calc
    ⊤ = IntermediateField.adjoin ℂ ({(RatFunc.X : E)} : Set E) := htopX.symm
    _ ≤ F := hle

/-- Inversion of X also generates the full rational-function field. -/
theorem adjoin_inv_X :
    IntermediateField.adjoin ℂ
      ({(RatFunc.X : E)⁻¹} : Set E) = ⊤ := by
  let F : IntermediateField ℂ E :=
    IntermediateField.adjoin ℂ ({(RatFunc.X : E)⁻¹} : Set E)
  have hinv : (RatFunc.X : E)⁻¹ ∈ F :=
    IntermediateField.subset_adjoin ℂ _ (by simp)
  have hX : (RatFunc.X : E) ∈ F := by
    simpa using F.inv_mem hinv
  have hle : IntermediateField.adjoin ℂ ({(RatFunc.X : E)} : Set E) ≤ F := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = (RatFunc.X : E) := by simpa using hx
    simpa [hx'] using hX
  have htopX : IntermediateField.adjoin ℂ ({(RatFunc.X : E)} : Set E) = ⊤ := by
    simpa using (RatFunc.adjoin_X (K := ℂ))
  change F = ⊤
  apply le_antisymm le_top
  calc
    ⊤ = IntermediateField.adjoin ℂ ({(RatFunc.X : E)} : Set E) := htopX.symm
    _ ≤ F := hle

/-- The ℂ-algebra automorphism determined by X ↦ cX. -/
noncomputable def linearAuto (c : ℂ) (hc : c ≠ 0) : E ≃ₐ[ℂ] E := by
  let f : E := RatFunc.C c * (RatFunc.X : E)
  have hf : Transcendental ℂ f := by
    refine f.transcendental_of_ne_C ?_
    rintro ⟨d, hd⟩
    have hX : (RatFunc.X : E) = RatFunc.C (c⁻¹ * d) := by
      calc
        (RatFunc.X : E) =
            (RatFunc.C c⁻¹ * RatFunc.C c) * (RatFunc.X : E) := by simp [hc]
        _ = RatFunc.C c⁻¹ * (RatFunc.C c * (RatFunc.X : E)) := by ring
        _ = RatFunc.C c⁻¹ * RatFunc.C d := by
          change RatFunc.C c⁻¹ * f = RatFunc.C c⁻¹ * RatFunc.C d
          exact congrArg (fun y : E => RatFunc.C c⁻¹ * y) hd
        _ = RatFunc.C (c⁻¹ * d) := by simp
    exact RatFunc.transcendental_X (hX ▸ isAlgebraic_algebraMap _)
  have hgen : IntermediateField.adjoin ℂ ({f} : Set E) = ⊤ := by
    simpa [f] using adjoin_scaled_X c hc
  have htop : ℂ⟮f⟯ = ⊤ := hgen
  exact (RatFunc.algEquivOfTranscendental f hf).trans
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)

/-- The ℂ-algebra automorphism determined by X ↦ X⁻¹. -/
noncomputable def inversionAuto : E ≃ₐ[ℂ] E := by
  let f : E := (RatFunc.X : E)⁻¹
  have hf : Transcendental ℂ f := by
    refine f.transcendental_of_ne_C ?_
    rintro ⟨c, hc⟩
    have hX : (RatFunc.X : E) = RatFunc.C c⁻¹ := by
      calc
        (RatFunc.X : E) = ((RatFunc.X : E)⁻¹)⁻¹ := by simp
        _ = (RatFunc.C c)⁻¹ := by
          change f⁻¹ = (RatFunc.C c)⁻¹
          rw [hc]
        _ = RatFunc.C c⁻¹ := by simp
    exact RatFunc.transcendental_X (hX ▸ isAlgebraic_algebraMap _)
  have hgen : IntermediateField.adjoin ℂ ({f} : Set E) = ⊤ := by
    simpa [f] using adjoin_inv_X
  have htop : ℂ⟮f⟯ = ⊤ := hgen
  exact (RatFunc.algEquivOfTranscendental f hf).trans
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)

@[simp] theorem linearAuto_X (c : ℂ) (hc : c ≠ 0) :
    linearAuto c hc (RatFunc.X : E) = RatFunc.C c * (RatFunc.X : E) := by
  simp [linearAuto, RatFunc.algEquivOfTranscendental_X]

@[simp] theorem inversionAuto_X :
    inversionAuto (RatFunc.X : E) = (RatFunc.X : E)⁻¹ := by
  simp [inversionAuto, RatFunc.algEquivOfTranscendental_X]

/-- The two basic ℂ-automorphisms fix every Joukowski parameter. -/
theorem linearAuto_fixes_parameter (m : ℕ) (hm : m ≠ 0) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ m) :
    linearAuto ζ (hζ.ne_zero hm) (genericParameter m) =
      genericParameter m := by
  rw [genericParameter_eq_joukowski]
  unfold LinearInputChebyshevDescent.joukowski
  have hpow : (RatFunc.C ζ * (RatFunc.X : E)) ^ m =
      (RatFunc.X : E) ^ m := by
    rw [mul_pow]
    have hCpow : (RatFunc.C ζ) ^ m = 1 := by
      rw [← map_pow]
      rw [hζ.pow_eq_one]
      simp
    rw [hCpow]
    simp
  have htwo :
      linearAuto ζ (hζ.ne_zero hm) (2 : E) = 2 := by
    exact map_ofNat (linearAuto ζ (hζ.ne_zero hm)) 2
  simp [linearAuto_X, map_add, map_inv₀, map_div₀, map_pow, hpow, htwo]

theorem inversionAuto_fixes_parameter (m : ℕ) :
    inversionAuto (genericParameter m) = genericParameter m := by
  rw [genericParameter_eq_joukowski]
  unfold LinearInputChebyshevDescent.joukowski
  have htwo : inversionAuto (2 : E) = 2 := by
    exact map_ofNat inversionAuto 2
  simp [inversionAuto_X, map_add, map_inv₀, map_div₀, inv_pow, htwo]
  ring

/-- A base-field generator fixed by a ℂ-automorphism forces all of C(t) fixed. -/
theorem fixes_adjoin_parameter {m : ℕ} (ψ : E ≃ₐ[ℂ] E)
    (hψ : ψ (genericParameter m) = genericParameter m) :
    ∀ x : IntermediateField.adjoin ℂ ({genericParameter m} : Set E),
      ψ x.1 = x.1 := by
  intro x
  have hfix : ∀ y, y ∈
      (IntermediateField.adjoin ℂ ({genericParameter m} : Set E)) →
      ψ y = y := by
    intro y hy
    refine IntermediateField.adjoin_induction (F := ℂ)
      (motive := fun y _ => ψ y = y)
      (mem := ?_)
      (algebraMap := ?_)
      (add := ?_)
      (inv := ?_)
      (mul := ?_)
      hy
    · intro y hy
      have hy' : y = genericParameter m := by simpa using hy
      subst y
      exact hψ
    · intro c
      change ψ (algebraMap ℂ E c) = algebraMap ℂ E c
      exact ψ.commutes c
    · intro y z hy hz ihy ihz
      simp [map_add, ihy, ihz]
    · intro y hy ih
      simp [map_inv₀, ih]
    · intro y z hy hz ihy ihz
      simp [map_mul, ihy, ihz]
  exact hfix x.1 x.2

/-- Regrade a ℂ-automorphism fixing t as an automorphism over C(t). -/
noncomputable def asBaseAuto (k : ℕ) (ψ : E ≃ₐ[ℂ] E)
    (hψ : ψ (genericParameter (3 ^ k)) =
      genericParameter (3 ^ k)) : Aut k := by
  refine
    { toRingEquiv := ψ.toRingEquiv
      commutes' := ?_ }
  intro x
  change ψ x.1 = x.1
  exact fixes_adjoin_parameter ψ hψ x

noncomputable def rotation (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) : Aut k :=
  asBaseAuto k (linearAuto ζ (hζ.ne_zero (by positivity)))
    (linearAuto_fixes_parameter (3 ^ k) (by positivity) ζ hζ)

noncomputable def reflection (k : ℕ) : Aut k :=
  asBaseAuto k inversionAuto (inversionAuto_fixes_parameter (3 ^ k))

@[simp] theorem rotation_X (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    rotation k ζ hζ (RatFunc.X : E) =
      RatFunc.C ζ * (RatFunc.X : E) := by
  change linearAuto ζ (hζ.ne_zero (by positivity)) (RatFunc.X : E) = _
  simp

@[simp] theorem reflection_X (k : ℕ) :
    reflection k (RatFunc.X : E) = (RatFunc.X : E)⁻¹ := by
  change inversionAuto (RatFunc.X : E) = _
  simp


/-- Every constant is fixed because it belongs to the chosen base field. -/
@[simp] theorem baseAuto_C (k : ℕ) (ψ : Aut k) (c : ℂ) :
    ψ (RatFunc.C c) = RatFunc.C c := by
  have h : RatFunc.C c =
      algebraMap (Base k) E (algebraMap ℂ (Base k) c) := by
    change algebraMap ℂ E c =
      algebraMap (Base k) E (algebraMap ℂ (Base k) c)
    exact (IsScalarTower.algebraMap_apply ℂ (Base k) E c).symm
  calc
    ψ (RatFunc.C c) =
        ψ (algebraMap (Base k) E (algebraMap ℂ (Base k) c)) := by rw [h]
    _ = algebraMap (Base k) E (algebraMap ℂ (Base k) c) := ψ.commutes _
    _ = RatFunc.C c := h.symm

/-- Rational-function algebra equivalences are determined by their value on X. -/
theorem ratFunc_algEquiv_ext_X {φ ψ : E ≃ₐ[ℂ] E}
    (hX : φ (RatFunc.X : E) = ψ (RatFunc.X : E)) : φ = ψ := by
  have hpoly :
      φ.toRingHom.comp (algebraMap (Polynomial ℂ) E) =
        ψ.toRingHom.comp (algebraMap (Polynomial ℂ) E) := by
    apply Polynomial.ringHom_ext
    · intro c
      change φ (RatFunc.C c) = ψ (RatFunc.C c)
      exact (φ.commutes c).trans (ψ.commutes c).symm
    · simp [RatFunc.algebraMap_X, hX]
  have hring : φ.toRingHom = ψ.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    exact congrArg (fun f : Polynomial ℂ →+* E => f p) hpoly
  ext x
  exact congrArg (fun f : E →+* E => f x) hring

theorem baseAuto_ext_X {k : ℕ} {φ ψ : Aut k}
    (hX : φ (RatFunc.X : E) = ψ (RatFunc.X : E)) : φ = ψ := by
  apply AlgEquiv.restrictScalars_injective ℂ
  exact ratFunc_algEquiv_ext_X (by simpa using hX)

@[simp] theorem rotation_pow_apply_X (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (n : ℕ) :
    (rotation k ζ hζ ^ n) (RatFunc.X : E) =
      RatFunc.C (ζ ^ n) * (RatFunc.X : E) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, AlgEquiv.mul_apply, rotation_X]
      simp [map_mul, ih]
      ring

/-- The standard generator of the rotation automorphism has order dividing 3^k. -/
theorem rotation_pow_order (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    rotation k ζ hζ ^ (3 ^ k) = 1 := by
  apply baseAuto_ext_X
  simp [rotation_pow_apply_X, hζ.pow_eq_one]

theorem reflection_sq (k : ℕ) :
    reflection k ^ 2 = 1 := by
  apply baseAuto_ext_X
  simp [pow_two, AlgEquiv.mul_apply, reflection_X]

theorem rotation_symm_X (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    (rotation k ζ hζ)⁻¹ (RatFunc.X : E) =
      RatFunc.C (ζ⁻¹) * (RatFunc.X : E) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
  have hpre : rotation k ζ hζ (RatFunc.C (ζ⁻¹) * (RatFunc.X : E)) =
      (RatFunc.X : E) := by
    rw [map_mul, baseAuto_C, rotation_X]
    calc
      RatFunc.C (ζ⁻¹) * (RatFunc.C ζ * (RatFunc.X : E)) =
          (RatFunc.C (ζ⁻¹) * RatFunc.C ζ) * (RatFunc.X : E) := by ring
      _ = RatFunc.C (ζ⁻¹ * ζ) * (RatFunc.X : E) := by rw [← map_mul]
      _ = (RatFunc.X : E) := by simp [inv_mul_cancel₀ hζ0]
  apply (rotation k ζ hζ).injective
  rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply, hpre]

theorem reflection_conjugates_rotation (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    reflection k * rotation k ζ hζ * reflection k =
      (rotation k ζ hζ)⁻¹ := by
  apply baseAuto_ext_X
  have hleft :
      (reflection k * rotation k ζ hζ * reflection k) (RatFunc.X : E) =
        RatFunc.C (ζ⁻¹) * (RatFunc.X : E) := by
    calc
      (reflection k * rotation k ζ hζ * reflection k) (RatFunc.X : E) =
          reflection k (rotation k ζ hζ (reflection k (RatFunc.X : E))) := by
            simp only [AlgEquiv.mul_apply]
      _ = reflection k (rotation k ζ hζ ((RatFunc.X : E)⁻¹)) := by
            rw [reflection_X]
      _ = reflection k ((rotation k ζ hζ (RatFunc.X : E))⁻¹) := by
            rw [map_inv₀]
      _ = reflection k ((RatFunc.C ζ * (RatFunc.X : E))⁻¹) := by
            rw [rotation_X]
      _ = (reflection k (RatFunc.C ζ * (RatFunc.X : E)))⁻¹ := by
            rw [map_inv₀]
      _ = (reflection k (RatFunc.C ζ) *
            reflection k (RatFunc.X : E))⁻¹ := by
            rw [map_mul]
      _ = (RatFunc.C ζ * (RatFunc.X : E)⁻¹)⁻¹ := by
            rw [baseAuto_C, reflection_X]
      _ = (RatFunc.X : E) * (RatFunc.C ζ)⁻¹ := by
            rw [mul_inv_rev, inv_inv]
      _ = (RatFunc.X : E) * RatFunc.C (ζ⁻¹) := by
            rw [← map_inv₀]
      _ = RatFunc.C (ζ⁻¹) * (RatFunc.X : E) := by ring
  rw [hleft, rotation_symm_X]

/-- Exponents in ZMod act on a rotation with its finite order. -/
def zmodPower {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (g : G) (i : ZMod m) : G := g ^ i.val

theorem zmodPower_zero {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (g : G) : zmodPower g (0 : ZMod m) = 1 := by
  simp [zmodPower]

theorem zmodPower_add {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (g : G) (hg : g ^ m = 1) (i j : ZMod m) :
    zmodPower g (i + j) = zmodPower g i * zmodPower g j := by
  simp only [zmodPower, ZMod.val_add, ← pow_eq_pow_mod _ hg, ← pow_add]

theorem zmodPower_neg {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (g : G) (hg : g ^ m = 1) (i : ZMod m) :
    zmodPower g (-i) = (zmodPower g i)⁻¹ := by
  have hmul : zmodPower g i * zmodPower g (-i) = 1 := by
    have h := zmodPower_add g hg i (-i)
    simpa [zmodPower_zero] using h.symm
  calc
    zmodPower g (-i) = 1 * zmodPower g (-i) := by simp
    _ = ((zmodPower g i)⁻¹ * zmodPower g i) * zmodPower g (-i) := by simp
    _ = (zmodPower g i)⁻¹ * (zmodPower g i * zmodPower g (-i)) := by rw [← mul_assoc]
    _ = (zmodPower g i)⁻¹ := by rw [hmul]; simp



/-- Conjugation by an involution sends every power to the corresponding
power of the conjugate generator. -/
theorem conjugate_pow_of_involution {G : Type*} [Group G] (s r : G)
    (hs : s * s = 1) (hsrs : s * r * s = r⁻¹) (n : ℕ) :
    s * r ^ n * s = (r⁻¹) ^ n := by
  let f : G →* G :=
    { toFun := fun x => s * x * s
      map_one' := by simpa using hs
      map_mul' := by
        intro x y
        calc
          s * (x * y) * s = s * x * y * s := by group
          _ = s * x * (s * s) * (y * s) := by
            rw [hs]
            group
          _ = (s * x * s) * (s * y * s) := by group }
  simpa [f, hsrs] using (map_pow f r n)

/-- Regard the rotation powers as indexed by ZMod (3^k). -/
noncomputable def rotationPower (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (i : ZMod (3 ^ k)) : Aut k := by
  letI : NeZero (3 ^ k) := ⟨by positivity⟩
  exact zmodPower (rotation k ζ hζ) i

theorem rotationPower_add (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (i j : ZMod (3 ^ k)) :
    rotationPower k ζ hζ (i + j) =
      rotationPower k ζ hζ i * rotationPower k ζ hζ j := by
  let : NeZero (3 ^ k) := ⟨by positivity⟩
  exact zmodPower_add (rotation k ζ hζ) (rotation_pow_order k ζ hζ) i j

theorem rotationPower_neg (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (i : ZMod (3 ^ k)) :
    rotationPower k ζ hζ (-i) =
      (rotationPower k ζ hζ i)⁻¹ := by
  let : NeZero (3 ^ k) := ⟨by positivity⟩
  exact zmodPower_neg (rotation k ζ hζ) (rotation_pow_order k ζ hζ) i

/-- The reflection conjugates every indexed rotation to its inverse. -/
theorem reflection_conjugates_rotationPower (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (i : ZMod (3 ^ k)) :
    reflection k * rotationPower k ζ hζ i * reflection k =
      rotationPower k ζ hζ (-i) := by
  have hpow := conjugate_pow_of_involution (G := Aut k)
    (reflection k) (rotation k ζ hζ) (by simpa only [pow_two] using reflection_sq k)
    (reflection_conjugates_rotation k ζ hζ) i.val
  calc
    reflection k * rotationPower k ζ hζ i * reflection k =
        (rotationPower k ζ hζ i)⁻¹ := by
          change reflection k * (rotation k ζ hζ) ^ i.val * reflection k =
            ((rotation k ζ hζ) ^ i.val)⁻¹
          rw [hpow]
          simp
    _ = rotationPower k ζ hζ (-i) :=
      (rotationPower_neg k ζ hζ i).symm

/-- Move a rotation past the reflection. -/
theorem rotationPower_mul_reflection (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (i : ZMod (3 ^ k)) :
    rotationPower k ζ hζ i * reflection k =
      reflection k * rotationPower k ζ hζ (-i) := by
  calc
    rotationPower k ζ hζ i * reflection k =
        reflection k * reflection k *
          rotationPower k ζ hζ i * reflection k := by
            change rotationPower k ζ hζ i * reflection k =
              (reflection k ^ 2) * rotationPower k ζ hζ i * reflection k
            rw [reflection_sq]
            simp
    _ = reflection k *
          (reflection k * rotationPower k ζ hζ i * reflection k) := by group
    _ = reflection k * rotationPower k ζ hζ (-i) := by
          rw [reflection_conjugates_rotationPower]

/-- The two automorphisms provide the standard faithful dihedral action on
the roots, encoded as a homomorphism to base-field automorphisms. -/
noncomputable def dihedralRepresentation (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    DihedralGroup (3 ^ k) →* Aut k where
  toFun
    | .r i => rotationPower k ζ hζ i
    | .sr i => reflection k * rotationPower k ζ hζ i
  map_one' := by
    let : NeZero (3 ^ k) := ⟨by positivity⟩
    rw [DihedralGroup.one_def]
    change rotationPower k ζ hζ (0 : ZMod (3 ^ k)) = 1
    exact zmodPower_zero (rotation k ζ hζ)
  map_mul' := by
    intro x y
    cases x with
    | r i =>
      cases y with
      | r j =>
        rw [DihedralGroup.r_mul_r]
        exact rotationPower_add k ζ hζ i j
      | sr j =>
        rw [DihedralGroup.r_mul_sr]
        symm
        change rotationPower k ζ hζ i *
            (reflection k * rotationPower k ζ hζ j) =
          reflection k * rotationPower k ζ hζ (j - i)
        calc
          rotationPower k ζ hζ i *
              (reflection k * rotationPower k ζ hζ j) =
              (rotationPower k ζ hζ i * reflection k) *
                rotationPower k ζ hζ j := by rw [← mul_assoc]
          _ = (reflection k * rotationPower k ζ hζ (-i)) *
                rotationPower k ζ hζ j := by
                  rw [rotationPower_mul_reflection]
          _ = reflection k *
                (rotationPower k ζ hζ (-i) *
                  rotationPower k ζ hζ j) := by rw [mul_assoc]
          _ = reflection k * rotationPower k ζ hζ (j - i) := by
                rw [← rotationPower_add k ζ hζ (-i) j]
                congr 2
                abel
    | sr i =>
      cases y with
      | r j =>
        rw [DihedralGroup.sr_mul_r]
        symm
        change (reflection k * rotationPower k ζ hζ i) *
              rotationPower k ζ hζ j =
          reflection k * rotationPower k ζ hζ (i + j)
        calc
          (reflection k * rotationPower k ζ hζ i) *
              rotationPower k ζ hζ j =
              reflection k *
                (rotationPower k ζ hζ i * rotationPower k ζ hζ j) := by
                  rw [mul_assoc]
          _ = reflection k * rotationPower k ζ hζ (i + j) := by
                rw [← rotationPower_add k ζ hζ i j]
      | sr j =>
        rw [DihedralGroup.sr_mul_sr]
        symm
        change (reflection k * rotationPower k ζ hζ i) *
              (reflection k * rotationPower k ζ hζ j) =
          rotationPower k ζ hζ (j - i)
        calc
          (reflection k * rotationPower k ζ hζ i) *
              (reflection k * rotationPower k ζ hζ j) =
              (reflection k * rotationPower k ζ hζ i * reflection k) *
                rotationPower k ζ hζ j := by simp only [mul_assoc]
          _ = rotationPower k ζ hζ (-i) *
                rotationPower k ζ hζ j := by
                  rw [reflection_conjugates_rotationPower]
          _ = rotationPower k ζ hζ (j - i) := by
                rw [← rotationPower_add k ζ hζ (-i) j]
                congr 1
                abel

@[simp] theorem dihedralRepresentation_r (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (i : ZMod (3 ^ k)) :
    dihedralRepresentation k ζ hζ (.r i) =
      rotationPower k ζ hζ i := rfl

@[simp] theorem dihedralRepresentation_sr (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (i : ZMod (3 ^ k)) :
    dihedralRepresentation k ζ hζ (.sr i) =
      reflection k * rotationPower k ζ hζ i := rfl

theorem dihedralRepresentation_r_X (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (i : ZMod (3 ^ k)) :
    dihedralRepresentation k ζ hζ (.r i) (RatFunc.X : E) =
      RatFunc.C (ζ ^ i.val) * (RatFunc.X : E) := by
  let : NeZero (3 ^ k) := ⟨by positivity⟩
  simp [rotationPower, zmodPower, rotation_pow_apply_X]

theorem dihedralRepresentation_sr_X (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (i : ZMod (3 ^ k)) :
    dihedralRepresentation k ζ hζ (.sr i) (RatFunc.X : E) =
      RatFunc.C (ζ ^ i.val) * (RatFunc.X : E)⁻¹ := by
  let : NeZero (3 ^ k) := ⟨by positivity⟩
  simp [dihedralRepresentation, AlgEquiv.mul_apply, rotationPower,
    zmodPower, rotation_pow_apply_X, reflection_X, map_mul]

/-- No nonzero scalar multiple of X equals a constant multiple of X inverse. -/
theorem no_scalar_X_eq_inverse (a b : ℂ) (ha : a ≠ 0)
    (h : RatFunc.C a * (RatFunc.X : E) =
      RatFunc.C b * (RatFunc.X : E)⁻¹) : False := by
  have haC : RatFunc.C a ≠ (0 : E) := by
    intro h0
    apply ha
    exact RatFunc.C_injective (by simpa using h0)
  have hsq' : RatFunc.C a * (RatFunc.X : E) ^ 2 = RatFunc.C b := by
    calc
      RatFunc.C a * (RatFunc.X : E) ^ 2 =
          (RatFunc.C a * (RatFunc.X : E)) * (RatFunc.X : E) := by ring
      _ = (RatFunc.C b * (RatFunc.X : E)⁻¹) * (RatFunc.X : E) := by rw [h]
      _ = RatFunc.C b := by field_simp [RatFunc.X_ne_zero]
  have hsq : (RatFunc.X : E) ^ 2 =
      RatFunc.C (b / a) := by
    rw [map_div₀]
    apply (eq_div_iff haC).2
    calc
      (RatFunc.X : E) ^ 2 * RatFunc.C a =
          RatFunc.C a * (RatFunc.X : E) ^ 2 := mul_comm _ _
      _ = RatFunc.C b := hsq'
  exact LinearInputChebyshevNext.generic_square_not_constant (b / a) hsq

/-- Faithfulness follows by evaluating at the generic variable: the two
root-label families have distinct scalar powers, and the X and inverse-X
families cannot collide. -/
theorem dihedralRepresentation_injective (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    Function.Injective (dihedralRepresentation k ζ hζ) := by
  let : NeZero (3 ^ k) := ⟨by positivity⟩
  intro a b hab
  have heval : (dihedralRepresentation k ζ hζ a) (RatFunc.X : E) =
      (dihedralRepresentation k ζ hζ b) (RatFunc.X : E) :=
    congrArg (fun f : Aut k => f (RatFunc.X : E)) hab
  cases a with
  | r i =>
    cases b with
    | r j =>
      rw [dihedralRepresentation_r_X, dihedralRepresentation_r_X] at heval
      have hcoeff : ζ ^ i.val = ζ ^ j.val :=
        RatFunc.C_injective ((mul_right_cancel₀ RatFunc.X_ne_zero) heval)
      have hv := hζ.pow_inj (ZMod.val_lt i) (ZMod.val_lt j) hcoeff
      exact congrArg DihedralGroup.r
        ((ZMod.val_injective (3 ^ k)) hv)
    | sr j =>
      rw [dihedralRepresentation_r_X, dihedralRepresentation_sr_X] at heval
      have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
      exact False.elim
        (no_scalar_X_eq_inverse (ζ ^ i.val) (ζ ^ j.val)
          (pow_ne_zero _ hζ0) heval)
  | sr i =>
    cases b with
    | r j =>
      rw [dihedralRepresentation_sr_X, dihedralRepresentation_r_X] at heval
      have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
      exact False.elim
        (no_scalar_X_eq_inverse (ζ ^ j.val) (ζ ^ i.val)
          (pow_ne_zero _ hζ0) heval.symm)
    | sr j =>
      rw [dihedralRepresentation_sr_X, dihedralRepresentation_sr_X] at heval
      have hcoeff : ζ ^ i.val = ζ ^ j.val :=
        RatFunc.C_injective
          ((mul_right_cancel₀ (inv_ne_zero RatFunc.X_ne_zero)) heval)
      have hv := hζ.pow_inj (ZMod.val_lt i) (ZMod.val_lt j) hcoeff
      exact congrArg DihedralGroup.sr
        ((ZMod.val_injective (3 ^ k)) hv)

end LinearInputChebyshevAutomorphisms
