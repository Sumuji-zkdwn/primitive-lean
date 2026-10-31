/-!
# Variable-pair energy, cubic discriminants, and sign-orbit reduction

Additive bridges to the actual derivatives in VariablePairObservations,
the Chebyshev cubic in BranchForgetting, and the Kummer root-label viewpoint.

Claims are algebraic and use the displayed energy. The sign quotient is by
coordinate reflections on (x,y), not a quotient of all 15 variable-pair slices:
fixed parameters and excluded domains must also be transformed.
-/

noncomputable section

namespace LinearInputVariablePairGalois

open LinearInputVariablePairs

/-- Eliminate the stationary y-coordinate when a is nonzero. -/
def stationaryY (a c x : ℝ) : ℝ := c * x / a

/-- Schur-complement coefficient after completing the square in y. -/
def reducedB (k a c : ℝ) : ℝ := k - c ^ 2 / a

/-- The cubic obtained from the actual two-variable Euler equation. -/
def reducedCubic (lam b u x : ℝ) : ℝ := lam * x ^ 3 + b * x - u

/-- Derivative of the reduced stationarity polynomial. -/
def cubicDerivative (lam b x : ℝ) : ℝ := 3 * lam * x ^ 2 + b

/-- The discriminant of lam*x^3 + b*x - u, without dividing by lam. -/
def cubicDiscriminant (lam b u : ℝ) : ℝ :=
  -4 * lam * b ^ 3 - 27 * lam ^ 2 * u ^ 2

/-- The actual determinant of the derivative of the original gradient map. -/
def hessianDet (k lam a c u x y : ℝ) : ℝ :=
  jacobianPair
    (fun v w => (gradXY k lam a c u (v, w)).1)
    (fun v w => (gradXY k lam a c u (v, w)).2) x y

/-- Substitution of the second stationarity condition into both gradient
components. This is not a new postulated force law. -/
theorem gradient_at_stationaryY (k lam a c u x : ℝ) (ha : a ≠ 0) :
    gradXY k lam a c u (x, stationaryY a c x) =
      (reducedCubic lam (reducedB k a c) u x, 0) := by
  rw [gradXY_formula]
  apply Prod.ext
  · dsimp [stationaryY, reducedCubic, reducedB]
    field_simp [ha]
    ring
  · dsimp [stationaryY]
    field_simp [ha]
    ring

/-- Every and only stationary point is a root of the reduced cubic, with its
unique stationary y-coordinate. -/
theorem stationary_iff_reduced_cubic (k lam a c u x y : ℝ) (ha : a ≠ 0) :
    gradXY k lam a c u (x, y) = (0, 0) ↔
      y = stationaryY a c x ∧ reducedCubic lam (reducedB k a c) u x = 0 := by
  constructor
  · intro h
    have hy : a * y - c * x = 0 := by
      have h' := congrArg Prod.snd h
      simpa only [gradXY_formula, Prod.snd] using h'
    have hyy : y = stationaryY a c x := by
      unfold stationaryY
      apply (eq_div_iff ha).2
      nlinarith [hy]
    refine ⟨hyy, ?_⟩
    rw [hyy, gradient_at_stationaryY k lam a c u x ha] at h
    exact congrArg Prod.fst h
  · rintro ⟨rfl, hc⟩
    rw [gradient_at_stationaryY k lam a c u x ha]
    simp [hc]

/-- The original Hessian determinant factors through the cubic derivative. -/
theorem hessian_eq_reduced_derivative (k lam a c u x y : ℝ) (ha : a ≠ 0) :
    hessianDet k lam a c u x y =
      a * cubicDerivative lam (reducedB k a c) x := by
  unfold hessianDet
  rw [gradXY_jacobian]
  unfold cubicDerivative reducedB
  field_simp [ha]
  ring

theorem hessian_zero_iff_cubic_derivative_zero
    (k lam a c u x y : ℝ) (ha : a ≠ 0) :
    hessianDet k lam a c u x y = 0 ↔
      cubicDerivative lam (reducedB k a c) x = 0 := by
  rw [hessian_eq_reduced_derivative k lam a c u x y ha]
  simp [ha]

/-- A repeated stationary root forces the depressed cubic's discriminant to
vanish; no unsupported converse for arbitrary real parameters is assumed. -/
theorem discriminant_zero_of_common_root (lam b u x : ℝ)
    (hroot : reducedCubic lam b u x = 0)
    (hder : cubicDerivative lam b x = 0) :
    cubicDiscriminant lam b u = 0 := by
  have hb : b = -(3 * lam * x ^ 2) := by
    unfold cubicDerivative at hder
    linarith
  have hu : u = -(2 * lam * x ^ 3) := by
    unfold reducedCubic at hroot
    rw [hb] at hroot
    nlinarith [hroot]
  rw [hb, hu]
  unfold cubicDiscriminant
  ring

theorem derivative_ne_zero_of_discriminant_ne_zero
    (lam b u x : ℝ) (hd : cubicDiscriminant lam b u ≠ 0)
    (hroot : reducedCubic lam b u x = 0) :
    cubicDerivative lam b x ≠ 0 := by
  intro hder
  exact hd (discriminant_zero_of_common_root lam b u x hroot hder)

theorem stationary_degenerate_implies_discriminant_zero
    (k lam a c u x y : ℝ) (ha : a ≠ 0)
    (hs : gradXY k lam a c u (x, y) = (0, 0))
    (hh : hessianDet k lam a c u x y = 0) :
    cubicDiscriminant lam (reducedB k a c) u = 0 := by
  have hroot := (stationary_iff_reduced_cubic k lam a c u x y ha).mp hs
  have hder := (hessian_zero_iff_cubic_derivative_zero
    k lam a c u x y ha).mp hh
  exact discriminant_zero_of_common_root
    lam (reducedB k a c) u x hroot.2 hder

/-- The depressed cubic is a rescaled Chebyshev cubic whenever the
coefficients admit the chosen scale (a model condition, not automatic). -/
theorem reduced_cubic_chebyshev (lam b u s t : ℝ)
    (hs : 3 * lam * s ^ 2 = -4 * b) :
    reducedCubic lam b u (s * t) =
      lam * s ^ 3 / 4 * LinearInputBranchForgetting.chebyshevThree t - u := by
  have hbs : b * s = -(3 * lam * s ^ 3) / 4 := by
    have h := congrArg (fun z : ℝ => z * s) hs
    nlinarith [h]
  unfold reducedCubic LinearInputBranchForgetting.chebyshevThree
  calc
    lam * (s * t) ^ 3 + b * (s * t) - u =
        lam * s ^ 3 * t ^ 3 + (b * s) * t - u := by ring
    _ = lam * s ^ 3 / 4 * (4 * t ^ 3 - 3 * t) - u := by
      rw [hbs]
      ring

theorem reduced_cubic_chebyshev_special (x u : ℝ) :
    reducedCubic 4 (-3) u x =
      LinearInputBranchForgetting.chebyshevThree x - u := by
  unfold reducedCubic LinearInputBranchForgetting.chebyshevThree
  ring

theorem chebyshev_discriminant (u : ℝ) :
    cubicDiscriminant 4 (-3) u = 432 * (1 - u ^ 2) := by
  unfold cubicDiscriminant
  ring

theorem chebyshev_discriminant_critical_iff (u : ℝ) :
    cubicDiscriminant 4 (-3) u = 0 ↔ u = 1 ∨ u = -1 := by
  rw [chebyshev_discriminant]
  constructor
  · intro h
    have hsq : u ^ 2 = 1 := by nlinarith [h]
    have hf : (u - 1) * (u + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Flipping y toggles the xy sign; flipping x toggles xy and ux signs. -/
def flipX (σ : Fin 5 → Bool) : Fin 5 → Bool :=
  fun i => if i = (3 : Fin 5) ∨ i = (4 : Fin 5) then !σ i else σ i

def flipY (σ : Fin 5 → Bool) : Fin 5 → Bool :=
  fun i => if i = (3 : Fin 5) then !σ i else σ i

theorem signValue_not (b : Bool) :
    signValue (!b) = -signValue b := by
  cases b <;> norm_num [signValue]

theorem signedEnergy_flipX (σ : Fin 5 → Bool) (k lam a c x y u : ℝ) :
    signedEnergy (flipX σ) k lam a c x y u =
      signedEnergy σ k lam a c (-x) y u := by
  rw [signedEnergy_expansion, signedEnergy_expansion]
  simp [flipX, signValue_not]
  exact Or.inl (by ring)

theorem signedEnergy_flipY (σ : Fin 5 → Bool) (k lam a c x y u : ℝ) :
    signedEnergy (flipY σ) k lam a c x y u =
      signedEnergy σ k lam a c x (-y) u := by
  rw [signedEnergy_expansion, signedEnergy_expansion]
  simp [flipY, signValue_not]

theorem flipX_involutive (σ : Fin 5 → Bool) : flipX (flipX σ) = σ := by
  funext i
  by_cases h : i = (3 : Fin 5) ∨ i = (4 : Fin 5)
  · simp [flipX, h]
  · simp [flipX, h]

theorem flipY_involutive (σ : Fin 5 → Bool) : flipY (flipY σ) = σ := by
  funext i
  by_cases h : i = (3 : Fin 5)
  · simp [flipY, h]
  · simp [flipY, h]

/-- Retain only the three coefficient signs unchanged by x/y reflections. -/
def signShape (σ : Fin 5 → Bool) : Fin 3 → Bool :=
  fun i => σ ⟨i.val, by omega⟩

/-- A representative with the xy and ux signs both chosen positive. -/
def signCanonical (τ : Fin 3 → Bool) : Fin 5 → Bool :=
  fun i => if hi : i.val < 3 then τ ⟨i.val, hi⟩ else true

theorem signShape_canonical (τ : Fin 3 → Bool) :
    signShape (signCanonical τ) = τ := by
  funext i
  simp [signShape, signCanonical, i.isLt]

theorem signShape_flipX (σ : Fin 5 → Bool) :
    signShape (flipX σ) = signShape σ := by
  funext i
  fin_cases i <;> simp [signShape, flipX]

theorem signShape_flipY (σ : Fin 5 → Bool) :
    signShape (flipY σ) = signShape σ := by
  funext i
  fin_cases i <;> simp [signShape, flipY]

theorem signShape_surjective : Function.Surjective signShape := by
  intro τ
  exact ⟨signCanonical τ, signShape_canonical τ⟩

/-- There are exactly eight images of the thirty-two sign patterns under
the invariant that forgets the two coordinate-reflection signs. -/
theorem signShape_eight :
    (Finset.univ.image signShape : Finset (Fin 3 → Bool)).card = 8 := by
  classical
  have heq : (Finset.univ.image signShape : Finset (Fin 3 → Bool)) = Finset.univ := by
    ext τ
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact signShape_surjective τ
  rw [heq]
  norm_num [Fintype.card_fun]


/-!
The preceding 8-valued shape invariant was known.  We now prove that it is
*complete*: two formal sign patterns have the same shape if and only if they
are connected by the four coordinate reflections (identity, flipX, flipY,
flipX after flipY).  The quotient therefore has exactly eight classes.

The result concerns formal signs with the coordinate variables transformed.
It is not a claim that all parameter-fixed variable-pair slices are
interchangeable, or that degenerate zero coefficients create no extra
identifications of actual functions.
-/

/-- Any two unequal booleans are logical complements. -/
theorem bool_eq_not_of_ne (b c : Bool) (h : b ≠ c) : b = !c := by
  cases b <;> cases c <;> simp_all

/-- The orbit generated by the two coordinate reflections, enumerated in
four steps. -/
def sameReflectionOrbit (σ τ : Fin 5 → Bool) : Prop :=
  τ = σ ∨ τ = flipY σ ∨ τ = flipX σ ∨ τ = flipX (flipY σ)

/-- The three preserved coefficient signs completely classify reflection
orbits.  In particular, this is stronger than mere invariance of signShape. -/
theorem sameReflectionOrbit_iff_signShape (σ τ : Fin 5 → Bool) :
    sameReflectionOrbit σ τ ↔ signShape τ = signShape σ := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · rfl
    · exact signShape_flipY σ
    · exact signShape_flipX σ
    · rw [signShape_flipX, signShape_flipY]
  · intro h
    have h0 : τ 0 = σ 0 := by
      have hv := congrFun h (0 : Fin 3)
      simpa [signShape] using hv
    have h1 : τ 1 = σ 1 := by
      have hv := congrFun h (1 : Fin 3)
      simpa [signShape] using hv
    have h2 : τ 2 = σ 2 := by
      have hv := congrFun h (2 : Fin 3)
      simpa [signShape] using hv
    by_cases h4 : τ 4 = σ 4
    · by_cases h3 : τ 3 = σ 3
      · left
        funext i
        fin_cases i <;> simp [h0, h1, h2, h3, h4]
      · right; left
        have h3' : τ 3 = !σ 3 := bool_eq_not_of_ne _ _ h3
        funext i
        fin_cases i <;> simp [flipY, h0, h1, h2, h3', h4]
    · by_cases h3 : τ 3 = σ 3
      · right; right; right
        have h4' : τ 4 = !σ 4 := bool_eq_not_of_ne _ _ h4
        funext i
        fin_cases i <;> simp [flipX, flipY, h0, h1, h2, h3, h4']
      · right; right; left
        have h3' : τ 3 = !σ 3 := bool_eq_not_of_ne _ _ h3
        have h4' : τ 4 = !σ 4 := bool_eq_not_of_ne _ _ h4
        funext i
        fin_cases i <;> simp [flipX, h0, h1, h2, h3', h4']

/-- Every sign pattern is equivalent to the canonical representative with
its last two signs set to positive. -/
theorem sameReflectionOrbit_canonical (σ : Fin 5 → Bool) :
    sameReflectionOrbit σ (signCanonical (signShape σ)) :=
  (sameReflectionOrbit_iff_signShape σ _).2 (signShape_canonical _)

/-- The precise equivalence relation induced by coordinate reflections. -/
def signOrbitSetoid : Setoid (Fin 5 → Bool) where
  r σ τ := signShape σ = signShape τ
  iseqv := {
    refl := by intro σ; rfl
    symm := by intro σ τ h; exact h.symm
    trans := by intro σ τ υ h₁ h₂; exact h₁.trans h₂
  }

theorem sameReflectionOrbit_iff_setoid (σ τ : Fin 5 → Bool) :
    sameReflectionOrbit σ τ ↔ signOrbitSetoid.r σ τ := by
  constructor
  · intro h
    exact ((sameReflectionOrbit_iff_signShape σ τ).mp h).symm
  · intro h
    exact (sameReflectionOrbit_iff_signShape σ τ).2 h.symm

/-- The quotient by actual x/y-reflection orbits is equivalent to exactly
three Boolean coefficient signs. -/
noncomputable def signOrbitEquiv :
    Quotient signOrbitSetoid ≃ (Fin 3 → Bool) where
  toFun := Quotient.lift signShape (by
    intro σ τ h
    exact h)
  invFun := fun θ => Quotient.mk signOrbitSetoid (signCanonical θ)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro σ
    apply Quotient.sound
    exact signShape_canonical _
  right_inv := signShape_canonical

/-- There are exactly eight orbits, not merely eight invariant labels. -/
theorem reflectionOrbit_count_eight :
    Nat.card (Quotient signOrbitSetoid) = 8 := by
  calc
    Nat.card (Quotient signOrbitSetoid) = Nat.card (Fin 3 → Bool) :=
      Nat.card_congr signOrbitEquiv
    _ = 8 := by norm_num [Nat.card_eq_fintype_card, Fintype.card_fun]

/-- Every orbit equivalence preserves the energy after the corresponding
coordinate reflections; this does not keep fixed numerical coordinates. -/
theorem sameReflectionOrbit_energy (σ τ : Fin 5 → Bool)
    (h : sameReflectionOrbit σ τ) :
    ∃ bx byFlag : Bool, ∀ k lam a c x y u : ℝ,
      signedEnergy τ k lam a c x y u =
        signedEnergy σ k lam a c
          (if bx then -x else x) (if byFlag then -y else y) u := by
  rcases h with h | h | h | h
  · refine ⟨false, false, ?_⟩
    intro k lam a c x y u
    simpa [h]
  · refine ⟨false, true, ?_⟩
    intro k lam a c x y u
    simpa [h] using signedEnergy_flipY σ k lam a c x y u
  · refine ⟨true, false, ?_⟩
    intro k lam a c x y u
    simpa [h] using signedEnergy_flipX σ k lam a c x y u
  · refine ⟨true, true, ?_⟩
    intro k lam a c x y u
    simp only [if_true, h]
    calc
      signedEnergy (flipX (flipY σ)) k lam a c x y u =
        signedEnergy (flipY σ) k lam a c (-x) y u :=
          signedEnergy_flipX (flipY σ) k lam a c x y u
      _ = signedEnergy σ k lam a c (-x) (-y) u :=
          signedEnergy_flipY σ k lam a c (-x) y u


end LinearInputVariablePairGalois
