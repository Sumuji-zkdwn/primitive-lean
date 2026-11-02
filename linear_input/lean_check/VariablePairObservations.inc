/-!
Variable-pair observations of the polynomial family in the Research note.
Actual partial derivatives are used throughout. The existing primitive energy
is a specialization, and no inverse is inferred from a constant Jacobian alone.
-/

noncomputable section
open Real

namespace LinearInputVariablePairs

def energy (k lam a c x y u : ℝ) : ℝ :=
  k * x ^ 2 / 2 + lam * x ^ 4 / 4 + a * y ^ 2 / 2 - c * x * y - u * x

theorem energy_eq_primitive (lam r u x y : ℝ) :
    energy (r + 2) lam 1 (sqrt 2) x y u = LinearInputDesign.E lam r u x y := by
  have hs : (sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold energy LinearInputDesign.E LinearInputDesign.f
  ring_nf
  rw [hs]
  ring

theorem energy_complete_square (k lam a c x y u : ℝ) (ha : a ≠ 0) :
    energy k lam a c x y u =
      lam * x ^ 4 / 4 + (k - c ^ 2 / a) * x ^ 2 / 2 - u * x +
        a / 2 * (y - c * x / a) ^ 2 := by
  unfold energy
  field_simp
  ring

theorem energy_eq_linear_observation (k lam a c u : ℝ) (z : ℝ × ℝ) :
    energy k lam a c z.1 z.2 u =
      LinearInputObservation.energy
        (fun w : ℝ × ℝ => energy k lam a c w.1 w.2 0) Prod.fst u z := by
  unfold energy LinearInputObservation.energy
  ring

/-- These are derivatives of the displayed polynomial, not postulated forces. -/
theorem hasDerivAt_energy_x (k lam a c x y u : ℝ) :
    HasDerivAt (fun t => energy k lam a c t y u)
      (k * x + lam * x ^ 3 - c * y - u) x := by
  have h := ((((hasDerivAt_id x).pow 2).const_mul k).div_const 2).add
    ((((hasDerivAt_id x).pow 4).const_mul lam).div_const 4)
  convert ((h.add_const (a * y ^ 2 / 2)).sub
    (((hasDerivAt_id x).const_mul c).mul_const y)).sub
    ((hasDerivAt_id x).const_mul u) using 1
  simp only [id_eq]
  ring

theorem hasDerivAt_energy_y (k lam a c x y u : ℝ) :
    HasDerivAt (fun t => energy k lam a c x t u) (a * y - c * x) y := by
  have h := ((((hasDerivAt_id y).pow 2).const_mul a).div_const 2).const_add
    (k * x ^ 2 / 2 + lam * x ^ 4 / 4)
  convert (h.sub ((hasDerivAt_id y).const_mul (c * x))).sub_const (u * x)
    using 1
  simp only [id_eq]
  ring

/-- The input coefficient s is kept explicit; s=-1 recovers the original energy. -/
def gradXu (k lam a c s y : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun t => energy k lam a c t y (-s * z.2)) z.1,
   deriv (fun t => energy k lam a c z.1 y (-s * t)) z.2)

theorem hasDerivAt_signed_input (k lam a c s x y u : ℝ) :
    HasDerivAt (fun t => energy k lam a c x y (-s * t)) (s * x) u := by
  have hf : (fun t => energy k lam a c x y (-s * t)) =
      fun t => (k * x ^ 2 / 2 + lam * x ^ 4 / 4 + a * y ^ 2 / 2 - c * x * y) +
        (s * x) * t := by
    funext t
    unfold energy
    ring
  rw [hf]
  simpa using ((hasDerivAt_id u).const_mul (s * x)).const_add
    (k * x ^ 2 / 2 + lam * x ^ 4 / 4 + a * y ^ 2 / 2 - c * x * y)

theorem gradXu_formula (k lam a c s y : ℝ) (z : ℝ × ℝ) :
    gradXu k lam a c s y z =
      (k * z.1 + lam * z.1 ^ 3 - c * y + s * z.2, s * z.1) := by
  unfold gradXu
  rw [(hasDerivAt_energy_x k lam a c z.1 y (-s * z.2)).deriv,
    (hasDerivAt_signed_input k lam a c s z.1 y z.2).deriv]
  congr 1
  ring

def inverseXu (k lam c s y : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2 / s, (z.1 - k * (z.2 / s) - lam * (z.2 / s) ^ 3 + c * y) / s)

theorem inverseXu_gradXu (k lam a c s y : ℝ) (hs : s ≠ 0) (z : ℝ × ℝ) :
    inverseXu k lam c s y (gradXu k lam a c s y z) = z := by
  rw [gradXu_formula]
  apply Prod.ext <;> dsimp [inverseXu]
  · field_simp
  · field_simp
    ring

theorem gradXu_inverseXu (k lam a c s y : ℝ) (hs : s ≠ 0) (z : ℝ × ℝ) :
    gradXu k lam a c s y (inverseXu k lam c s y z) = z := by
  rw [gradXu_formula]
  apply Prod.ext <;> dsimp [inverseXu]
  · field_simp
    ring
  · field_simp

theorem gradXu_injective (k lam a c s y : ℝ) (hs : s ≠ 0) :
    Function.Injective (gradXu k lam a c s y) := by
  intro z w h
  have hh := congrArg (inverseXu k lam c s y) h
  simpa only [inverseXu_gradXu k lam a c s y hs] using hh

theorem gradXu_bijective (k lam a c s y : ℝ) (hs : s ≠ 0) :
    Function.Bijective (gradXu k lam a c s y) := by
  refine ⟨gradXu_injective k lam a c s y hs, ?_⟩
  intro z
  exact ⟨inverseXu k lam c s y z, gradXu_inverseXu k lam a c s y hs z⟩

theorem gradXu_zero_not_injective (k lam a c y : ℝ) :
    ¬ Function.Injective (gradXu k lam a c 0 y) := by
  intro h
  have he : gradXu k lam a c 0 y (0, 0) = gradXu k lam a c 0 y (0, 1) := by
    simp only [gradXu_formula, zero_mul]
  have hu := congrArg Prod.snd (h he)
  norm_num at hu

theorem gradXu_bijective_iff (k lam a c s y : ℝ) :
    Function.Bijective (gradXu k lam a c s y) ↔ s ≠ 0 := by
  constructor
  · intro h hs
    subst s
    exact gradXu_zero_not_injective k lam a c y h.1
  · exact gradXu_bijective k lam a c s y

/-- The actual determinant of two scalar observations of two real variables. -/
def jacobianPair (f g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x * deriv (fun t => g x t) y -
    deriv (fun t => f x t) y * deriv (fun t => g t y) x

theorem gradXu_jacobian (k lam a c s y x u : ℝ) :
    jacobianPair
      (fun v w => (gradXu k lam a c s y (v, w)).1)
      (fun v w => (gradXu k lam a c s y (v, w)).2) x u = -s ^ 2 := by
  have hx : HasDerivAt (fun t : ℝ => k * t + lam * t ^ 3 - c * y + s * u)
      (k + 3 * lam * x ^ 2) x := by
    convert ((((hasDerivAt_id x).const_mul k).add
      (((hasDerivAt_id x).pow 3).const_mul lam)).sub_const (c * y)).add_const (s * u)
      using 1
    simp only [id_eq]
    ring
  have hu : HasDerivAt (fun t : ℝ => k * x + lam * x ^ 3 - c * y + s * t) s u := by
    simpa using ((hasDerivAt_id u).const_mul s).const_add (k * x + lam * x ^ 3 - c * y)
  have hqx : HasDerivAt (fun t : ℝ => s * t) s x := by
    simpa using (hasDerivAt_id x).const_mul s
  simp only [jacobianPair, gradXu_formula]
  rw [hx.deriv, hu.deriv, (hasDerivAt_const u (s * x)).deriv,
    hqx.deriv]
  ring

def signValue (b : Bool) : ℝ := if b then 1 else -1

theorem signValue_sq (b : Bool) : signValue b ^ 2 = 1 := by
  cases b <;> norm_num [signValue]

theorem signValue_ne_zero (b : Bool) : signValue b ≠ 0 := by
  cases b <;> norm_num [signValue]

theorem sign_pattern_count : Fintype.card (Fin 5 → Bool) = 32 := by
  norm_num [Fintype.card_fun]

/-- True selects +1 and false selects -1 in the five displayed terms. -/
def signedEnergy (σ : Fin 5 → Bool) (k lam a c x y u : ℝ) : ℝ :=
  energy (signValue (σ 0) * k) (signValue (σ 1) * lam)
    (signValue (σ 2) * a) (-signValue (σ 3) * c) x y (-signValue (σ 4) * u)

theorem signedEnergy_expansion (σ : Fin 5 → Bool) (k lam a c x y u : ℝ) :
    signedEnergy σ k lam a c x y u =
      signValue (σ 0) * k * x ^ 2 / 2 + signValue (σ 1) * lam * x ^ 4 / 4 +
      signValue (σ 2) * a * y ^ 2 / 2 + signValue (σ 3) * c * x * y +
      signValue (σ 4) * u * x := by
  unfold signedEnergy energy
  ring

def signedGradXu (σ : Fin 5 → Bool) (k lam a c y : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun t => signedEnergy σ k lam a c t y z.2) z.1,
   deriv (fun t => signedEnergy σ k lam a c z.1 y t) z.2)

theorem signedGradXu_eq (σ : Fin 5 → Bool) (k lam a c y : ℝ) (z : ℝ × ℝ) :
    signedGradXu σ k lam a c y z =
      gradXu (signValue (σ 0) * k) (signValue (σ 1) * lam)
        (signValue (σ 2) * a) (-signValue (σ 3) * c) (signValue (σ 4)) y z := by
  rfl

theorem signedGradXu_bijective (σ : Fin 5 → Bool) (k lam a c y : ℝ) :
    Function.Bijective (signedGradXu σ k lam a c y) := by
  simpa only [signedGradXu_eq] using
    gradXu_bijective (signValue (σ 0) * k) (signValue (σ 1) * lam)
      (signValue (σ 2) * a) (-signValue (σ 3) * c) (signValue (σ 4)) y
      (signValue_ne_zero (σ 4))

theorem signedGradXu_jacobian (σ : Fin 5 → Bool) (k lam a c y x u : ℝ) :
    jacobianPair (fun v w => (signedGradXu σ k lam a c y (v, w)).1)
      (fun v w => (signedGradXu σ k lam a c y (v, w)).2) x u = -1 := by
  simp only [signedGradXu_eq, gradXu_jacobian, signValue_sq]

theorem chebyshev_energy (x u : ℝ) :
    energy (-3) 4 0 0 x 0 u = LinearInputCalculus.potential 4 (-3) u x := by
  unfold energy LinearInputCalculus.potential
  ring

theorem chebyshev_gradient (x u : ℝ) :
    gradXu (-3) 4 0 0 (-1) 0 (x, u) =
      (LinearInputBranchForgetting.chebyshevThree x - u, -x) := by
  rw [gradXu_formula]
  unfold LinearInputBranchForgetting.chebyshevThree
  apply Prod.ext <;> dsimp <;> ring

theorem chebyshev_stationary_fiber (x u : ℝ) :
    (gradXu (-3) 4 0 0 (-1) 0 (x, u)).1 = 0 ↔
      u = LinearInputBranchForgetting.chebyshevThree x := by
  rw [chebyshev_gradient]
  change LinearInputBranchForgetting.chebyshevThree x - u = 0 ↔ _
  constructor <;> intro h <;> linarith

/-- An invertible encoding of each paired observation preserves every cutoff. -/
theorem gradient_preserves_observation_hierarchy {S : Type*}
    (obs : ℕ → S → ℝ × ℝ) (m : ℕ) (z w : S)
    (k lam a c s y : ℝ) (hs : s ≠ 0) :
    LinearInputHistorySignature.agreeThrough
      (fun n t => gradXu k lam a c s y (obs n t)) m z w ↔
      LinearInputHistorySignature.agreeThrough obs m z w := by
  constructor
  · intro h n hn
    exact gradXu_injective k lam a c s y hs (h n hn)
  · intro h n hn
    exact congrArg (gradXu k lam a c s y) (h n hn)

/-- Specialize the previously proved forgetting condition to the actual energy family. -/
theorem actual_energy_minimum_forgets (k lam a c : ℝ) (p q r : ℝ × ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : q.1 = (1 - t) * p.1 + t * r.1)
    (hE : (1 - t) * energy k lam a c p.1 p.2 0 +
      t * energy k lam a c r.1 r.2 0 ≤ energy k lam a c q.1 q.2 0) :
    (fun u => min (min (energy k lam a c p.1 p.2 u) (energy k lam a c r.1 r.2 u))
      (energy k lam a c q.1 q.2 u)) =
    (fun u => min (energy k lam a c p.1 p.2 u) (energy k lam a c r.1 r.2 u)) := by
  have h := LinearInputBranchForgetting.minimum_forgets_hidden_state
    (fun z : ℝ × ℝ => energy k lam a c z.1 z.2 0) Prod.fst p q r t ht0 ht1 hx hE
  simpa only [← energy_eq_linear_observation] using h

/-- A concrete hidden candidate in the same Chebyshev energy family. -/
theorem chebyshev_minimum_forgets_zero :
    (fun u => min (min (energy (-3) 4 0 0 (-1) 0 u) (energy (-3) 4 0 0 1 0 u))
      (energy (-3) 4 0 0 0 0 u)) =
    (fun u => min (energy (-3) 4 0 0 (-1) 0 u) (energy (-3) 4 0 0 1 0 u)) := by
  exact actual_energy_minimum_forgets (-3) 4 0 0 (-1, 0) (0, 0) (1, 0) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [energy])

def gradXY (k lam a c u : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun t => energy k lam a c t z.2 u) z.1,
   deriv (fun t => energy k lam a c z.1 t u) z.2)

theorem gradXY_formula (k lam a c u : ℝ) (z : ℝ × ℝ) :
    gradXY k lam a c u z =
      (k * z.1 + lam * z.1 ^ 3 - c * z.2 - u, a * z.2 - c * z.1) := by
  exact Prod.ext (hasDerivAt_energy_x k lam a c z.1 z.2 u).deriv
    (hasDerivAt_energy_y k lam a c z.1 z.2 u).deriv

theorem gradXY_jacobian (k lam a c u x y : ℝ) :
    jacobianPair (fun v w => (gradXY k lam a c u (v, w)).1)
      (fun v w => (gradXY k lam a c u (v, w)).2) x y =
        a * (k + 3 * lam * x ^ 2) - c ^ 2 := by
  have hxx : HasDerivAt (fun t : ℝ => k * t + lam * t ^ 3 - c * y - u)
      (k + 3 * lam * x ^ 2) x := by
    convert ((((hasDerivAt_id x).const_mul k).add
      (((hasDerivAt_id x).pow 3).const_mul lam)).sub_const (c * y)).sub_const u using 1
    simp only [id_eq]
    ring
  have hxy : HasDerivAt (fun t : ℝ => k * x + lam * x ^ 3 - c * t - u) (-c) y := by
    simpa using (((hasDerivAt_id y).const_mul c).const_sub
      (k * x + lam * x ^ 3)).sub_const u
  have hyx : HasDerivAt (fun t : ℝ => a * y - c * t) (-c) x := by
    simpa using ((hasDerivAt_id x).const_mul c).const_sub (a * y)
  have hyy : HasDerivAt (fun t : ℝ => a * t - c * x) a y := by
    simpa using ((hasDerivAt_id y).const_mul a).sub_const (c * x)
  simp only [jacobianPair, gradXY_formula]
  rw [hxx.deriv, hxy.deriv, hyx.deriv, hyy.deriv]
  ring

theorem signed_xy_jacobian (σ : Fin 5 → Bool) (k lam a c u x y : ℝ) :
    jacobianPair
      (fun v w => deriv (fun t => signedEnergy σ k lam a c t w u) v)
      (fun v w => deriv (fun t => signedEnergy σ k lam a c v t u) w) x y =
      signValue (σ 2) * a * (signValue (σ 0) * k +
        3 * signValue (σ 1) * lam * x ^ 2) - c ^ 2 := by
  change jacobianPair
    (fun v w => (gradXY (signValue (σ 0) * k) (signValue (σ 1) * lam)
      (signValue (σ 2) * a) (-signValue (σ 3) * c) (-signValue (σ 4) * u) (v, w)).1)
    (fun v w => (gradXY (signValue (σ 0) * k) (signValue (σ 1) * lam)
      (signValue (σ 2) * a) (-signValue (σ 3) * c) (-signValue (σ 4) * u) (v, w)).2)
    x y = _
  rw [gradXY_jacobian]
  ring_nf
  rw [signValue_sq]
  ring

def plusEnergy (x y : ℝ) : ℝ := energy 1 0 1 1 x y 1

def minusEnergy (x y : ℝ) : ℝ := energy 1 0 (-1) 1 x y 1

def plusCoordinates (z : ℝ × ℝ) : ℝ × ℝ := (plusEnergy z.1 z.2, z.1 - z.2)

def inversePlusCoordinates (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2 ^ 2 / 2 - z.1, z.2 ^ 2 / 2 - z.1 - z.2)

theorem inverse_plus_coordinates (z : ℝ × ℝ) :
    inversePlusCoordinates (plusCoordinates z) = z := by
  apply Prod.ext <;> dsimp [inversePlusCoordinates, plusCoordinates, plusEnergy, energy] <;> ring

theorem plus_coordinates_inverse (z : ℝ × ℝ) :
    plusCoordinates (inversePlusCoordinates z) = z := by
  apply Prod.ext <;> dsimp [inversePlusCoordinates, plusCoordinates, plusEnergy, energy] <;> ring

theorem plus_coordinates_bijective : Function.Bijective plusCoordinates := by
  constructor
  · intro z w h
    have hh := congrArg inversePlusCoordinates h
    simpa only [inverse_plus_coordinates] using hh
  · intro z
    exact ⟨inversePlusCoordinates z, plus_coordinates_inverse z⟩

theorem plus_unit_jacobian_mate (x y : ℝ) :
    jacobianPair plusEnergy (fun v w => v - w) x y = 1 := by
  have hqx : HasDerivAt (fun t : ℝ => t - y) 1 x := (hasDerivAt_id x).sub_const y
  have hqy : HasDerivAt (fun t : ℝ => x - t) (-1) y := (hasDerivAt_id y).const_sub x
  unfold jacobianPair plusEnergy
  rw [(hasDerivAt_energy_x 1 0 1 1 x y 1).deriv,
    (hasDerivAt_energy_y 1 0 1 1 x y 1).deriv, hqx.deriv, hqy.deriv]
  ring

theorem plus_gradient_not_injective : ¬ Function.Injective (gradXY 1 0 1 1 1) := by
  intro h
  have he : gradXY 1 0 1 1 1 (0, 0) = gradXY 1 0 1 1 1 (1, 1) := by
    norm_num [gradXY_formula]
  have hx := congrArg Prod.fst (h he)
  norm_num at hx

theorem plus_gradient_jacobian (x y : ℝ) :
    jacobianPair (fun v w => (gradXY 1 0 1 1 1 (v, w)).1)
      (fun v w => (gradXY 1 0 1 1 1 (v, w)).2) x y = 0 := by
  rw [gradXY_jacobian]
  ring

/-- A critical point prevents any unit-Jacobian mate, in particular any polynomial mate. -/
theorem no_mate_at_critical_point (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : deriv (fun t => f t y) x = 0) (hy : deriv (fun t => f x t) y = 0) :
    ¬ ∃ g : ℝ → ℝ → ℝ, ∀ v w, jacobianPair f g v w = 1 := by
  rintro ⟨g, hg⟩
  have h := hg x y
  simp only [jacobianPair, hx, hy, zero_mul, sub_self] at h
  norm_num at h

theorem minus_critical_point : gradXY 1 0 (-1) 1 1 (1 / 2, -1 / 2) = (0, 0) := by
  norm_num [gradXY_formula]

theorem minus_no_unit_jacobian_mate :
    ¬ ∃ g : ℝ → ℝ → ℝ, ∀ x y, jacobianPair minusEnergy g x y = 1 := by
  apply no_mate_at_critical_point minusEnergy (1 / 2) (-1 / 2)
  · change deriv (fun t => energy 1 0 (-1) 1 t (-1 / 2) 1) (1 / 2) = 0
    rw [(hasDerivAt_energy_x 1 0 (-1) 1 (1 / 2) (-1 / 2) 1).deriv]
    norm_num
  · change deriv (fun t => energy 1 0 (-1) 1 (1 / 2) t 1) (-1 / 2) = 0
    rw [(hasDerivAt_energy_y 1 0 (-1) 1 (1 / 2) (-1 / 2) 1).deriv]
    norm_num

def inverseMinusGradient (z : ℝ × ℝ) : ℝ × ℝ :=
  ((z.1 - z.2 + 1) / 2, -(z.1 + z.2 + 1) / 2)

theorem inverse_minus_gradient (z : ℝ × ℝ) :
    inverseMinusGradient (gradXY 1 0 (-1) 1 1 z) = z := by
  rw [gradXY_formula]
  apply Prod.ext <;> dsimp [inverseMinusGradient] <;> ring

theorem minus_gradient_inverse (z : ℝ × ℝ) :
    gradXY 1 0 (-1) 1 1 (inverseMinusGradient z) = z := by
  rw [gradXY_formula]
  apply Prod.ext <;> dsimp [inverseMinusGradient] <;> ring

theorem minus_gradient_bijective : Function.Bijective (gradXY 1 0 (-1) 1 1) := by
  constructor
  · intro z w h
    have hh := congrArg inverseMinusGradient h
    simpa only [inverse_minus_gradient] using hh
  · intro z
    exact ⟨inverseMinusGradient z, minus_gradient_inverse z⟩

theorem minus_gradient_jacobian (x y : ℝ) :
    jacobianPair (fun v w => (gradXY 1 0 (-1) 1 1 (v, w)).1)
      (fun v w => (gradXY 1 0 (-1) 1 1 (v, w)).2) x y = -2 := by
  rw [gradXY_jacobian]
  ring

end LinearInputVariablePairs
