/-!
Actual spatial partial derivatives and the chain rule for a moving linear input.
Every derivative below is derived from the polynomial energy definition.
-/
noncomputable section
namespace LinearInputGradient

open LinearInputDesign

def gx (lam r u x y : ℝ) : ℝ :=
  lam * x ^ 3 + (r + 2) * x - Real.sqrt 2 * y - u

def gy (x y : ℝ) : ℝ := y - Real.sqrt 2 * x

def gSq (lam r u x y : ℝ) : ℝ :=
  (gx lam r u x y) ^ 2 + (gy x y) ^ 2

theorem hasDerivAt_E_x (lam r u x y : ℝ) :
    HasDerivAt (fun t : ℝ => E lam r u t y) (gx lam r u x y) x := by
  have hf : HasDerivAt (f lam r u) (lam * x ^ 3 + r * x - u) x :=
    LinearInputCalculus.hasDerivAt_potential lam r u x
  convert hf.add (((hasDerivAt_const x y).sub
    ((hasDerivAt_id x).const_mul (Real.sqrt 2))).pow 2 |>.div_const 2) using 1
  dsimp [gx]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem hasDerivAt_E_y (lam r u x y : ℝ) :
    HasDerivAt (fun t : ℝ => E lam r u x t) (gy x y) y := by
  convert (hasDerivAt_const y (f lam r u x)).add
    (((hasDerivAt_id y).sub_const (Real.sqrt 2 * x)).pow 2 |>.div_const 2) using 1
  dsimp [gy]
  ring

theorem hasDerivAt_E_input (lam r u x y : ℝ) :
    HasDerivAt (fun t : ℝ => E lam r t x y) (-x) u := by
  convert ((hasDerivAt_const u (lam * x ^ 4 / 4 + r * x ^ 2 / 2)).sub
    ((hasDerivAt_id u).mul_const x)).add_const
    ((y - Real.sqrt 2 * x) ^ 2 / 2) using 1
  simp

theorem deriv_E_x (lam r u x y : ℝ) :
    deriv (fun t : ℝ => E lam r u t y) x = gx lam r u x y :=
  (hasDerivAt_E_x lam r u x y).deriv

theorem deriv_E_y (lam r u x y : ℝ) :
    deriv (fun t : ℝ => E lam r u x t) y = gy x y :=
  (hasDerivAt_E_y lam r u x y).deriv

theorem stationary_iff (lam r u x y : ℝ) :
    gx lam r u x y = 0 ∧ gy x y = 0 ↔
      y = Real.sqrt 2 * x ∧ u = lam * x ^ 3 + r * x := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [gx, gy]
  constructor
  · rintro ⟨hx, hy⟩
    have hy' : y = Real.sqrt 2 * x := by linarith
    refine ⟨hy', ?_⟩
    rw [hy'] at hx
    nlinarith [congrArg (fun s : ℝ => s * x) hs]
  · rintro ⟨hy, hu⟩
    rw [hy, hu]
    constructor
    · nlinarith [congrArg (fun s : ℝ => s * x) hs]
    · ring

theorem partials_zero_iff (lam r u x y : ℝ) :
    (deriv (fun t : ℝ => E lam r u t y) x = 0 ∧
      deriv (fun t : ℝ => E lam r u x t) y = 0) ↔
      y = Real.sqrt 2 * x ∧ u = lam * x ^ 3 + r * x := by
  rw [deriv_E_x, deriv_E_y, stationary_iff]

theorem stationary_value_le {lam r u x y : ℝ} (hlam : 0 < lam)
    (hg : gx lam r u x y = 0 ∧ gy x y = 0) :
    E lam r u x y ≤ (max (-r) 0) ^ 2 / (12 * lam) := by
  obtain ⟨hy, hu⟩ := (stationary_iff lam r u x y).1 hg
  rw [hy]
  simpa only [E, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
    using LinearInputCalculus.critical_value_le hlam hu

theorem no_stationary_on_band {lam r u x y target : ℝ} (hlam : 0 < lam)
    (ht : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (he : target ≤ E lam r u x y) :
    ¬ (gx lam r u x y = 0 ∧ gy x y = 0) := by
  intro hg
  linarith [stationary_value_le hlam hg]

theorem gSq_nonneg (lam r u x y : ℝ) : 0 ≤ gSq lam r u x y := by
  unfold gSq
  positivity

theorem gSq_eq_zero_iff (lam r u x y : ℝ) :
    gSq lam r u x y = 0 ↔ gx lam r u x y = 0 ∧ gy x y = 0 := by
  unfold gSq
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (gx lam r u x y), sq_nonneg (gy x y)]
  · rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num

theorem gSq_pos_on_band {lam r u x y target : ℝ} (hlam : 0 < lam)
    (ht : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (he : target ≤ E lam r u x y) :
    0 < gSq lam r u x y := by
  have hn := gSq_nonneg lam r u x y
  have hne : gSq lam r u x y ≠ 0 := by
    intro hz
    exact no_stationary_on_band hlam ht he ((gSq_eq_zero_iff lam r u x y).1 hz)
  exact lt_of_le_of_ne hn (Ne.symm hne)

theorem continuous_E (lam r u : ℝ) :
    Continuous (fun z : ℝ × ℝ => E lam r u z.1 z.2) := by
  exact (((continuous_const.mul (continuous_fst.pow 4)).div_const 4).add
    ((continuous_const.mul (continuous_fst.pow 2)).div_const 2) |>.sub
    (continuous_const.mul continuous_fst)).add
    ((continuous_snd.sub (continuous_const.mul continuous_fst)).pow 2 |>.div_const 2)

theorem continuous_gSq (lam r u : ℝ) :
    Continuous (fun z : ℝ × ℝ => gSq lam r u z.1 z.2) := by
  exact ((((continuous_const.mul (continuous_fst.pow 3)).add
    (continuous_const.mul continuous_fst)).sub
    (continuous_const.mul continuous_snd) |>.sub continuous_const).pow 2).add
    ((continuous_snd.sub (continuous_const.mul continuous_fst)).pow 2)

/-- The input is allowed to move: its work term is forced by the actual chain rule. -/
theorem hasDerivAt_energy_curve {x y u : ℝ → ℝ} {t x' y' u' : ℝ}
    (lam r : ℝ) (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t)
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => E lam r (u s) (x s) (y s))
      (gx lam r (u t) (x t) (y t) * x' + gy (x t) (y t) * y' - x t * u') t := by
  convert (((((hx.pow 4).const_mul lam).div_const 4).add
    (((hx.pow 2).const_mul r).div_const 2)).sub (hu.mul hx)).add
    (((hy.sub (hx.const_mul (Real.sqrt 2))).pow 2).div_const 2) using 1
  dsimp [gx, gy]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Conditional on actual coordinate velocities, the tangential part cancels.
The moving input contributes the term `-x t * u'`; no existence assertion is made. -/
theorem hasDerivAt_energy_of_velocity {x y u : ℝ → ℝ} {t u' : ℝ}
    (lam r gamma target b : ℝ)
    (hx : HasDerivAt x
      (-gamma * (E lam r (u t) (x t) (y t) - target) * gx lam r (u t) (x t) (y t)
        - b * gy (x t) (y t)) t)
    (hy : HasDerivAt y
      (-gamma * (E lam r (u t) (x t) (y t) - target) * gy (x t) (y t)
        + b * gx lam r (u t) (x t) (y t)) t)
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => E lam r (u s) (x s) (y s))
      (-gamma * (E lam r (u t) (x t) (y t) - target) *
        gSq lam r (u t) (x t) (y t) - x t * u') t := by
  convert hasDerivAt_energy_curve lam r hx hy hu using 1
  unfold gSq
  ring

/-- With fixed input, this is the genuine energy derivative along any such curve. -/
theorem hasDerivAt_energy_fixed_input {x y : ℝ → ℝ} {t : ℝ}
    (lam r u gamma target b : ℝ)
    (hx : HasDerivAt x
      (-gamma * (E lam r u (x t) (y t) - target) * gx lam r u (x t) (y t)
        - b * gy (x t) (y t)) t)
    (hy : HasDerivAt y
      (-gamma * (E lam r u (x t) (y t) - target) * gy (x t) (y t)
        + b * gx lam r u (x t) (y t)) t) :
    HasDerivAt (fun s => E lam r u (x s) (y s))
      (-gamma * (E lam r u (x t) (y t) - target) *
        gSq lam r u (x t) (y t)) t := by
  simpa only [mul_zero, sub_zero] using
    hasDerivAt_energy_of_velocity (u := fun _ => u) lam r gamma target b hx hy
      (hasDerivAt_const t u)

/-- The squared energy gap has the expected derivative, derived by the chain rule. -/
theorem hasDerivAt_squared_gap_fixed_input {x y : ℝ → ℝ} {t : ℝ}
    (lam r u gamma target b : ℝ)
    (hx : HasDerivAt x
      (-gamma * (E lam r u (x t) (y t) - target) * gx lam r u (x t) (y t)
        - b * gy (x t) (y t)) t)
    (hy : HasDerivAt y
      (-gamma * (E lam r u (x t) (y t) - target) * gy (x t) (y t)
        + b * gx lam r u (x t) (y t)) t) :
    HasDerivAt (fun s => (E lam r u (x s) (y s) - target) ^ 2)
      (-2 * gamma * (E lam r u (x t) (y t) - target) ^ 2 *
        gSq lam r u (x t) (y t)) t := by
  convert ((hasDerivAt_energy_fixed_input lam r u gamma target b hx hy).sub_const
    target).pow 2 using 1
  ring

end LinearInputGradient
