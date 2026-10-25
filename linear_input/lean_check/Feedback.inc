/-!
An energy-rate constraint determines the normal velocity at a regular point.
The tangential coefficient remains free. These are algebraic consequences of
an explicitly chosen rate law, not a derivation of that law from a static energy.
-/
noncomputable section
namespace LinearInputFeedback

open LinearInputDesign LinearInputGradient

/-- Every feedback velocity satisfies the chosen energy-rate identity. -/
theorem feedback_rate (px py gamma gap b : ℝ) :
    px * (-gamma * gap * px - b * py) +
      py * (-gamma * gap * py + b * px) =
        -gamma * gap * (px ^ 2 + py ^ 2) := by
  ring

/-- At a regular point the coefficient is recovered by the oriented area. -/
theorem feedback_coefficient {px py : ℝ} (hpos : 0 < px ^ 2 + py ^ 2)
    (gamma gap b : ℝ) :
    (px * (-gamma * gap * py + b * px) -
      py * (-gamma * gap * px - b * py)) / (px ^ 2 + py ^ 2) = b := by
  apply (div_eq_iff (ne_of_gt hpos)).2
  ring

/-- The scalar rate constraint gives the explicit tangential decomposition. -/
theorem decomposition_of_rate {px py vx vy gamma gap : ℝ}
    (hpos : 0 < px ^ 2 + py ^ 2)
    (hrate : px * vx + py * vy = -gamma * gap * (px ^ 2 + py ^ 2)) :
    vx = -gamma * gap * px -
        ((px * vy - py * vx) / (px ^ 2 + py ^ 2)) * py ∧
      vy = -gamma * gap * py +
        ((px * vy - py * vx) / (px ^ 2 + py ^ 2)) * px := by
  have hn : px ^ 2 + py ^ 2 ≠ 0 := ne_of_gt hpos
  constructor
  · field_simp
    nlinarith [congrArg (fun q : ℝ => q * px) hrate]
  · field_simp
    nlinarith [congrArg (fun q : ℝ => q * py) hrate]

/-- The coefficient is unique for each velocity, although the rate law allows
every coefficient and thus does not select a velocity. -/
theorem rate_iff_exists_unique_feedback {px py vx vy gamma gap : ℝ}
    (hpos : 0 < px ^ 2 + py ^ 2) :
    (px * vx + py * vy = -gamma * gap * (px ^ 2 + py ^ 2)) ↔
      ∃! b : ℝ, vx = -gamma * gap * px - b * py ∧
        vy = -gamma * gap * py + b * px := by
  constructor
  · intro hrate
    refine ⟨(px * vy - py * vx) / (px ^ 2 + py ^ 2),
      decomposition_of_rate hpos hrate, ?_⟩
    intro b hb
    rw [hb.1, hb.2]
    exact (feedback_coefficient hpos gamma gap b).symm
  · rintro ⟨b, hb, _⟩
    rw [hb.1, hb.2]
    exact feedback_rate px py gamma gap b

/-- Without a regularity hypothesis the rate constraint imposes no velocity
restriction at a zero gradient. -/
theorem zero_gradient_rate (vx vy gamma gap : ℝ) :
    (0 : ℝ) * vx + 0 * vy = -gamma * gap * (0 ^ 2 + 0 ^ 2) := by
  ring

/-- At a zero gradient the feedback expression only represents zero velocity. -/
theorem zero_gradient_feedback_iff (vx vy gamma gap : ℝ) :
    (∃ b : ℝ, vx = -gamma * gap * 0 - b * 0 ∧
      vy = -gamma * gap * 0 + b * 0) ↔ vx = 0 ∧ vy = 0 := by
  simp

/-- The unit horizontal velocity is an exact obstruction to extending the
decomposition equivalence across zero gradients. -/
theorem zero_gradient_counterexample (gamma gap : ℝ) :
    (0 : ℝ) * 1 + 0 * 0 = -gamma * gap * (0 ^ 2 + 0 ^ 2) ∧
      ¬ ∃ b : ℝ, (1 : ℝ) = -gamma * gap * 0 - b * 0 ∧
        (0 : ℝ) = -gamma * gap * 0 + b * 0 := by
  norm_num

/-- Instantiation uses the actual polynomial partial derivatives proved in
LinearInputGradient, without assuming a derivative formula. -/
theorem energy_rate_iff_exists_unique_feedback {lam r u x y vx vy gamma target : ℝ}
    (hpos : 0 < gSq lam r u x y) :
    (gx lam r u x y * vx + gy x y * vy =
      -gamma * (E lam r u x y - target) * gSq lam r u x y) ↔
      ∃! b : ℝ,
        vx = -gamma * (E lam r u x y - target) * gx lam r u x y - b * gy x y ∧
        vy = -gamma * (E lam r u x y - target) * gy x y + b * gx lam r u x y := by
  exact rate_iff_exists_unique_feedback hpos

/-- The same equivalence expressed as an actual derivative along a curve,
using the already proved polynomial chain rule and uniqueness of derivatives. -/
theorem hasDerivAt_energy_iff_exists_unique_feedback
    {x y : ℝ → ℝ} {t vx vy lam r u gamma target : ℝ}
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t)
    (hpos : 0 < gSq lam r u (x t) (y t)) :
    HasDerivAt (fun s => E lam r u (x s) (y s))
      (-gamma * (E lam r u (x t) (y t) - target) *
        gSq lam r u (x t) (y t)) t ↔
      ∃! b : ℝ,
        vx = -gamma * (E lam r u (x t) (y t) - target) *
          gx lam r u (x t) (y t) - b * gy (x t) (y t) ∧
        vy = -gamma * (E lam r u (x t) (y t) - target) *
          gy (x t) (y t) + b * gx lam r u (x t) (y t) := by
  have hd : HasDerivAt (fun s => E lam r u (x s) (y s))
      (gx lam r u (x t) (y t) * vx + gy (x t) (y t) * vy) t := by
    simpa only [mul_zero, sub_zero] using
      hasDerivAt_energy_curve lam r hx hy (hasDerivAt_const t u)
  rw [← energy_rate_iff_exists_unique_feedback hpos]
  constructor
  · intro h
    exact hd.unique h
  · intro h
    rwa [h] at hd

/-- Above the critical-value bound, regularity follows from the energy band. -/
theorem energy_rate_iff_exists_unique_feedback_on_band
    {lam r u x y vx vy gamma target : ℝ} (hlam : 0 < lam)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (he : target ≤ E lam r u x y) :
    (gx lam r u x y * vx + gy x y * vy =
      -gamma * (E lam r u x y - target) * gSq lam r u x y) ↔
      ∃! b : ℝ,
        vx = -gamma * (E lam r u x y - target) * gx lam r u x y - b * gy x y ∧
        vy = -gamma * (E lam r u x y - target) * gy x y + b * gx lam r u x y := by
  exact energy_rate_iff_exists_unique_feedback (gSq_pos_on_band hlam htarget he)

end LinearInputFeedback
