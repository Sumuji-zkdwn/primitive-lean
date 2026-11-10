/-!
Algebra of normalized curve pieces with a real lifted turning angle.
The state retains endpoint, total angle and additive cost; it does not assert
that every triple is realized by a smooth constrained elastica.
-/

noncomputable section

namespace LinearInputCurveWordAlgebra

abbrev State := ℂ × ℝ × ℝ

def endpoint (s : State) : ℂ := s.1

def angle (s : State) : ℝ := s.2.1

def cost (s : State) : ℝ := s.2.2

def rotation (a : ℝ) : ℂ := Complex.exp ((a : ℂ) * Complex.I)

def emptyState : State := (0, 0, 0)

def join (s t : State) : State :=
  (endpoint s + rotation (angle s) * endpoint t, angle s + angle t, cost s + cost t)

theorem state_ext {s t : State} (hz : endpoint s = endpoint t)
    (ha : angle s = angle t) (hc : cost s = cost t) : s = t :=
  Prod.ext hz (Prod.ext ha hc)

theorem rotation_zero : rotation 0 = 1 := by simp [rotation]

theorem rotation_add (a b : ℝ) : rotation (a + b) = rotation a * rotation b := by
  simp [rotation, add_mul, Complex.exp_add]

theorem rotation_norm (a : ℝ) : ‖rotation a‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I a

theorem join_endpoint (s t : State) :
    endpoint (join s t) = endpoint s + rotation (angle s) * endpoint t := rfl

theorem join_angle (s t : State) : angle (join s t) = angle s + angle t := rfl

theorem join_cost (s t : State) : cost (join s t) = cost s + cost t := rfl

theorem empty_join (s : State) : join emptyState s = s := by
  apply state_ext <;> simp [join, emptyState, endpoint, angle, cost, rotation_zero]

theorem join_empty (s : State) : join s emptyState = s := by
  apply state_ext <;> simp [join, emptyState, endpoint, angle, cost]

theorem join_assoc (s t u : State) : join (join s t) u = join s (join t u) := by
  apply state_ext
  · simp only [join_endpoint, join_angle, rotation_add]
    ring
  · simp only [join_angle]
    ring
  · simp only [join_cost]
    ring

theorem exchange_angle (s t : State) : angle (join s t) = angle (join t s) := by
  simp only [join_angle, add_comm]

theorem exchange_cost (s t : State) : cost (join s t) = cost (join t s) := by
  simp only [join_cost, add_comm]

theorem exchange_endpoint (s t : State) :
    endpoint (join s t) - endpoint (join t s) =
      (1 - rotation (angle t)) * endpoint s -
        (1 - rotation (angle s)) * endpoint t := by
  simp only [join_endpoint]
  ring

/-- Equal lifted angles ensure that a common suffix cancels from the difference. -/
theorem context_endpoint_difference (p s t q : State) (ha : angle s = angle t) :
    endpoint (join (join p s) q) - endpoint (join (join p t) q) =
      rotation (angle p) * (endpoint s - endpoint t) := by
  simp only [join_endpoint, join_angle, ha]
  ring

theorem context_difference_norm (p s t q : State) (ha : angle s = angle t) :
    ‖endpoint (join (join p s) q) - endpoint (join (join p t) q)‖ =
      ‖endpoint s - endpoint t‖ := by
  rw [context_endpoint_difference p s t q ha, norm_mul, rotation_norm, one_mul]

theorem exchange_context_difference (p s t q : State) :
    endpoint (join (join p (join s t)) q) -
        endpoint (join (join p (join t s)) q) =
      rotation (angle p) * (endpoint (join s t) - endpoint (join t s)) :=
  context_endpoint_difference p (join s t) (join t s) q (exchange_angle s t)

theorem exchange_context_norm (p s t q : State) :
    ‖endpoint (join (join p (join s t)) q) -
        endpoint (join (join p (join t s)) q)‖ =
      ‖endpoint (join s t) - endpoint (join t s)‖ :=
  context_difference_norm p (join s t) (join t s) q (exchange_angle s t)

def observe (s : State) : ℝ × ℝ × ℝ := (cost s, angle s, (endpoint s).re)

def quarterPrefix : State := (0, Real.pi / 2, 0)

theorem rotation_quarter : rotation (Real.pi / 2) = Complex.I := by
  simpa only [rotation, Complex.ofReal_div, Complex.ofReal_ofNat] using
    Complex.exp_pi_div_two_mul_I

theorem quarter_prefix_endpoint_real (p s : State) (hp : angle p = Real.pi / 2) :
    (endpoint (join p s)).re = (endpoint p).re - (endpoint s).im := by
  simp only [join_endpoint, hp, rotation_quarter, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im]
  ring

theorem quarter_endpoint_real (s : State) :
    (endpoint (join quarterPrefix s)).re = -(endpoint s).im := by
  simp [join, quarterPrefix, endpoint, angle, rotation_quarter, Complex.mul_re]

theorem two_observations_complete (s t : State) :
    observe s = observe t ∧ observe (join quarterPrefix s) = observe (join quarterPrefix t)
      ↔ s = t := by
  constructor
  · rintro ⟨h, hq⟩
    apply state_ext
    · apply Complex.ext
      · exact congrArg (fun v : ℝ × ℝ × ℝ => v.2.2) h
      · have hi := congrArg (fun v : ℝ × ℝ × ℝ => v.2.2) hq
        change (endpoint (join quarterPrefix s)).re =
          (endpoint (join quarterPrefix t)).re at hi
        simpa only [quarter_endpoint_real, neg_inj] using hi
    · exact congrArg (fun v : ℝ × ℝ × ℝ => v.2.1) h
    · exact congrArg (fun v : ℝ × ℝ × ℝ => v.1) h
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- Any quarter-turn prefix works, irrespective of its endpoint or cost. -/
theorem quarter_prefix_observations_complete (p s t : State)
    (hp : angle p = Real.pi / 2) :
    observe s = observe t ∧ observe (join p s) = observe (join p t) ↔ s = t := by
  constructor
  · rintro ⟨h, hq⟩
    apply state_ext
    · apply Complex.ext
      · exact congrArg (fun v : ℝ × ℝ × ℝ => v.2.2) h
      · have hi := congrArg (fun v : ℝ × ℝ × ℝ => v.2.2) hq
        change (endpoint (join p s)).re = (endpoint (join p t)).re at hi
        rw [quarter_prefix_endpoint_real p s hp, quarter_prefix_endpoint_real p t hp] at hi
        linarith
    · exact congrArg (fun v : ℝ × ℝ × ℝ => v.2.1) h
    · exact congrArg (fun v : ℝ × ℝ × ℝ => v.1) h
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem equal_state_all_contexts {s t : State} (h : s = t) (p q : State) :
    join (join p s) q = join (join p t) q := by rw [h]

theorem contextual_observation_complete (s t : State) :
    (∀ p q : State, observe (join (join p s) q) = observe (join (join p t) q))
      ↔ s = t := by
  constructor
  · intro h
    apply (two_observations_complete s t).mp
    constructor
    · simpa only [empty_join, join_empty] using h emptyState emptyState
    · simpa only [join_empty] using h quarterPrefix emptyState
  · rintro rfl
    intro p q
    rfl

/-- Positive geometric scale has endpoint degree 1 and quadratic bending cost degree -1. -/
def scale (σ : ℝ) (s : State) : State :=
  ((σ : ℂ) * endpoint s, angle s, cost s / σ)

theorem scale_join (σ : ℝ) (s t : State) :
    scale σ (join s t) = join (scale σ s) (scale σ t) := by
  apply state_ext
  · simp [scale, join, endpoint, angle]
    ring
  · rfl
  · simp [scale, join, cost, add_div]

def linearEnergy (u : ℝ × ℝ) (s : State) : ℝ :=
  cost s - u.1 * (endpoint s).re - u.2 * (endpoint s).im

theorem linearEnergy_scale (σ : ℝ) (hσ : σ ≠ 0) (u : ℝ × ℝ) (s : State) :
    linearEnergy u (scale σ s) =
      linearEnergy (σ ^ 2 * u.1, σ ^ 2 * u.2) s / σ := by
  simp only [linearEnergy, scale, cost, endpoint, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp
  ring

def cross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

theorem cross_add_left (z w v : ℂ) : cross (z + w) v = cross z v + cross w v := by
  simp only [cross, Complex.add_re, Complex.add_im]
  ring

theorem cross_add_right (z w v : ℂ) : cross z (w + v) = cross z w + cross z v := by
  simp only [cross, Complex.add_re, Complex.add_im]
  ring

theorem cross_rotation (a : ℝ) (z w : ℂ) :
    cross (rotation a * z) (rotation a * w) = cross z w := by
  have hn : (rotation a).re * (rotation a).re + (rotation a).im * (rotation a).im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, rotation_norm]
    norm_num
  calc
    cross (rotation a * z) (rotation a * w) =
        ((rotation a).re * (rotation a).re + (rotation a).im * (rotation a).im) *
          cross z w := by
      simp only [cross, Complex.mul_re, Complex.mul_im]
      ring
    _ = cross z w := by rw [hn, one_mul]

/-- The signed-area correction for translating and rotating the second piece. -/
def areaCocycle (s t : State) : ℝ :=
  cross (endpoint s) (rotation (angle s) * endpoint t) / 2

theorem area_cocycle_identity (s t u : State) :
    areaCocycle s t + areaCocycle (join s t) u =
      areaCocycle t u + areaCocycle s (join t u) := by
  simp only [areaCocycle, join_endpoint, join_angle, rotation_add, mul_assoc,
    mul_add, cross_add_left, cross_add_right, cross_rotation]
  ring

abbrev AreaState := State × ℝ

def joinArea (s t : AreaState) : AreaState :=
  (join s.1 t.1, s.2 + t.2 + areaCocycle s.1 t.1)

theorem joinArea_assoc (s t u : AreaState) :
    joinArea (joinArea s t) u = joinArea s (joinArea t u) := by
  apply Prod.ext
  · exact join_assoc s.1 t.1 u.1
  · change s.2 + t.2 + areaCocycle s.1 t.1 + u.2 + areaCocycle (join s.1 t.1) u.1 =
      s.2 + (t.2 + u.2 + areaCocycle t.1 u.1) + areaCocycle s.1 (join t.1 u.1)
    linarith [area_cocycle_identity s.1 t.1 u.1]

theorem equal_area_state_all_contexts {s t : AreaState} (h : s = t) (p q : AreaState) :
    joinArea (joinArea p s) q = joinArea (joinArea p t) q := by rw [h]

end LinearInputCurveWordAlgebra
