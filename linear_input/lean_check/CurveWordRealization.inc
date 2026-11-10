/-!
Every finite word agrees with composition of its actual integrated arc states.
The lifted angle is retained as a real number; only rotations use its residue.
This identifies states of composed pieces, not a new global smooth curve or a
stationary solution of the original fixed-boundary elastica problem.
-/

noncomputable section
open Filter

namespace LinearInputCurveWordRealization

def point (h : ℝ) (p : LinearInputCurveWordFinite.Point) : ℂ :=
  ⟨LinearInputCurveWordArc.endpointUnit h * (p.1 : ℝ),
   LinearInputCurveWordArc.endpointUnit h * (p.2 : ℝ)⟩

def decode (h : ℝ) (s : LinearInputCurveWordFinite.State) :
    LinearInputCurveWordAlgebra.State := LinearInputCurveWordArc.interpretFirstState h s

theorem decode_endpoint (h : ℝ) (s : LinearInputCurveWordFinite.State) :
    LinearInputCurveWordAlgebra.endpoint (decode h s) = point h s.1 := rfl

theorem decode_angle (h : ℝ) (s : LinearInputCurveWordFinite.State) :
    LinearInputCurveWordAlgebra.angle (decode h s) = (s.2.1 : ℝ) * (Real.pi / 2) := rfl

theorem decode_cost (h : ℝ) (s : LinearInputCurveWordFinite.State) :
    LinearInputCurveWordAlgebra.cost (decode h s) =
      LinearInputCurveWordArc.costUnit h * (s.2.2.1 : ℝ) := rfl

theorem point_add (h : ℝ) (p q : LinearInputCurveWordFinite.Point) :
    point h (p.1 + q.1, p.2 + q.2) = point h p + point h q := by
  apply Complex.ext <;> simp [point, mul_add]

theorem rotation_quarter_count (n : ℕ) :
    LinearInputCurveWordAlgebra.rotation ((n : ℝ) * (Real.pi / 2)) = Complex.I ^ n := by
  induction n with
  | zero => simp [LinearInputCurveWordAlgebra.rotation_zero]
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      LinearInputCurveWordAlgebra.rotation_add, ih,
      LinearInputCurveWordAlgebra.rotation_quarter, pow_succ]

theorem rotation_matches_lattice (h : ℝ) (p : LinearInputCurveWordFinite.Point) (n : ℕ) :
    point h (LinearInputCurveWordFinite.rotate p n) =
      LinearInputCurveWordAlgebra.rotation ((n : ℝ) * (Real.pi / 2)) * point h p := by
  rw [rotation_quarter_count, Complex.I_pow_eq_pow_mod]
  have hn : n % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hk : n % 4 <;> apply Complex.ext <;>
    norm_num [LinearInputCurveWordFinite.rotate, hk, point, Complex.mul_re, Complex.mul_im,
      Complex.I_sq, Complex.I_pow_three]

theorem decode_empty (h : ℝ) :
    decode h ((0, 0), 0, 0, 0) = LinearInputCurveWordAlgebra.emptyState := by
  simp [decode, LinearInputCurveWordArc.interpretFirstState,
    LinearInputCurveWordAlgebra.emptyState]
  rfl

theorem letter_endpoint {h : ℝ} (hh : 0 < h) (a : Bool) :
    LinearInputCurveWordAlgebra.endpoint (LinearInputCurveWordArc.letterState h a) =
      point h (if a then (3, 3) else (-1, 1)) := by
  rw [LinearInputCurveWordArc.letter_matches_integer_step hh a]
  cases a <;>
    simp [LinearInputCurveWordAlgebra.endpoint, LinearInputCurveWordArc.interpretFirstState,
      LinearInputCurveWordFinite.step, LinearInputCurveWordFinite.rotate, point]

theorem letter_angle {h : ℝ} (hh : 0 < h) (a : Bool) :
    LinearInputCurveWordAlgebra.angle (LinearInputCurveWordArc.letterState h a) =
      ((if a then 1 else 3 : ℕ) : ℝ) * (Real.pi / 2) := by
  rw [LinearInputCurveWordArc.letter_matches_integer_step hh a]
  cases a <;>
    simp [LinearInputCurveWordAlgebra.angle, LinearInputCurveWordArc.interpretFirstState,
      LinearInputCurveWordFinite.step]

theorem letter_cost {h : ℝ} (hh : 0 < h) (a : Bool) :
    LinearInputCurveWordAlgebra.cost (LinearInputCurveWordArc.letterState h a) =
      LinearInputCurveWordArc.costUnit h * ((if a then 1 else 9 : ℕ) : ℝ) := by
  rw [LinearInputCurveWordArc.letter_matches_integer_step hh a]
  cases a <;>
    simp [LinearInputCurveWordAlgebra.cost, LinearInputCurveWordArc.interpretFirstState,
      LinearInputCurveWordFinite.step]

theorem decode_step {h : ℝ} (hh : 0 < h) (s : LinearInputCurveWordFinite.State) (a : Bool) :
    decode h (LinearInputCurveWordFinite.step s a) =
      LinearInputCurveWordAlgebra.join (decode h s) (LinearInputCurveWordArc.letterState h a) := by
  apply LinearInputCurveWordAlgebra.state_ext
  · rw [LinearInputCurveWordAlgebra.join_endpoint, decode_endpoint, decode_endpoint,
      decode_angle, letter_endpoint hh]
    change point h (s.1.1 + (LinearInputCurveWordFinite.rotate
      (if a then (3, 3) else (-1, 1)) s.2.1).1,
      s.1.2 + (LinearInputCurveWordFinite.rotate
      (if a then (3, 3) else (-1, 1)) s.2.1).2) = _
    rw [point_add, rotation_matches_lattice]
  · rw [LinearInputCurveWordAlgebra.join_angle, decode_angle, decode_angle, letter_angle hh]
    simp [LinearInputCurveWordFinite.step, Nat.cast_add, add_mul]
  · rw [LinearInputCurveWordAlgebra.join_cost, decode_cost, decode_cost, letter_cost hh]
    simp [LinearInputCurveWordFinite.step, Nat.cast_add, mul_add]

def wordState (h : ℝ) (w : List Bool) : LinearInputCurveWordAlgebra.State :=
  w.foldl (fun s a => LinearInputCurveWordAlgebra.join s
    (LinearInputCurveWordArc.letterState h a)) LinearInputCurveWordAlgebra.emptyState

theorem decode_fold {h : ℝ} (hh : 0 < h) (w : List Bool)
    (s : LinearInputCurveWordFinite.State) :
    decode h (w.foldl LinearInputCurveWordFinite.step s) =
      w.foldl (fun t a => LinearInputCurveWordAlgebra.join t
        (LinearInputCurveWordArc.letterState h a)) (decode h s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp only [List.foldl_cons, ih, decode_step hh]

theorem wordState_eq_decode {h : ℝ} (hh : 0 < h) (w : List Bool) :
    wordState h w = decode h (LinearInputCurveWordFinite.state w) := by
  rw [LinearInputCurveWordFinite.state, decode_fold hh, decode_empty]
  rfl

theorem word_endpoint {h : ℝ} (hh : 0 < h) (w : List Bool) :
    LinearInputCurveWordAlgebra.endpoint (wordState h w) =
      point h (LinearInputCurveWordFinite.state w).1 := by
  rw [wordState_eq_decode hh, decode_endpoint]

theorem word_lifted_angle {h : ℝ} (hh : 0 < h) (w : List Bool) :
    LinearInputCurveWordAlgebra.angle (wordState h w) =
      ((LinearInputCurveWordFinite.state w).2.1 : ℝ) * (Real.pi / 2) := by
  rw [wordState_eq_decode hh, decode_angle]

theorem word_cost {h : ℝ} (hh : 0 < h) (w : List Bool) :
    LinearInputCurveWordAlgebra.cost (wordState h w) =
      LinearInputCurveWordArc.costUnit h * ((LinearInputCurveWordFinite.state w).2.2.1 : ℝ) := by
  rw [wordState_eq_decode hh, decode_cost]

/-- Convert a physical endpoint force to the dimensionless integer-lattice force. -/
def normalizedInput (h : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 * LinearInputCurveWordArc.endpointUnit h / LinearInputCurveWordArc.costUnit h,
   u.2 * LinearInputCurveWordArc.endpointUnit h / LinearInputCurveWordArc.costUnit h)

theorem linearEnergy_decode {h : ℝ} (hh : 0 < h) (u : ℝ × ℝ)
    (s : LinearInputCurveWordFinite.State) :
    LinearInputCurveWordAlgebra.linearEnergy u (decode h s) =
      LinearInputCurveWordArc.costUnit h *
        LinearInputCurveWordFiniteState.arcObjective
          (normalizedInput h u).1 (normalizedInput h u).2 s := by
  have hc : LinearInputCurveWordArc.costUnit h ≠ 0 :=
    ne_of_gt (LinearInputCurveWordArc.costUnit_pos hh)
  simp only [LinearInputCurveWordAlgebra.linearEnergy, decode_cost, decode_endpoint,
    point, normalizedInput, LinearInputCurveWordFiniteState.arcObjective]
  field_simp [hc]

theorem word_linearEnergy_normalized {h : ℝ} (hh : 0 < h) (u : ℝ × ℝ) (w : List Bool) :
    LinearInputCurveWordAlgebra.linearEnergy u (wordState h w) =
      LinearInputCurveWordArc.costUnit h *
        LinearInputCurveWordFiniteState.arcObjective
          (normalizedInput h u).1 (normalizedInput h u).2 (LinearInputCurveWordFinite.state w) := by
  rw [wordState_eq_decode hh, linearEnergy_decode hh]

/-- The finite four-state computation expressed in physical energy units. -/
def minimumEnergy (h : ℝ) (u : ℝ × ℝ) (n : ℕ) : ℝ :=
  LinearInputCurveWordArc.costUnit h *
    LinearInputCurveWordFiniteState.bellman LinearInputCurveWordFiniteState.arcNext
      (LinearInputCurveWordFiniteState.arcEdge (normalizedInput h u).1
        (normalizedInput h u).2) n 0

theorem minimumEnergy_is_global_minimum {h : ℝ} (hh : 0 < h) (u : ℝ × ℝ) (n : ℕ) :
    (∃ w : List Bool, w.length = n ∧
      LinearInputCurveWordAlgebra.linearEnergy u (wordState h w) = minimumEnergy h u n) ∧
    ∀ w : List Bool, w.length = n → minimumEnergy h u n ≤
      LinearInputCurveWordAlgebra.linearEnergy u (wordState h w) := by
  obtain ⟨⟨w, hlen, hcost⟩, hmin⟩ :=
    LinearInputCurveWordFiniteState.arc_bellman_is_global_minimum
      (normalizedInput h u).1 (normalizedInput h u).2 n
  constructor
  · refine ⟨w, hlen, ?_⟩
    rw [word_linearEnergy_normalized hh, hcost]
    rfl
  · intro v hv
    rw [word_linearEnergy_normalized hh]
    exact mul_le_mul_of_nonneg_left (hmin v hv)
      (LinearInputCurveWordArc.costUnit_pos hh).le

def physicalRate (h u : ℝ) : ℝ :=
  min (LinearInputCurveWordArc.costUnit h)
    (5 * LinearInputCurveWordArc.costUnit h - LinearInputCurveWordArc.endpointUnit h * |u|)

theorem normalized_rate_to_physical {h : ℝ} (hh : 0 < h) (u : ℝ) :
    LinearInputCurveWordArc.costUnit h *
      min 1 (5 - |u * LinearInputCurveWordArc.endpointUnit h /
        LinearInputCurveWordArc.costUnit h|) = physicalRate h u := by
  have hc := LinearInputCurveWordArc.costUnit_pos hh
  have hx := LinearInputCurveWordArc.endpointUnit_pos hh
  rw [mul_min_of_nonneg _ _ hc.le, mul_one, physicalRate]
  congr 1
  rw [abs_div, abs_mul, abs_of_pos hx, abs_of_pos hc]
  field_simp [ne_of_gt hc]

theorem physicalRate_formula (h u : ℝ) :
    physicalRate h u = min (Real.pi ^ 2 / (8 * h))
      (5 * Real.pi ^ 2 / (8 * h) - 2 * h * |u| / (3 * Real.pi)) := by
  unfold physicalRate LinearInputCurveWordArc.costUnit LinearInputCurveWordArc.endpointUnit
  congr 1
  ring

/-- The limit is for the actual integrated-arc word-state energy, whose finite
minimum and attaining words were proved above. -/
theorem minimumEnergy_average_tendsto {h : ℝ} (hh : 0 < h) (u : ℝ) :
    Tendsto (fun n : ℕ => minimumEnergy h (u, 0) n / (n : ℝ)) atTop
      (nhds (physicalRate h u)) := by
  have hc : Tendsto (fun _ : ℕ => LinearInputCurveWordArc.costUnit h) atTop
      (nhds (LinearInputCurveWordArc.costUnit h)) := tendsto_const_nhds
  have ht := hc.mul (LinearInputCurveWordCycleLimit.bellman_average_tendsto
    (u * LinearInputCurveWordArc.endpointUnit h / LinearInputCurveWordArc.costUnit h))
  rw [normalized_rate_to_physical hh] at ht
  simpa only [minimumEnergy, normalizedInput, zero_mul, zero_div, mul_div_assoc] using ht

theorem minimumEnergy_average_explicit {h : ℝ} (hh : 0 < h) (u : ℝ) :
    Tendsto (fun n : ℕ => minimumEnergy h (u, 0) n / (n : ℝ)) atTop
      (nhds (min (Real.pi ^ 2 / (8 * h))
        (5 * Real.pi ^ 2 / (8 * h) - 2 * h * |u| / (3 * Real.pi)))) := by
  simpa only [physicalRate_formula] using minimumEnergy_average_tendsto hh u

def criticalInput (h : ℝ) : ℝ := 3 * Real.pi ^ 3 / (4 * h ^ 2)

theorem criticalInput_pos {h : ℝ} (hh : 0 < h) : 0 < criticalInput h := by
  unfold criticalInput
  positivity

theorem criticalInput_unit_identity {h : ℝ} (hh : 0 < h) :
    LinearInputCurveWordArc.endpointUnit h * criticalInput h =
      4 * LinearInputCurveWordArc.costUnit h := by
  unfold LinearInputCurveWordArc.endpointUnit criticalInput LinearInputCurveWordArc.costUnit
  field_simp [ne_of_gt hh, Real.pi_ne_zero]
  ring

theorem physicalRate_pureA {h : ℝ} (hh : 0 < h) (u : ℝ)
    (hu : |u| ≤ criticalInput h) :
    physicalRate h u = LinearInputCurveWordArc.costUnit h := by
  apply min_eq_left
  have hm := mul_le_mul_of_nonneg_left hu (LinearInputCurveWordArc.endpointUnit_pos hh).le
  rw [criticalInput_unit_identity hh] at hm
  linarith

theorem physicalRate_alternating {h : ℝ} (hh : 0 < h) (u : ℝ)
    (hu : criticalInput h ≤ |u|) :
    physicalRate h u = 5 * LinearInputCurveWordArc.costUnit h -
      LinearInputCurveWordArc.endpointUnit h * |u| := by
  apply min_eq_right
  have hm := mul_le_mul_of_nonneg_left hu (LinearInputCurveWordArc.endpointUnit_pos hh).le
  rw [criticalInput_unit_identity hh] at hm
  linarith

theorem physicalRate_at_threshold {h : ℝ} (hh : 0 < h) (u : ℝ)
    (hu : |u| = criticalInput h) :
    physicalRate h u = LinearInputCurveWordArc.costUnit h ∧
      5 * LinearInputCurveWordArc.costUnit h -
        LinearInputCurveWordArc.endpointUnit h * |u| = LinearInputCurveWordArc.costUnit h := by
  refine ⟨physicalRate_pureA hh u hu.le, ?_⟩
  rw [hu, criticalInput_unit_identity hh]
  ring

end LinearInputCurveWordRealization
