/-!
# Rim/observability: exact four-phase decoding of a rotation/reflection pair

This supplement formalizes a four-dimensional local normal form:
one quarter turn paired with one reflection, read out by one scalar.

The original F16 pencil has four rotation-type and four reflection-type
2x2 blocks after an invertible row gauge (F16UnexpectedBridges and
F16FullMatrix).  This local calculation does not, by itself, claim
that a global conjugacy with the original 16x16 pencil has been proved.
-/ 

noncomputable section

namespace LinearInputRimObservability

/-- A pair of real two-dimensional normal-form states. -/
abbrev LocalState := (ℝ × ℝ) × (ℝ × ℝ)

/-- Rotation on the first pair, reflection on the second. -/
def step (v : LocalState) : LocalState :=
  ((-v.1.2, v.1.1), (v.2.2, v.2.1))

/-- A single scalar output, mixing the second coordinates of both pairs. -/
def observe (v : LocalState) : ℝ :=
  (v.2.2 - v.1.2) / 2

/-- Four successive scalar observations. -/
def trace4 (v : LocalState) : LocalState :=
  ((observe v, observe (step v)),
   (observe (step (step v)), observe (step (step (step v)))))

/-- The exact decoder, requiring no matrix inverse operation. -/
def decode4 (y : LocalState) : LocalState :=
  ((y.2.2 - y.1.2, y.2.1 - y.1.1),
   (y.2.2 + y.1.2, y.2.1 + y.1.1))

/-- A full rotation-reflection cycle is four steps. -/
theorem step_four (v : LocalState) :
    step (step (step (step v))) = v := by
  rcases v with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [step]

/-- All four original coordinates are exactly recovered from four outputs. -/
theorem decode4_trace4 (v : LocalState) :
    decode4 (trace4 v) = v := by
  rcases v with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  apply Prod.ext
  · apply Prod.ext
    · dsimp [decode4, trace4, observe, step]
      ring
    · dsimp [decode4, trace4, observe, step]
      ring
  · apply Prod.ext
    · dsimp [decode4, trace4, observe, step]
      ring
    · dsimp [decode4, trace4, observe, step]
      ring

/-- Four scalar samples suffice to distinguish all four-dimensional states. -/
theorem trace4_injective : Function.Injective trace4 := by
  intro v w h
  calc
    v = decode4 (trace4 v) := (decode4_trace4 v).symm
    _ = decode4 (trace4 w) := congrArg decode4 h
    _ = w := decode4_trace4 w

/-- Three successive scalar observations. -/
def trace3 (v : LocalState) : (ℝ × ℝ) × ℝ :=
  ((observe v, observe (step v)), observe (step (step v)))

/-- First three outputs do not distinguish two explicit different states. -/
theorem trace3_not_injective : ¬ Function.Injective trace3 := by
  intro h
  let v₀ : LocalState := ((0, 0), (0, 0))
  let v₁ : LocalState := ((1, 0), (1, 0))
  have hs : trace3 v₀ = trace3 v₁ := by
    norm_num [v₀, v₁, trace3, observe, step]
  have hn : v₀ ≠ v₁ := by
    norm_num [v₀, v₁]
  exact hn (h hs)

/-- Arbitrary signed 2x2 local action. -/
def signedStep (p q : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (p * z.2, q * z.1)

/-- Diagonal sign gauge on the second coordinate. -/
def signGauge (q : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1, q * z.2)

/-- Every signed block with pq=-1 and q²=1 is gauge-equivalent
to the canonical quarter turn. -/
theorem rotation_sign_gauge (p q : ℝ)
    (hpq : p * q = -1) (hq : q ^ 2 = 1) (z : ℝ × ℝ) :
    signGauge q (signedStep p q z) =
      (-(signGauge q z).2, (signGauge q z).1) := by
  rcases z with ⟨x, y⟩
  have hp : p = -q := by
    calc
      p = p * q ^ 2 := by rw [hq]; ring
      _ = (p * q) * q := by ring
      _ = -q := by rw [hpq]; ring
  apply Prod.ext
  · change p * y = -(q * y)
    rw [hp]
    ring
  · change q * (q * x) = x
    calc
      q * (q * x) = q ^ 2 * x := by ring
      _ = x := by rw [hq]; ring

/-- Every signed block with pq=1 and q²=1 is gauge-equivalent
to the coordinate swap reflection. -/
theorem reflection_sign_gauge (p q : ℝ)
    (hpq : p * q = 1) (hq : q ^ 2 = 1) (z : ℝ × ℝ) :
    signGauge q (signedStep p q z) =
      ((signGauge q z).2, (signGauge q z).1) := by
  rcases z with ⟨x, y⟩
  have hp : p = q := by
    calc
      p = p * q ^ 2 := by rw [hq]; ring
      _ = (p * q) * q := by ring
      _ = q := by rw [hpq]; ring
  apply Prod.ext
  · change p * y = q * y
    rw [hp]
  · change q * (q * x) = x
    calc
      q * (q * x) = q ^ 2 * x := by ring
      _ = x := by rw [hq]; ring

end LinearInputRimObservability
