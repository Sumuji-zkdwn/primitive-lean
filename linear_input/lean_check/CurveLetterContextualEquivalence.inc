/-!
# Discrete curve-letter instance of contextual observational equivalence

Use the research note's normalized signature S=(z, α, F), where z is measured
in ξ=2h/(3π), F in c₀=π²/(8h), and α in quarter-turn units. The two
letters are the note's exact integer states A=(3+3i, 1, 1),
B=(-1+i, 3, 9). Repeated left quarter-turns implement e^(iα).
This arithmetic model covers their piecewise-smooth concatenations; it does
not establish smooth-junction, minimizer, or general physical-realizability
claims.
-/

namespace LinearInputCurveLetters

open LinearInputOperatorWords
open LinearInputJoinContexts

/-- Integer lattice coordinates for the normalized complex displacement z. -/
structure Point where
  re : Int
  im : Int
  deriving DecidableEq, Repr

def pointAdd (p q : Point) : Point := ⟨p.re + q.re, p.im + q.im⟩

/-- Multiplication of z by i, corresponding to a positive quarter turn. -/
def turnLeft (p : Point) : Point := ⟨-p.im, p.re⟩

/-- The exact action z ↦ e^(iα)z for α a nonnegative multiple of π/2. -/
def rotateQuarter : Nat → Point → Point
  | 0, p => p
  | n + 1, p => turnLeft (rotateQuarter n p)

theorem turnLeft_add (p q : Point) :
    turnLeft (pointAdd p q) = pointAdd (turnLeft p) (turnLeft q) := by
  cases p
  cases q
  simp [turnLeft, pointAdd, Int.add_comm]

theorem pointAdd_assoc (p q r : Point) :
    pointAdd (pointAdd p q) r = pointAdd p (pointAdd q r) := by
  cases p
  cases q
  cases r
  simp [pointAdd, Int.add_assoc]

theorem rotateQuarter_addPoint (n : Nat) (p q : Point) :
    rotateQuarter n (pointAdd p q) =
      pointAdd (rotateQuarter n p) (rotateQuarter n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rotateQuarter]
      rw [ih, turnLeft_add]

theorem rotateQuarter_comp (n m : Nat) (p : Point) :
    rotateQuarter (n + m) p = rotateQuarter n (rotateQuarter m p) := by
  induction n with
  | zero => simp [rotateQuarter]
  | succ n ih =>
      rw [Nat.succ_add]
      simp only [rotateQuarter]
      rw [ih]

/-- Curve-piece signature S=(z, α, F), with α in quarter-turn units and
normalized additive cost F/c₀. -/
structure CurvePiece where
  z : Point
  alpha : Nat
  cost : Nat
  deriving DecidableEq, Repr

/-- SE(2)-type curve concatenation with additive normalized bending cost. -/
def curveJoin (s t : CurvePiece) : CurvePiece :=
  ⟨pointAdd s.z (rotateQuarter s.alpha t.z), s.alpha + t.alpha, s.cost + t.cost⟩

infixl:70 " ⋆ " => curveJoin

theorem curveJoin_assoc (a b c : CurvePiece) :
    (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  cases a
  cases b
  cases c
  simp [curveJoin, rotateQuarter_addPoint, rotateQuarter_comp,
    pointAdd_assoc, Nat.add_assoc]

/-- Observe only Re(z), the lifted total angle α, and additive cost F. -/
structure Readout where
  endpointReal : Int
  totalQuarterTurns : Nat
  additiveCost : Nat
  deriving DecidableEq, Repr

def observe (s : CurvePiece) : Readout :=
  ⟨s.z.re, s.alpha, s.cost⟩

/-- The two normalized constant-curvature curve letters in the research note. -/
def A : CurvePiece := ⟨⟨3, 3⟩, 1, 1⟩
def B : CurvePiece := ⟨⟨-1, 1⟩, 3, 9⟩

/-- The sole old rewrite symbol acts as identity. Thus WordEq is exactly
equality under the original readout. -/
def rewrite : Unit → CurvePiece → CurvePiece := fun _ s => s

theorem run_rewrite_identity (word : List Unit) (s : CurvePiece) :
    LinearInputOperatorWords.run rewrite word s = s := by
  induction word with
  | nil => rfl
  | cons _ rest ih => simpa [LinearInputOperatorWords.run, rewrite] using ih

theorem wordEq_iff_observe_eq (s t : CurvePiece) :
    LinearInputOperatorWords.WordEq observe rewrite s t ↔ observe s = observe t := by
  constructor
  · exact LinearInputOperatorWords.word_now
  · intro h word
    rw [run_rewrite_identity, run_rewrite_identity, h]

theorem AB_state : A ⋆ B = ⟨⟨2, 2⟩, 4, 10⟩ := by decide

theorem BA_state : B ⋆ A = ⟨⟨2, -2⟩, 4, 10⟩ := by decide

theorem AB_BA_noncommute : A ⋆ B ≠ B ⋆ A := by decide

theorem AB_values :
    observe (A ⋆ B) = ⟨2, 4, 10⟩ := by decide

theorem BA_values :
    observe (B ⋆ A) = ⟨2, 4, 10⟩ := by decide

/-- AB and BA collide in the old observation and its predictive quotient. -/
theorem AB_BA_wordEq :
    LinearInputOperatorWords.WordEq observe rewrite (A ⋆ B) (B ⋆ A) :=
  (wordEq_iff_observe_eq (A ⋆ B) (B ⋆ A)).2 (by rw [AB_values, BA_values])

theorem old_quotient_identifies_AB_BA :
    LinearInputOperatorWords.encode observe rewrite (A ⋆ B) =
      LinearInputOperatorWords.encode observe rewrite (B ⋆ A) :=
  (LinearInputOperatorWords.encode_eq_iff observe rewrite _ _).2 AB_BA_wordEq

theorem AAB_state : A ⋆ (A ⋆ B) = ⟨⟨1, 5⟩, 5, 11⟩ := by decide

theorem ABA_state : A ⋆ (B ⋆ A) = ⟨⟨5, 5⟩, 5, 11⟩ := by decide

theorem AAB_real_endpoint :
    (A ⋆ (A ⋆ B)).z.re = 1 := by decide

theorem ABA_real_endpoint :
    (A ⋆ (B ⋆ A)).z.re = 5 := by decide

theorem left_attachment_separates :
    observe (A ⋆ (A ⋆ B)) ≠ observe (A ⋆ (B ⋆ A)) := by decide

/-- PR #87's stability condition fails: AB ~ BA, but left attachment by A
separates their readouts. -/
theorem old_curve_kernel_not_stable :
    ¬ LinearInputJoinContexts.StableJoin observe rewrite curveJoin := by
  intro hs
  have hleft := (hs (A ⋆ B) (B ⋆ A) A AB_BA_wordEq).2
  exact left_attachment_separates (LinearInputOperatorWords.word_now hleft)

/-- By stable_iff_old_attach_exists, no exact binary attachment descends to
the old predictive quotient while still agreeing with ⋆ on representatives. -/
theorem old_quotient_has_no_exact_attachment :
    ¬ ∃ attach :
        LinearInputOperatorWords.State observe rewrite →
        LinearInputOperatorWords.State observe rewrite →
        LinearInputOperatorWords.State observe rewrite,
      ∀ x y : CurvePiece,
        attach
          (LinearInputOperatorWords.encode observe rewrite x)
          (LinearInputOperatorWords.encode observe rewrite y) =
        LinearInputOperatorWords.encode observe rewrite (curveJoin x y) := by
  intro hexact
  exact old_curve_kernel_not_stable
    ((LinearInputJoinContexts.stable_iff_old_attach_exists
      observe rewrite curveJoin).2 hexact)

/-- The full contextual quotient retains the observed readout. -/
theorem contextual_readout_exact (s : CurvePiece) :
    LinearInputJoinContexts.readout observe rewrite curveJoin
      (LinearInputJoinContexts.encode observe rewrite curveJoin s) = observe s :=
  LinearInputJoinContexts.readout_encode observe rewrite curveJoin s

/-- On the full contextual quotient, the original attachment is well-defined. -/
theorem contextual_attachment_exact (s t : CurvePiece) :
    LinearInputJoinContexts.attach observe rewrite curveJoin
      (LinearInputJoinContexts.encode observe rewrite curveJoin s)
      (LinearInputJoinContexts.encode observe rewrite curveJoin t) =
        LinearInputJoinContexts.encode observe rewrite curveJoin (curveJoin s t) :=
  LinearInputJoinContexts.attach_encode observe rewrite curveJoin s t

/-- The canonical contextual quotient refines the old AB/BA collision. -/
theorem contextual_quotient_separates_AB_BA :
    LinearInputJoinContexts.encode observe rewrite curveJoin (A ⋆ B) ≠
      LinearInputJoinContexts.encode observe rewrite curveJoin (B ⋆ A) := by
  intro h
  have hctx :=
    (LinearInputJoinContexts.encode_iff observe rewrite curveJoin _ _).1 h
  have hleft := hctx (LinearInputJoinContexts.Context.left A
    LinearInputJoinContexts.Context.hole)
  exact left_attachment_separates hleft

end LinearInputCurveLetters

