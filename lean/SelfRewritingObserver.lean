import Mathlib

/-!
# An isolated Lean model of a self-rewriting finite observer

The state consists of two memory bits, a read head, a public report, and a
read-rule bit. Scan either leaves the rule fixed, replaces it by the bit
just read, or flips it blindly. All claims concern finite-word observable
behaviour, not phenomenal consciousness.

This is intentionally separate from the repository's .inc integration:
WordEq below has the same action-word semantics as
LinearInputOperatorWords.WordEq, but no cross-module import is claimed.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace SelfRewritingObserver

set_option backward.isDefEq.respectTransparency false in
inductive Mode where
  | blind | frozen | feedback
  deriving DecidableEq, Repr, Fintype

set_option backward.isDefEq.respectTransparency false in
inductive Action where
  | idle | clear | set | scan
  deriving DecidableEq, Repr, Fintype

structure State where
  a : Bool
  b : Bool
  h : Bool
  r : Bool
  g : Bool
  deriving DecidableEq, Repr, Fintype

/-- First and second cells relative to the current read rule. -/
def first (s : State) : Bool :=
  if s.h == s.g then s.a else s.b

def second (s : State) : Bool :=
  if s.h == s.g then s.b else s.a

/-- The interpreter is fixed; only the rule bit stored in the state changes. -/
def step (m : Mode) : Action → State → State
  | .idle, s => s
  | .clear, s => {s with r := false}
  | .set, s => {s with r := true}
  | .scan, s =>
      {s with
        h := !s.h
        r := first s
        g := match m with
             | .blind => !s.g
             | .frozen => s.g
             | .feedback => first s}

def run (m : Mode) : List Action → State → State
  | [], s => s
  | a :: w, s => run m w (step m a s)

def readout (s : State) : Bool := s.r

/-- Observations match after every finite program of allowed actions. -/
def WordEq (m : Mode) (s t : State) : Prop :=
  ∀ w : List Action, readout (run m w s) = readout (run m w t)

/-- Empty, one, two and three scans completely characterize the state. -/
def signature (m : Mode) (s : State) : Bool × Bool × Bool × Bool :=
  (readout s,
   readout (step m .scan s),
   readout (run m [.scan, .scan] s),
   readout (run m [.scan, .scan, .scan] s))

/-- A finite, exhaustively kernel-checked closure condition. -/
private theorem signature_step (m : Mode) (a : Action) :
    ∀ s t : State, signature m s = signature m t →
      signature m (step m a s) = signature m (step m a t) := by
  cases m <;> cases a <;> decide

private theorem signature_readout (m : Mode) (s t : State)
    (h : signature m s = signature m t) : readout s = readout t := by
  exact congrArg Prod.fst h

/-- Signature agreement is preserved by any finite action program. -/
private theorem signature_sound (m : Mode) (w : List Action) :
    ∀ s t : State, signature m s = signature m t →
      readout (run m w s) = readout (run m w t) := by
  induction w with
  | nil =>
      intro s t h
      exact signature_readout m s t h
  | cons a rest ih =>
      intro s t h
      exact ih (step m a s) (step m a t) (signature_step m a s t h)

/-- Necessary and sufficient invariant for all finite operation words. -/
theorem wordEq_iff_signature (m : Mode) (s t : State) :
    WordEq m s t ↔ signature m s = signature m t := by
  constructor
  · intro h
    apply Prod.ext
    · exact h []
    apply Prod.ext
    · exact h [.scan]
    apply Prod.ext
    · exact h [.scan, .scan]
    · exact h [.scan, .scan, .scan]
  · intro h w
    exact signature_sound m w s t h

/-- The whole state space really has 32 states. -/
theorem states_card : Fintype.card State = 32 := by decide

/-- Minimal predictive quotient cardinalities for the three controllers. -/
theorem blind_classes : (Finset.univ.image (signature .blind)).card = 4 := by decide
theorem frozen_classes : (Finset.univ.image (signature .frozen)).card = 8 := by decide
theorem feedback_classes : (Finset.univ.image (signature .feedback)).card = 12 := by decide

/-- Feedback identifies no pair that the fixed-rule observer distinguishes. -/
theorem feedback_implies_frozen (s t : State) :
    WordEq .feedback s t → WordEq .frozen s t := by
  intro h
  apply (wordEq_iff_signature .frozen s t).2
  have hfinite : ∀ s t : State, signature .feedback s = signature .feedback t →
      signature .frozen s = signature .frozen t := by decide
  exact hfinite s t ((wordEq_iff_signature .feedback s t).1 h)

/-- The fixed-rule observer identifies no pair that blind flipping separates. -/
theorem frozen_implies_blind (s t : State) :
    WordEq .frozen s t → WordEq .blind s t := by
  intro h
  apply (wordEq_iff_signature .blind s t).2
  have hfinite : ∀ s t : State, signature .frozen s = signature .frozen t →
      signature .blind s = signature .blind t := by decide
  exact hfinite s t ((wordEq_iff_signature .frozen s t).1 h)

private def p : State := ⟨false, true, false, false, false⟩
private def q : State := ⟨false, true, true, false, true⟩
private def z : State := ⟨false, false, false, false, false⟩

/-- Strictness: one pair is frozen-equivalent but feedback-distinguishable. -/
theorem strict_feedback : WordEq .frozen p q ∧ ¬ WordEq .feedback p q := by
  constructor
  · exact (wordEq_iff_signature .frozen p q).2 (by decide)
  · intro h
    have bad : signature .feedback p ≠ signature .feedback q := by decide
    exact bad ((wordEq_iff_signature .feedback p q).1 h)

/-- A single concrete, short distinguishing word for the same pair. -/
theorem feedback_two_scans :
    readout (run .feedback [.scan, .scan] p) ≠
      readout (run .feedback [.scan, .scan] q) := by decide

/-- In another pair, feedback moves a distinction to the third scan. -/
theorem delayed_witness :
    readout (run .frozen [.scan, .scan] z) ≠
      readout (run .frozen [.scan, .scan] q) ∧
    readout (run .feedback [.scan, .scan] z) =
      readout (run .feedback [.scan, .scan] q) ∧
    readout (run .feedback [.scan, .scan, .scan] z) ≠
      readout (run .feedback [.scan, .scan, .scan] q) := by decide

/-- Simultaneously renaming memory cells and the read head is invisible. -/
def symmetry (s : State) : State :=
  ⟨s.b, s.a, !s.h, s.r, s.g⟩

theorem symmetry_involutive : ∀ s : State, symmetry (symmetry s) = s := by decide

theorem symmetry_invisible : ∀ (m : Mode) (s : State),
    WordEq m (symmetry s) s := by
  intro m s
  apply (wordEq_iff_signature m (symmetry s) s).2
  have hfinite : ∀ (m : Mode) (s : State),
      signature m (symmetry s) = signature m s := by decide
  exact hfinite m s

end SelfRewritingObserver
