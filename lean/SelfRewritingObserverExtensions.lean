import SelfRewritingObserver

/-!
# Extra access operations for the finite self-rewriting observer

Two new alphabets allow reading the stored scan-rule bit (peekRule) and
then also the current read-head bit (peekHead). These are new operations,
not merely renamings of the old scan operation. They leave the memory and
read-rule unchanged and write their result to the public report bit.

All claims are mathematical properties of this finite deterministic model.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace SelfRewritingObserver

inductive RuleAction where
  | base (a : Action)
  | peekRule
  deriving DecidableEq, Repr, Fintype

inductive HeadAction where
  | base (a : Action)
  | peekRule
  | peekHead
  deriving DecidableEq, Repr, Fintype

/-- Feedback scan, plus an explicit operation reporting the scan-rule bit. -/
def ruleStep : RuleAction → State → State
  | .base a, s => step .feedback a s
  | .peekRule, s => {s with r := s.g}

/-- The same machine, with an additional operation reporting the read head. -/
def headStep : HeadAction → State → State
  | .base a, s => step .feedback a s
  | .peekRule, s => {s with r := s.g}
  | .peekHead, s => {s with r := s.h}

def ruleRun : List RuleAction → State → State
  | [], s => s
  | a :: w, s => ruleRun w (ruleStep a s)

def headRun : List HeadAction → State → State
  | [], s => s
  | a :: w, s => headRun w (headStep a s)

def RuleWordEq (s t : State) : Prop :=
  ∀ w : List RuleAction, readout (ruleRun w s) = readout (ruleRun w t)

def HeadWordEq (s t : State) : Prop :=
  ∀ w : List HeadAction, readout (headRun w s) = readout (headRun w t)

/-- The core 0-to-3 scan observations plus direct observation of the rule. -/
def ruleSignature (s : State) : (Bool × Bool × Bool × Bool) × Bool :=
  (signature .feedback s, s.g)

/-- Adding the public observation of the head completes the original state. -/
def headSignature (s : State) : ((Bool × Bool × Bool × Bool) × Bool) × Bool :=
  (ruleSignature s, s.h)

private theorem ruleSignature_step (a : RuleAction) :
    ∀ s t : State, ruleSignature s = ruleSignature t →
      ruleSignature (ruleStep a s) = ruleSignature (ruleStep a t) := by
  cases a with
  | base a => cases a <;> decide
  | peekRule => decide

/-- Complete observation is an injective coordinate encoding. -/
theorem head_signature_injective : Function.Injective headSignature := by decide

private theorem headSignature_step (a : HeadAction) :
    ∀ s t : State, headSignature s = headSignature t →
      headSignature (headStep a s) = headSignature (headStep a t) := by
  intro s t h
  exact congrArg (fun u : State => headSignature (headStep a u))
    (head_signature_injective h)

private theorem ruleSignature_readout (s t : State)
    (h : ruleSignature s = ruleSignature t) : readout s = readout t := by
  exact congrArg Prod.fst (congrArg Prod.fst h)

private theorem headSignature_readout (s t : State)
    (h : headSignature s = headSignature t) : readout s = readout t := by
  exact ruleSignature_readout s t (congrArg Prod.fst h)

private theorem ruleSignature_sound (w : List RuleAction) :
    ∀ s t : State, ruleSignature s = ruleSignature t →
      readout (ruleRun w s) = readout (ruleRun w t) := by
  induction w with
  | nil =>
      intro s t h
      exact ruleSignature_readout s t h
  | cons a rest ih =>
      intro s t h
      exact ih (ruleStep a s) (ruleStep a t) (ruleSignature_step a s t h)

private theorem headSignature_sound (w : List HeadAction) :
    ∀ s t : State, headSignature s = headSignature t →
      readout (headRun w s) = readout (headRun w t) := by
  induction w with
  | nil =>
      intro s t h
      exact headSignature_readout s t h
  | cons a rest ih =>
      intro s t h
      exact ih (headStep a s) (headStep a t) (headSignature_step a s t h)

/-- Necessary and sufficient 5-bit observational signature with rule access. -/
theorem ruleWordEq_iff_signature (s t : State) :
    RuleWordEq s t ↔ ruleSignature s = ruleSignature t := by
  constructor
  · intro h
    apply Prod.ext
    · apply Prod.ext
      · simpa [ruleRun, ruleStep, run] using h []
      · apply Prod.ext
        · simpa [ruleRun, ruleStep, run] using h [.base .scan]
        · apply Prod.ext
          · simpa [ruleRun, ruleStep, run] using h [.base .scan, .base .scan]
          · simpa [ruleRun, ruleStep, run] using h [.base .scan, .base .scan, .base .scan]
    · simpa [ruleRun, ruleStep, readout] using h [.peekRule]
  · intro h w
    exact ruleSignature_sound w s t h

/-- Necessary and sufficient 6-bit signature with both rule and head access. -/
theorem headWordEq_iff_signature (s t : State) :
    HeadWordEq s t ↔ headSignature s = headSignature t := by
  constructor
  · intro h
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · simpa [headRun, headStep, run] using h []
        · apply Prod.ext
          · simpa [headRun, headStep, run] using h [.base .scan]
          · apply Prod.ext
            · simpa [headRun, headStep, run] using h [.base .scan, .base .scan]
            · simpa [headRun, headStep, run] using h [.base .scan, .base .scan, .base .scan]
      · simpa [headRun, headStep, readout] using h [.peekRule]
    · simpa [headRun, headStep, readout] using h [.peekHead]
  · intro h w
    exact headSignature_sound w s t h

/-- With a rule probe the quotient has exactly 16 classes. -/
theorem rule_classes : (Finset.univ.image ruleSignature).card = 16 := by decide

/-- With both probes, all 32 original states become distinguishable. -/
theorem head_classes : (Finset.univ.image headSignature).card = 32 := by decide

/-- Full rule-and-head observation distinguishes every labelled state. -/
theorem head_wordEq_iff_eq (s t : State) : HeadWordEq s t ↔ s = t := by
  rw [headWordEq_iff_signature]
  exact ⟨fun h => head_signature_injective h, fun h => congrArg headSignature h⟩

/-- The memory-cell relabelling remains invisible when the rule is readable. -/
theorem symmetry_invisible_with_rule (s : State) :
    RuleWordEq (symmetry s) s := by
  apply (ruleWordEq_iff_signature (symmetry s) s).2
  have h : ∀ s : State, ruleSignature (symmetry s) = ruleSignature s := by decide
  exact h s

private def differentHeads : State := ⟨false, true, false, false, false⟩

/-- The head probe breaks that symmetry, by a one-letter certificate. -/
theorem symmetry_broken_by_head :
    RuleWordEq (symmetry differentHeads) differentHeads ∧
    ¬ HeadWordEq (symmetry differentHeads) differentHeads := by
  constructor
  · exact symmetry_invisible_with_rule differentHeads
  · intro h
    have hbad : readout (headRun [.peekHead] (symmetry differentHeads)) ≠
        readout (headRun [.peekHead] differentHeads) := by decide
    exact hbad (h [.peekHead])

/-- The rule probe reveals a hidden rule bit even for identical memories. -/
private def zeroMem0 : State := ⟨false, false, false, false, false⟩
private def zeroMem1 : State := ⟨false, false, false, false, true⟩

theorem rule_probe_refines_feedback :
    WordEq .feedback zeroMem0 zeroMem1 ∧
    ¬ RuleWordEq zeroMem0 zeroMem1 := by
  constructor
  · exact (wordEq_iff_signature .feedback zeroMem0 zeroMem1).2 (by decide)
  · intro h
    have hbad : readout (ruleRun [.peekRule] zeroMem0) ≠
        readout (ruleRun [.peekRule] zeroMem1) := by decide
    exact hbad (h [.peekRule])

end SelfRewritingObserver
