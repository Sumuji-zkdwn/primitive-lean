import PrimitiveMain
noncomputable section
namespace CopyControl
-- Positive controls: same objects written from scratch under new names.
def fCopy (a b c t : ℝ) : ℝ := a * t ^ 4 / 4 + b * t ^ 2 / 2 - c * t
def ECopy (a b c t s : ℝ) : ℝ := (a * t ^ 4 / 4 + b * t ^ 2 / 2 - c * t) + (s - Real.sqrt 2 * t) ^ 2 / 2
def inputCopy (a b t : ℝ) : ℝ := a * t ^ 3 + b * t
-- Same value, different presentation (needs ring reasoning, not unfolding).
def fRearranged (a b c t : ℝ) : ℝ := - c * t + b * t ^ 2 / 2 + a * t ^ 4 / 4
-- Negative control: same type, different function.
def fWrong (a b c t : ℝ) : ℝ := a * t ^ 4 / 4 + b * t ^ 2 / 2 + c * t
end CopyControl
