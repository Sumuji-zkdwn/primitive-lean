/-!
Choice independence for actual iterated Stieltjes signatures of continuous
bounded-variation coordinates. Jordan decompositions are compared through
their signed coordinate increments, not through an assumed signature equality.
-/

noncomputable section

namespace LinearInputCurveWordBVSignature

open Real Set MeasureTheory Filter
open scoped Topology
open LinearInputCurveWordStieltjes

def SameIncrements (p m q n : StieltjesFunction ℝ) : Prop :=
  ∀ a b, (p b - p a) - (m b - m a) = (q b - q a) - (n b - n a)

theorem continuous_stieltjes_noAtoms (p : StieltjesFunction ℝ) (hp : Continuous (p : ℝ → ℝ)) :
    NullSingletonClass p.measure := by
  constructor
  intro t
  rw [StieltjesFunction.measure_singleton, hp.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]

theorem primitive_stieltjes_continuous (p : StieltjesFunction ℝ)
    (hp : Continuous (p : ℝ → ℝ)) {F : ℝ → ℝ} (hF : Continuous F) (a : ℝ) :
    Continuous (fun t => ∫ s in a..t, F s ∂p.measure) := by
  let : NullSingletonClass p.measure := continuous_stieltjes_noAtoms p hp
  exact intervalIntegral.continuous_primitive (fun x y => hF.intervalIntegrable x y) a

theorem stieltjesIntegral_continuous (p m : StieltjesFunction ℝ)
    (hp : Continuous (p : ℝ → ℝ)) (hm : Continuous (m : ℝ → ℝ))
    {F : ℝ → ℝ} (hF : Continuous F) (a : ℝ) :
    Continuous (fun t => stieltjesIntegral p m a t F) :=
  (primitive_stieltjes_continuous p hp hF a).sub (primitive_stieltjes_continuous m hm hF a)

theorem sameIncrements_measure_sum {p m q n : StieltjesFunction ℝ}
    (h : SameIncrements p m q n) : p.measure + n.measure = q.measure + m.measure := by
  rw [← StieltjesFunction.measure_add, ← StieltjesFunction.measure_add]
  apply Measure.ext_of_Ioc
  intro a b _
  rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc]
  congr 1
  change (p b + n b) - (p a + n a) = (q b + m b) - (q a + m a)
  linarith [h a b]

theorem intervalIntegral_add_measure (μ ν : Measure ℝ) {F : ℝ → ℝ} (a b : ℝ)
    (hμ : IntervalIntegrable F μ a b) (hν : IntervalIntegrable F ν a b) :
    (∫ t in a..b, F t ∂(μ + ν)) =
      (∫ t in a..b, F t ∂μ) + ∫ t in a..b, F t ∂ν := by
  simp only [intervalIntegral, Measure.restrict_add]
  rw [integral_add_measure hμ.1 hν.1, integral_add_measure hμ.2 hν.2]
  ring

theorem stieltjesIntegral_independent {p m q n : StieltjesFunction ℝ}
    (h : SameIncrements p m q n) {F : ℝ → ℝ} (hF : Continuous F) (a b : ℝ) :
    stieltjesIntegral p m a b F = stieltjesIntegral q n a b F := by
  have he := congrArg (fun μ : Measure ℝ => ∫ t in a..b, F t ∂μ) (sameIncrements_measure_sum h)
  change (∫ t in a..b, F t ∂(p.measure + n.measure)) =
    ∫ t in a..b, F t ∂(q.measure + m.measure) at he
  rw [intervalIntegral_add_measure p.measure n.measure a b
      (hF.intervalIntegrable a b) (hF.intervalIntegrable a b),
    intervalIntegral_add_measure q.measure m.measure a b
      (hF.intervalIntegrable a b) (hF.intervalIntegrable a b)] at he
  unfold stieltjesIntegral
  linarith

theorem reverseStieltjes_continuous {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a : ℝ) (w : List ι) : Continuous (reverseStieltjes p m a w) := by
  induction w with
  | nil => exact continuous_const
  | cons i w ih => exact stieltjesIntegral_continuous (p i) (m i) (hp i) (hm i) ih a

theorem reverseStieltjes_independent {ι : Type*} {p m q n : ι → StieltjesFunction ℝ}
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (h : ∀ i, SameIncrements (p i) (m i) (q i) (n i)) (a : ℝ) (w : List ι) (b : ℝ) :
    reverseStieltjes p m a w b = reverseStieltjes q n a w b := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih =>
    change stieltjesIntegral (p i) (m i) a b _ = stieltjesIntegral (q i) (n i) a b _
    rw [show reverseStieltjes p m a w = reverseStieltjes q n a w from funext ih]
    exact stieltjesIntegral_independent (h i) (reverseStieltjes_continuous q n hq hn a w) a b

/-- Equality of signed coordinate increments implies equality of every
Stieltjes-signature coefficient, independently of the selected Jordan pair. -/
theorem stieltjesSignature_independent {ι : Type*} {p m q n : ι → StieltjesFunction ℝ}
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (h : ∀ i, SameIncrements (p i) (m i) (q i) (n i)) (a b : ℝ) (w : List ι) :
    stieltjesSignature p m a b w = stieltjesSignature q n a b w :=
  reverseStieltjes_independent hq hn h a w.reverse b

end LinearInputCurveWordBVSignature
