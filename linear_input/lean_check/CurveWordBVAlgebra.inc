/-!
All-degree formal algebra of the actual continuous-BV Stieltjes signature.
Shuffle gives group-likeness, Friedrichs gives homogeneous free-Lie witnesses,
and Chen becomes BCH. None of these asserts geometric tree-like uniqueness.
-/

noncomputable section

namespace LinearInputCurveWordBVAlgebra

open LinearInputCurveWordStieltjes LinearInputCurveWordBVShuffle LinearInputCurveWordBVChen
open LinearInputCurveWordFormalSeries LinearInputCurveWordCoproduct LinearInputCurveWordFriedrichs

theorem signature_groupLike {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (hab : a ≤ b) : GroupLike (stieltjesSignature p m a b) := by
  constructor
  · rfl
  · intro u w
    exact (stieltjesSignature_shuffle p m hp hm a b hab u w).symm

theorem signature_product {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b c : ℝ) :
    stieltjesSignature p m a c = product (stieltjesSignature p m a b) (stieltjesSignature p m b c) := by
  funext w
  exact stieltjesSignature_chen p m hp hm a b c w

theorem signature_logarithm_primitive {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (hab : a ≤ b) : Primitive (logarithm (stieltjesSignature p m a b)) :=
  logarithm_primitive (signature_groupLike p m hp hm a b hab)

/-- The completed free-Lie conclusion uses actual finite homogeneous free-Lie
elements over a finite alphabet, and holds at every degree. -/
theorem signature_logarithm_completed_lie {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (hab : a ≤ b) :
    ∃ L : ℕ → FreeLieAlgebra ℝ ι, L 0 = 0 ∧
      (∀ n, L n ∈ lieDegree ι n) ∧
      ∀ n w, lieExpansion (L n) w =
        if w.length = n then logarithm (stieltjesSignature p m a b) w else 0 :=
  primitive_completed_lie_expansion (signature_logarithm_primitive p m hp hm a b hab)

theorem signature_logarithm_chen {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b c : ℝ) :
    logarithm (stieltjesSignature p m a c) =
      bch (logarithm (stieltjesSignature p m a b)) (logarithm (stieltjesSignature p m b c)) := by
  unfold bch
  rw [formalExp_logarithm _ (show stieltjesSignature p m a b [] = 1 from rfl),
    formalExp_logarithm _ (show stieltjesSignature p m b c [] = 1 from rfl),
    ← signature_product p m hp hm a b c]

theorem signature_bch_completed_lie {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ L : ℕ → FreeLieAlgebra ℝ ι, L 0 = 0 ∧
      (∀ n, L n ∈ lieDegree ι n) ∧
      ∀ n w, lieExpansion (L n) w = if w.length = n then
        bch (logarithm (stieltjesSignature p m a b)) (logarithm (stieltjesSignature p m b c)) w else 0 :=
  bch_completed_lie (signature_logarithm_primitive p m hp hm a b hab)
    (signature_logarithm_primitive p m hp hm b c hbc)

end LinearInputCurveWordBVAlgebra
