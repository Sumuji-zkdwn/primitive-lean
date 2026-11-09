import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
Analytic construction. A polynomial material inverse is constructed by an actual
contraction. The later weighted-convolution file must supply the displayed
bounded bilinear product; no PDE solution or material inverse is assumed.
-/

namespace KerrKoopman.Phase3PolynomialInverse

noncomputable section

open Set Metric
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def square (B : E →L[ℝ] E →L[ℝ] E) (x : E) : E := B x x

def cube (B : E →L[ℝ] E →L[ℝ] E) (x : E) : E := B x (square B x)

def correction (B : E →L[ℝ] E →L[ℝ] E) (x : E) : E :=
  (1 / 2 : ℝ) • square B x + (1 / 6 : ℝ) • cube B x

def inverseStep (B : E →L[ℝ] E →L[ℝ] E) (d x : E) : E :=
  (1 / 2 : ℝ) • d - correction B x

theorem square_norm_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (x : E) :
    ‖square B x‖ ≤ ‖x‖ ^ 2 := by simpa only [square, pow_two] using hB x x

theorem cube_norm_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (x : E) :
    ‖cube B x‖ ≤ ‖x‖ ^ 3 := by
  calc
    _ ≤ ‖x‖ * ‖square B x‖ := hB _ _
    _ ≤ ‖x‖ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left (square_norm_le B hB x) (norm_nonneg _)
    _ = _ := by ring

theorem square_difference (B : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    square B x - square B y = B (x - y) x + B y (x - y) := by
  simp only [square, map_sub, ContinuousLinearMap.sub_apply]
  abel

theorem square_norm_sub_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (r : ℝ) (_hr : 0 ≤ r)
    (x y : E) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖square B x - square B y‖ ≤ (2 * r) * ‖x - y‖ := by
  rw [square_difference]
  calc
    _ ≤ ‖B (x - y) x‖ + ‖B y (x - y)‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ := add_le_add (hB _ _) (hB _ _)
    _ ≤ ‖x - y‖ * r + r * ‖x - y‖ := by gcongr
    _ = _ := by ring

theorem cube_norm_sub_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (r : ℝ) (hr : 0 ≤ r)
    (x y : E) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖cube B x - cube B y‖ ≤ (3 * r ^ 2) * ‖x - y‖ := by
  have hid : cube B x - cube B y =
      B (x - y) (square B x) + B y (square B x - square B y) := by
    simp only [cube, map_sub, ContinuousLinearMap.sub_apply]
    abel
  have hsq : ‖square B x‖ ≤ r ^ 2 := (square_norm_le B hB x).trans (by gcongr)
  rw [hid]
  calc
    _ ≤ ‖B (x - y) (square B x)‖ + ‖B y (square B x - square B y)‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖square B x‖ + ‖y‖ * ‖square B x - square B y‖ :=
      add_le_add (hB _ _) (hB _ _)
    _ ≤ ‖x - y‖ * r ^ 2 + r * ((2 * r) * ‖x - y‖) := by
      gcongr
      exact square_norm_sub_le B hB r hr x y hx hy
    _ = _ := by ring

theorem correction_norm_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (x : E) :
    ‖correction B x‖ ≤ ‖x‖ ^ 2 / 2 + ‖x‖ ^ 3 / 6 := by
  have hn := norm_add_le ((1 / 2 : ℝ) • square B x) ((1 / 6 : ℝ) • cube B x)
  simp only [norm_smul, Real.norm_eq_abs] at hn
  norm_num at hn
  have hs := square_norm_le B hB x
  have hc := cube_norm_le B hB x
  change ‖(1 / 2 : ℝ) • square B x + (1 / 6 : ℝ) • cube B x‖ ≤ _
  linarith

theorem correction_norm_sub_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (r : ℝ) (hr : 0 ≤ r)
    (x y : E) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖correction B x - correction B y‖ ≤ (r + r ^ 2 / 2) * ‖x - y‖ := by
  have hid : correction B x - correction B y =
      (1 / 2 : ℝ) • (square B x - square B y) +
        (1 / 6 : ℝ) • (cube B x - cube B y) := by
    simp only [correction, smul_sub]
    abel
  rw [hid]
  have hn := norm_add_le ((1 / 2 : ℝ) • (square B x - square B y))
    ((1 / 6 : ℝ) • (cube B x - cube B y))
  simp only [norm_smul, Real.norm_eq_abs] at hn
  norm_num at hn
  have hs := square_norm_sub_le B hB r hr x y hx hy
  have hc := cube_norm_sub_le B hB r hr x y hx hy
  nlinarith

theorem inverseStep_norm_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d x : E)
    (hd : ‖d‖ ≤ 134 / 375) (hx : ‖x‖ ≤ 1 / 5) :
    ‖inverseStep B d x‖ ≤ 1 / 5 := by
  have hn := norm_sub_le ((1 / 2 : ℝ) • d) (correction B x)
  simp only [norm_smul, Real.norm_eq_abs] at hn
  norm_num at hn
  have hc := correction_norm_le B hB x
  have hx2 : ‖x‖ ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by gcongr
  have hx3 : ‖x‖ ^ 3 ≤ (1 / 5 : ℝ) ^ 3 := by gcongr
  change ‖(1 / 2 : ℝ) • d - correction B x‖ ≤ _
  linarith

theorem inverseStep_norm_sub_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d x y : E)
    (hx : ‖x‖ ≤ 1 / 5) (hy : ‖y‖ ≤ 1 / 5) :
    ‖inverseStep B d x - inverseStep B d y‖ ≤ (11 / 50 : ℝ) * ‖x - y‖ := by
  have hid : inverseStep B d x - inverseStep B d y = -(correction B x - correction B y) := by
    dsimp [inverseStep]
    abel
  rw [hid, norm_neg]
  have h := correction_norm_sub_le B hB (1 / 5) (by norm_num) x y hx hy
  norm_num at h
  exact h

/-- An actual inverse element exists in the prescribed ball. -/
theorem exists_inverse_iterates [CompleteSpace E] (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) :
    ∃ e : E, ‖e‖ ≤ 1 / 5 ∧ inverseStep B d e = e ∧
      Filter.Tendsto (fun n : ℕ => (inverseStep B d)^[n] 0) Filter.atTop (𝓝 e) := by
  let s : Set E := closedBall 0 (1 / 5)
  have hmaps : MapsTo (inverseStep B d) s s := by
    intro x hx
    apply mem_closedBall_zero_iff.mpr
    exact inverseStep_norm_le B hB d x hd (mem_closedBall_zero_iff.mp hx)
  have hcontract : ContractingWith (11 / 50 : ℝ≥0) (hmaps.restrict (inverseStep B d) s s) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (inverseStep B d x.val) (inverseStep B d y.val) ≤
        ((11 / 50 : ℝ≥0) : ℝ) * dist x.val y.val
      simp only [dist_eq_norm]
      norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
      exact inverseStep_norm_sub_le B hB d x y
        (mem_closedBall_zero_iff.mp x.property) (mem_closedBall_zero_iff.mp y.property)
  obtain ⟨e, he, hfix, hlim, _⟩ := ContractingWith.exists_fixedPoint'
    (isClosed_closedBall.isComplete) hmaps hcontract
    (show (0 : E) ∈ s from mem_closedBall_self (by norm_num)) (edist_ne_top _ _)
  exact ⟨e, mem_closedBall_zero_iff.mp he, hfix, hlim⟩

theorem exists_inverse [CompleteSpace E] (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) :
    ∃ e : E, ‖e‖ ≤ 1 / 5 ∧ inverseStep B d e = e := by
  obtain ⟨e, he, hf, _⟩ := exists_inverse_iterates B hB d hd
  exact ⟨e, he, hf⟩

variable [CompleteSpace E]

def inverse (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) : E :=
  (exists_inverse B hB d hd).choose

theorem inverse_norm_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) :
    ‖inverse B hB d hd‖ ≤ 1 / 5 := (exists_inverse B hB d hd).choose_spec.1

theorem inverse_fixedpoint (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) :
    inverseStep B d (inverse B hB d hd) = inverse B hB d hd :=
  (exists_inverse B hB d hd).choose_spec.2

theorem inverse_unique (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375)
    (e : E) (he : ‖e‖ ≤ 1 / 5) (hf : inverseStep B d e = e) :
    e = inverse B hB d hd := by
  have hc := inverseStep_norm_sub_le B hB d e (inverse B hB d hd)
    he (inverse_norm_le B hB d hd)
  rw [hf, inverse_fixedpoint] at hc
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  linarith [norm_nonneg (e - inverse B hB d hd)]

theorem iterates_tendsto_inverse (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) :
    Filter.Tendsto (fun n : ℕ => (inverseStep B d)^[n] 0)
      Filter.atTop (𝓝 (inverse B hB d hd)) := by
  obtain ⟨e, he, hf, ht⟩ := exists_inverse_iterates B hB d hd
  simpa only [inverse_unique B hB d hd e he hf] using ht

theorem inverse_constitutive (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) :
    (2 : ℝ) • inverse B hB d hd + square B (inverse B hB d hd) +
      (1 / 3 : ℝ) • cube B (inverse B hB d hd) = d := by
  let e := inverse B hB d hd
  have hf : (1 / 2 : ℝ) • d - correction B e = e := inverse_fixedpoint B hB d hd
  have h := congrArg (fun x : E => (2 : ℝ) • x) hf
  dsimp only [correction] at h
  have hid : (2 : ℝ) • ((1 / 2 : ℝ) • d -
      ((1 / 2 : ℝ) • square B e + (1 / 6 : ℝ) • cube B e)) =
        d - square B e - (1 / 3 : ℝ) • cube B e := by module
  rw [hid] at h
  change (2 : ℝ) • e + square B e + (1 / 3 : ℝ) • cube B e = d
  rw [← h]
  abel

theorem inverse_norm_sub_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d₁ d₂ : E)
    (hd₁ : ‖d₁‖ ≤ 134 / 375) (hd₂ : ‖d₂‖ ≤ 134 / 375) :
    ‖inverse B hB d₁ hd₁ - inverse B hB d₂ hd₂‖ ≤ (25 / 39 : ℝ) * ‖d₁ - d₂‖ := by
  let e₁ := inverse B hB d₁ hd₁
  let e₂ := inverse B hB d₂ hd₂
  have h₁ : (1 / 2 : ℝ) • d₁ - correction B e₁ = e₁ := inverse_fixedpoint B hB d₁ hd₁
  have h₂ : (1 / 2 : ℝ) • d₂ - correction B e₂ = e₂ := inverse_fixedpoint B hB d₂ hd₂
  have hid : e₁ - e₂ = (1 / 2 : ℝ) • (d₁ - d₂) - (correction B e₁ - correction B e₂) := by
    calc
      e₁ - e₂ = ((1 / 2 : ℝ) • d₁ - correction B e₁) -
          ((1 / 2 : ℝ) • d₂ - correction B e₂) := congrArg₂ (· - ·) h₁.symm h₂.symm
      _ = _ := by module
  have hn := norm_sub_le ((1 / 2 : ℝ) • (d₁ - d₂)) (correction B e₁ - correction B e₂)
  rw [← hid] at hn
  simp only [norm_smul, Real.norm_eq_abs] at hn
  norm_num at hn
  have hc := correction_norm_sub_le B hB (1 / 5) (by norm_num) e₁ e₂
    (inverse_norm_le B hB d₁ hd₁) (inverse_norm_le B hB d₂ hd₂)
  norm_num at hc
  change ‖e₁ - e₂‖ ≤ _
  linarith

def nonlinear (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) : E :=
  -correction B (inverse B hB d hd)

theorem nonlinear_eq (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) :
    nonlinear B hB d hd = inverse B hB d hd - (1 / 2 : ℝ) • d := by
  have h := inverse_fixedpoint B hB d hd
  change (1 / 2 : ℝ) • d - correction B (inverse B hB d hd) = inverse B hB d hd at h
  rw [← h]
  dsimp only [nonlinear]
  abel

theorem nonlinear_norm_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : E) (hd : ‖d‖ ≤ 134 / 375) :
    ‖nonlinear B hB d hd‖ ≤ 8 / 375 := by
  let e := inverse B hB d hd
  have he : ‖e‖ ≤ 1 / 5 := inverse_norm_le B hB d hd
  have he2 : ‖e‖ ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by gcongr
  have he3 : ‖e‖ ^ 3 ≤ (1 / 5 : ℝ) ^ 3 := by gcongr
  have hc := correction_norm_le B hB e
  change ‖-correction B e‖ ≤ _
  rw [norm_neg]
  linarith

theorem nonlinear_norm_sub_le (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d₁ d₂ : E)
    (hd₁ : ‖d₁‖ ≤ 134 / 375) (hd₂ : ‖d₂‖ ≤ 134 / 375) :
    ‖nonlinear B hB d₁ hd₁ - nonlinear B hB d₂ hd₂‖ ≤ (11 / 78 : ℝ) * ‖d₁ - d₂‖ := by
  have hc := correction_norm_sub_le B hB (1 / 5) (by norm_num)
    (inverse B hB d₁ hd₁) (inverse B hB d₂ hd₂)
    (inverse_norm_le B hB d₁ hd₁) (inverse_norm_le B hB d₂ hd₂)
  have hi := inverse_norm_sub_le B hB d₁ d₂ hd₁ hd₂
  norm_num at hc
  change ‖-correction B (inverse B hB d₁ hd₁) - -correction B (inverse B hB d₂ hd₂)‖ ≤ _
  rw [neg_sub_neg, norm_sub_rev]
  linarith

def nonlinearOnBall (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (d : closedBall (0 : E) (134 / 375)) : E :=
  nonlinear B hB d (mem_closedBall_zero_iff.mp d.property)

theorem nonlinearOnBall_lipschitz (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) :
    LipschitzWith (11 / 78 : ℝ≥0) (nonlinearOnBall B hB) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (nonlinearOnBall B hB x) (nonlinearOnBall B hB y) ≤
    ((11 / 78 : ℝ≥0) : ℝ) * dist x.val y.val
  simp only [dist_eq_norm]
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
  exact nonlinear_norm_sub_le B hB x y _ _

end

end KerrKoopman.Phase3PolynomialInverse
