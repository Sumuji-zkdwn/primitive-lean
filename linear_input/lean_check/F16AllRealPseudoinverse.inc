/-!
Full-parameter Gram Moore--Penrose construction for the original F16 pencil.

The imported projectors come from the signed Cayley--Dickson table.
The four Penrose identities below concern N_t = A_t^T A_t.
The distinct candidate for A_t^+ is also defined; the Gram identities
alone must not be misreported as all four Penrose identities for A_t.
-/

noncomputable section
open scoped Matrix

namespace LinearInputF16AllRealPinv

open LinearInputF16Spectral LinearInputF16Determinant

abbrev RMat := Matrix Idx Idx ℝ
abbrev castQ (M : QMat) : RMat := M.map (Rat.castHom ℝ)

abbrev Pplus : RMat := castQ plus
abbrev Pminus : RMat := castQ minus
abbrev Pzero : RMat := castQ zero

private theorem cast_product (A B C : QMat) (h : A * B = C) :
    castQ A * castQ B = castQ C := by
  have hc := congrArg castQ h
  simpa only [castQ, Matrix.map_mul] using hc

theorem plus_idem : Pplus * Pplus = Pplus := by
  simpa only [Pplus] using cast_product plus plus plus plus_idempotent

theorem minus_idem : Pminus * Pminus = Pminus := by
  simpa only [Pminus] using cast_product minus minus minus minus_idempotent

theorem zero_idem : Pzero * Pzero = Pzero := by
  simpa only [Pzero] using cast_product zero zero zero zero_idempotent

theorem plus_minus : Pplus * Pminus = 0 := by
  simpa [Pplus, Pminus, castQ] using
    (cast_product plus minus 0 plus_minus_zero)

theorem plus_zero : Pplus * Pzero = 0 := by
  simpa [Pplus, Pzero, castQ] using
    (cast_product plus zero 0 plus_zero_zero)

theorem minus_zero : Pminus * Pzero = 0 := by
  simpa [Pminus, Pzero, castQ] using
    (cast_product minus zero 0 minus_zero_zero)

theorem plus_sym : Pplusᵀ = Pplus := by
  ext i j
  change (plus j i : ℝ) = (plus i j : ℝ)
  exact congrArg (fun q : ℚ => (q : ℝ))
    (congrArg (fun M : QMat => M i j) plus_symmetric)

theorem minus_sym : Pminusᵀ = Pminus := by
  ext i j
  change (minus j i : ℝ) = (minus i j : ℝ)
  exact congrArg (fun q : ℚ => (q : ℝ))
    (congrArg (fun M : QMat => M i j) minus_symmetric)

theorem zero_sym : Pzeroᵀ = Pzero := by
  ext i j
  change (zero j i : ℝ) = (zero i j : ℝ)
  exact congrArg (fun q : ℚ => (q : ℝ))
    (congrArg (fun M : QMat => M i j) zero_symmetric)

theorem minus_plus : Pminus * Pplus = 0 := by
  have h := congrArg (fun M : RMat => Mᵀ) plus_minus
  simpa [Matrix.transpose_mul, plus_sym, minus_sym] using h

theorem zero_plus : Pzero * Pplus = 0 := by
  have h := congrArg (fun M : RMat => Mᵀ) plus_zero
  simpa [Matrix.transpose_mul, plus_sym, zero_sym] using h

theorem zero_minus : Pzero * Pminus = 0 := by
  have h := congrArg (fun M : RMat => Mᵀ) minus_zero
  simpa [Matrix.transpose_mul, minus_sym, zero_sym] using h

theorem complete : Pplus + Pminus + Pzero = 1 := by
  have h := congrArg castQ projector_sum
  simpa [Pplus, Pminus, Pzero, castQ] using h

/-- Simultaneously diagonal in the exact rationally defined sectors. -/
def spectral (a b c : ℝ) : RMat :=
  a • Pplus + b • Pminus + c • Pzero

theorem spectral_mul (a b c d e f : ℝ) :
    spectral a b c * spectral d e f =
      spectral (a * d) (b * e) (c * f) := by
  simp [spectral, Matrix.add_mul, Matrix.mul_add, smul_mul_assoc,
    mul_smul_comm, smul_smul, plus_idem, minus_idem, zero_idem,
    plus_minus, plus_zero, minus_zero, minus_plus, zero_plus,
    zero_minus, add_assoc]

theorem spectral_sym (a b c : ℝ) :
    (spectral a b c)ᵀ = spectral a b c := by
  simp [spectral, Matrix.transpose_add, Matrix.transpose_smul,
    plus_sym, minus_sym, zero_sym]

theorem spectral_one : spectral 1 1 1 = 1 := by
  simpa [spectral] using complete

/-- Exact Gram of the original signed 16 by 16 real pencil. -/
def gram (t : ℝ) : RMat :=
  (realPencilAll t)ᵀ * realPencilAll t

/-- All t, not merely integer probes: the same rational projector system. -/
theorem gram_spectral (t : ℝ) :
    gram t = spectral ((t + 1) ^ 2) ((t - 1) ^ 2) (1 + t ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, spectral, Pplus, Pminus, Pzero, castQ,
      plus, minus, zero, realSector, cross, Matrix.mul_apply,
      Fin.sum_univ_succ, realPencilAll, entryThree, entryTen,
      LinearInputF16Holonomy.rightIndex, LinearInputF16Holonomy.eps,
      LinearInputF16Holonomy.epsTable] <;> ring

/-- Spectral Moore--Penrose scalar coefficient: never invert a zero eigenvalue. -/
def inv0 (x : ℝ) : ℝ := if x = 0 then 0 else x⁻¹

theorem inv0_penrose_one (x : ℝ) : x * inv0 x * x = x := by
  by_cases h : x = 0
  · simp [inv0, h]
  · simp [inv0, h, mul_assoc]

theorem inv0_penrose_two (x : ℝ) : inv0 x * x * inv0 x = inv0 x := by
  by_cases h : x = 0
  · simp [inv0, h]
  · simp [inv0, h, mul_assoc]

theorem spectral_penrose_one (a b c : ℝ) :
    spectral a b c * spectral (inv0 a) (inv0 b) (inv0 c) *
        spectral a b c = spectral a b c := by
  rw [spectral_mul, spectral_mul]
  simp only [inv0_penrose_one]

theorem spectral_penrose_two (a b c : ℝ) :
    spectral (inv0 a) (inv0 b) (inv0 c) * spectral a b c *
        spectral (inv0 a) (inv0 b) (inv0 c) =
      spectral (inv0 a) (inv0 b) (inv0 c) := by
  rw [spectral_mul, spectral_mul]
  simp only [inv0_penrose_two]

theorem spectral_penrose_three (a b c : ℝ) :
    (spectral a b c * spectral (inv0 a) (inv0 b) (inv0 c))ᵀ =
      spectral a b c * spectral (inv0 a) (inv0 b) (inv0 c) := by
  rw [spectral_mul, spectral_sym]

theorem spectral_penrose_four (a b c : ℝ) :
    (spectral (inv0 a) (inv0 b) (inv0 c) * spectral a b c)ᵀ =
      spectral (inv0 a) (inv0 b) (inv0 c) * spectral a b c := by
  rw [spectral_mul, spectral_sym]

/-- A single real-valued formula, including the singular points. -/
def gramPinv (t : ℝ) : RMat :=
  spectral (inv0 ((t + 1) ^ 2)) (inv0 ((t - 1) ^ 2))
    (inv0 (1 + t ^ 2))

theorem gram_penrose_one (t : ℝ) :
    gram t * gramPinv t * gram t = gram t := by
  rw [gram_spectral]
  exact spectral_penrose_one _ _ _

theorem gram_penrose_two (t : ℝ) :
    gramPinv t * gram t * gramPinv t = gramPinv t := by
  rw [gram_spectral]
  exact spectral_penrose_two _ _ _

theorem gram_penrose_three (t : ℝ) :
    (gram t * gramPinv t)ᵀ = gram t * gramPinv t := by
  rw [gram_spectral]
  exact spectral_penrose_three _ _ _

theorem gram_penrose_four (t : ℝ) :
    (gramPinv t * gram t)ᵀ = gramPinv t * gram t := by
  rw [gram_spectral]
  exact spectral_penrose_four _ _ _

theorem gramPinv_at_one :
    gramPinv 1 = (1 / 4 : ℝ) • Pplus + (1 / 2 : ℝ) • Pzero := by
  norm_num [gramPinv, spectral, inv0]

theorem gramPinv_at_minus_one :
    gramPinv (-1) = (1 / 4 : ℝ) • Pminus + (1 / 2 : ℝ) • Pzero := by
  norm_num [gramPinv, spectral, inv0]

theorem gramPinv_regular (t : ℝ) (hpos : t ≠ 1) (hneg : t ≠ -1) :
    gramPinv t =
      spectral (((t + 1) ^ 2)⁻¹) (((t - 1) ^ 2)⁻¹)
        ((1 + t ^ 2)⁻¹) := by
  have ha : (t + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by
    intro h; apply hneg; linarith)
  have hb : (t - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by
    intro h; apply hpos; linarith)
  have hc : 1 + t ^ 2 ≠ 0 := by positivity
  simp [gramPinv, inv0, ha, hb, hc]

theorem gram_regular_two_sided (t : ℝ) (hpos : t ≠ 1) (hneg : t ≠ -1) :
    gram t * gramPinv t = 1 ∧ gramPinv t * gram t = 1 := by
  have ha : (t + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by
    intro h; apply hneg; linarith)
  have hb : (t - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by
    intro h; apply hpos; linarith)
  have hc : 1 + t ^ 2 ≠ 0 := by positivity
  have h1 : (t + 1) ^ 2 * inv0 ((t + 1) ^ 2) = 1 := by
    simp [inv0, ha]
  have h2 : (t - 1) ^ 2 * inv0 ((t - 1) ^ 2) = 1 := by
    simp [inv0, hb]
  have h3 : (1 + t ^ 2) * inv0 (1 + t ^ 2) = 1 := by
    simp [inv0, hc]
  constructor
  · calc
      gram t * gramPinv t =
        spectral ((t + 1) ^ 2) ((t - 1) ^ 2) (1 + t ^ 2) *
          spectral (inv0 ((t + 1) ^ 2)) (inv0 ((t - 1) ^ 2))
            (inv0 (1 + t ^ 2)) := by rw [gram_spectral]; rfl
      _ = spectral 1 1 1 := by rw [spectral_mul, h1, h2, h3]
      _ = 1 := spectral_one
  · calc
      gramPinv t * gram t =
        spectral (inv0 ((t + 1) ^ 2)) (inv0 ((t - 1) ^ 2))
          (inv0 (1 + t ^ 2)) *
          spectral ((t + 1) ^ 2) ((t - 1) ^ 2) (1 + t ^ 2) := by
            rw [gram_spectral]; rfl
      _ = spectral 1 1 1 := by
        rw [spectral_mul]
        simp only [mul_comm (inv0 ((t + 1) ^ 2)) ((t + 1) ^ 2),
          mul_comm (inv0 ((t - 1) ^ 2)) ((t - 1) ^ 2),
          mul_comm (inv0 (1 + t ^ 2)) (1 + t ^ 2), h1, h2, h3]
      _ = 1 := spectral_one

/-- The left-penc\-il candidate is distinct from the normal-matrix inverse. -/
def leftPinvCandidate (t : ℝ) : RMat :=
  gramPinv t * (realPencilAll t)ᵀ

theorem leftPinv_penrose_two (t : ℝ) :
    leftPinvCandidate t * realPencilAll t * leftPinvCandidate t =
      leftPinvCandidate t := by
  calc
    leftPinvCandidate t * realPencilAll t * leftPinvCandidate t =
      (gramPinv t * gram t * gramPinv t) * (realPencilAll t)ᵀ := by
        simp [leftPinvCandidate, gram, Matrix.mul_assoc]
    _ = leftPinvCandidate t := by rw [gram_penrose_two]; rfl

theorem leftPinv_penrose_four (t : ℝ) :
    (leftPinvCandidate t * realPencilAll t)ᵀ =
      leftPinvCandidate t * realPencilAll t := by
  simpa [leftPinvCandidate, gram, Matrix.mul_assoc] using
    gram_penrose_four t

end LinearInputF16AllRealPinv
