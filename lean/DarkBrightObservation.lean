import Mathlib

/-!
Two complex amplitudes, represented by four real coordinates.  The observed
quantity is B * conjugate D, not an asserted photon amplitude.  The mixer is
(B,D) -> (c B - i s D, c D - i s B).  It is norm preserving when c^2+s^2=1.
All results are algebraic identities or deterministic observation statements.
No particle ontology, quantization, Maxwell dynamics or physical time law
is assumed or derived.  The bridge file uses the repository's actual WordEq.
-/

noncomputable section
namespace DarkBrightObservation

structure Spinor where
  br : ℝ
  bi : ℝ
  dr : ℝ
  di : ℝ

abbrev Observation := ℝ × ℝ
abbrev Summary := ℝ × ℝ × ℝ

def reQ (x : Spinor) : ℝ := x.br * x.dr + x.bi * x.di
def imQ (x : Spinor) : ℝ := x.bi * x.dr - x.br * x.di
def delta (x : Spinor) : ℝ := x.br^2 + x.bi^2 - (x.dr^2 + x.di^2)
def norm2 (x : Spinor) : ℝ := x.br^2 + x.bi^2 + x.dr^2 + x.di^2
def output (x : Spinor) : Observation := (reQ x, imQ x)
def summary (x : Spinor) : Summary := (reQ x, imQ x, delta x)
def project (q : Summary) : Observation := (q.1, q.2.1)

def mix (c s : ℝ) (x : Spinor) : Spinor :=
  ⟨c*x.br + s*x.di, c*x.bi - s*x.dr,
   c*x.dr + s*x.bi, c*x.di - s*x.br⟩

def evolution (c s : ℝ) (q : Summary) : Summary :=
  ((c^2+s^2)*q.1, (c^2-s^2)*q.2.1+c*s*q.2.2,
   (c^2-s^2)*q.2.2-4*c*s*q.2.1)

theorem reQ_mix (c s : ℝ) (x : Spinor) :
    reQ (mix c s x) = (c^2+s^2)*reQ x := by
  dsimp [reQ, mix]
  ring

theorem imQ_mix (c s : ℝ) (x : Spinor) :
    imQ (mix c s x) = (c^2-s^2)*imQ x+c*s*delta x := by
  dsimp [imQ, mix, delta]
  ring

theorem delta_mix (c s : ℝ) (x : Spinor) :
    delta (mix c s x) = (c^2-s^2)*delta x-4*c*s*imQ x := by
  dsimp [delta, mix, imQ]
  ring

theorem norm2_mix (c s : ℝ) (x : Spinor) :
    norm2 (mix c s x) = (c^2+s^2)*norm2 x := by
  dsimp [norm2, mix]
  ring

theorem summary_mix (c s : ℝ) (x : Spinor) :
    summary (mix c s x) = evolution c s (summary x) := by
  exact Prod.ext (reQ_mix c s x)
    (Prod.ext (imQ_mix c s x) (delta_mix c s x))

theorem norm2_preserved (c s : ℝ) (h : c^2+s^2=1) (x : Spinor) :
    norm2 (mix c s x) = norm2 x := by
  rw [norm2_mix, h, one_mul]

theorem sphere_identity (x : Spinor) :
    (2*reQ x)^2 + (2*imQ x)^2 + (delta x)^2 = (norm2 x)^2 := by
  dsimp [reQ, imQ, delta, norm2]
  ring

theorem norm2_nonnegative (x : Spinor) : 0 ≤ norm2 x := by
  dsimp [norm2]
  positivity

/-- At fixed total norm, a current coherence leaves at most a sign of delta. -/
theorem delta_sign_ambiguity (x y : Spinor)
    (hq : output x = output y) (hn : norm2 x = norm2 y) :
    delta x = delta y ∨ delta x = -delta y := by
  have hr : reQ x = reQ y := congrArg Prod.fst hq
  have hi : imQ x = imQ y := congrArg Prod.snd hq
  have hx := sphere_identity x
  have hy := sphere_identity y
  rw [hr, hi, hn] at hx
  have hmul : (delta x-delta y)*(delta x+delta y)=0 := by
    nlinarith [hx, hy]
  rcases mul_eq_zero.mp hmul with h | h
  · left; linarith
  · right; linarith

def brightBasis : Spinor := ⟨1,0,0,0⟩
def darkBasis : Spinor := ⟨0,0,1,0⟩

/-- Exact obstruction: this coherence closes for all states iff c*s=0. -/
theorem output_closes_iff (c s : ℝ) :
    (∃ f : Observation → Observation,
      ∀ x, output (mix c s x) = f (output x)) ↔ c*s=0 := by
  constructor
  · rintro ⟨f, hf⟩
    have he : output (mix c s brightBasis) = output (mix c s darkBasis) := by
      calc
        output (mix c s brightBasis) = f (output brightBasis) := hf _
        _ = f (output darkBasis) := by rfl
        _ = output (mix c s darkBasis) := (hf _).symm
    have hi : imQ (mix c s brightBasis) = imQ (mix c s darkBasis) :=
      congrArg Prod.snd he
    rw [imQ_mix, imQ_mix] at hi
    norm_num [imQ, delta, brightBasis, darkBasis] at hi
    linarith
  · intro h
    refine ⟨fun q => ((c^2+s^2)*q.1, (c^2-s^2)*q.2), ?_⟩
    intro x
    apply Prod.ext
    · exact reQ_mix c s x
    · change imQ (mix c s x) = (c^2-s^2)*imQ x
      rw [imQ_mix, h]
      ring

/-- A particular norm-preserving pulse with rational coefficients. -/
def step (_ : Unit) (x : Spinor) : Spinor := mix (3/5) (4/5) x
def summaryStep (_ : Unit) (q : Summary) : Summary := evolution (3/5) (4/5) q

theorem summary_step (u : Unit) (x : Spinor) :
    summary (step u x) = summaryStep u (summary x) :=
  summary_mix (3/5) (4/5) x

theorem project_summary (x : Spinor) : project (summary x) = output x := rfl

theorem step_preserves_norm2 (u : Unit) (x : Spinor) :
    norm2 (step u x) = norm2 x := by
  exact norm2_preserved (3/5) (4/5) (by norm_num) x

/-- A current observation and one following pulse reconstruct the hidden delta. -/
theorem one_probe_recovers_delta (x : Spinor) :
    delta x = (25*(output (step () x)).2+7*(output x).2)/12 := by
  change delta x = (25*imQ (mix (3/5) (4/5) x)+7*imQ x)/12
  rw [imQ_mix]
  ring

theorem summary_eq_of_two_reads (x y : Spinor)
    (h0 : output x = output y)
    (h1 : output (step () x) = output (step () y)) :
    summary x = summary y := by
  have hd : delta x = delta y := by
    rw [one_probe_recovers_delta x, one_probe_recovers_delta y, h0, h1]
  exact Prod.ext (congrArg Prod.fst h0) (Prod.ext (congrArg Prod.snd h0) hd)

theorem two_reads_iff_summary (x y : Spinor) :
    (output x = output y ∧ output (step () x) = output (step () y)) ↔
      summary x = summary y := by
  constructor
  · rintro ⟨h0,h1⟩
    exact summary_eq_of_two_reads x y h0 h1
  · intro h
    constructor
    · exact congrArg project h
    · have hs : summary (step () x) = summary (step () y) := by
        rw [summary_step, summary_step, h]
      exact congrArg project hs

def witnessLeft : Spinor := ⟨1,0,2,0⟩
def witnessRight : Spinor := ⟨2,0,1,0⟩

theorem current_collision :
    output witnessLeft = output witnessRight ∧
    norm2 witnessLeft = norm2 witnessRight := by
  norm_num [output, reQ, imQ, norm2, witnessLeft, witnessRight]

theorem next_values :
    output (step () witnessLeft) = (2, -36/25) ∧
    output (step () witnessRight) = (2, 36/25) := by
  norm_num [output, reQ, imQ, step, mix, witnessLeft, witnessRight]

theorem next_separates :
    output (step () witnessLeft) ≠ output (step () witnessRight) := by
  rw [next_values.1, next_values.2]
  norm_num

def commonPhase (p q : ℝ) (x : Spinor) : Spinor :=
  ⟨p*x.br-q*x.bi, q*x.br+p*x.bi,
   p*x.dr-q*x.di, q*x.dr+p*x.di⟩

theorem reQ_phase (p q : ℝ) (x : Spinor) :
    reQ (commonPhase p q x) = (p^2+q^2)*reQ x := by
  dsimp [reQ, commonPhase]
  ring

theorem imQ_phase (p q : ℝ) (x : Spinor) :
    imQ (commonPhase p q x) = (p^2+q^2)*imQ x := by
  dsimp [imQ, commonPhase]
  ring

theorem delta_phase (p q : ℝ) (x : Spinor) :
    delta (commonPhase p q x) = (p^2+q^2)*delta x := by
  dsimp [delta, commonPhase]
  ring

theorem common_phase_summary (p q : ℝ) (h : p^2+q^2=1) (x : Spinor) :
    summary (commonPhase p q x) = summary x := by
  apply Prod.ext
  · change reQ (commonPhase p q x) = reQ x
    rw [reQ_phase, h, one_mul]
  · apply Prod.ext
    · change imQ (commonPhase p q x) = imQ x
      rw [imQ_phase, h, one_mul]
    · change delta (commonPhase p q x) = delta x
      rw [delta_phase, h, one_mul]

end DarkBrightObservation
