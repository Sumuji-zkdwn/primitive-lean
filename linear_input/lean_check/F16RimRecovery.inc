/-!
# Exact four-channel observability for the original F16 relative action

This supplement works from the retained F16 epsilon table and the existing
16-dimensional matrices.  It identifies the checker matrix A^TC directly,
proves A^TA = I, and proves a decoder identity for every real 16-state.
A separate explicit collision shows that one, two, or three phases do not
suffice.  No block-conjugacy assumption is used.
-/

noncomputable section
namespace LinearInputF16RimRecovery

abbrev State := Fin 16 -> Real
abbrev Channel := Fin 4

def f16Partner (i : Fin 16) : Fin 16 :=
  LinearInputF16Holonomy.rightIndex (9 : Fin 16) i

def f16Sign (i : Fin 16) : Int :=
  LinearInputF16Holonomy.eps (3 : Fin 16) (f16Partner i) *
    LinearInputF16Holonomy.eps (10 : Fin 16) i

def f16SignR (i : Fin 16) : Real := (f16Sign i : Real)

def f16Base : Matrix (Fin 16) (Fin 16) Real :=
  LinearInputF16ConstructiveRecovery.baseMatrix

def f16Slope : Matrix (Fin 16) (Fin 16) Real :=
  LinearInputF16ConstructiveRecovery.slopeMatrix

/-- This is the exact relative matrix constructed by the finite checker:
    U = A^T C, with A = L3 and C = L10. -/
def f16RelativeMatrix : Matrix (Fin 16) (Fin 16) Real :=
  f16Base.transpose * f16Slope

/-- Signed permutation form of the same relative matrix. -/
def f16ShiftMatrix : Matrix (Fin 16) (Fin 16) Real :=
  fun row col => if row = f16Partner col then f16SignR col else 0

/-- Coordinate action of U on states, obtained from its signed-permutation
    matrix. -/
def f16Step (v : State) : State :=
  fun i => f16SignR (f16Partner i) * v (f16Partner i)

theorem f16_base_transpose_left_inverse :
    f16Base.transpose * f16Base = (1 : Matrix (Fin 16) (Fin 16) Real) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [f16Base,
      LinearInputF16ConstructiveRecovery.baseMatrix,
      LinearInputF16Determinant.realPencilAll,
      LinearInputF16Determinant.entryThree,
      LinearInputF16Holonomy.rightIndex,
      LinearInputF16Holonomy.eps,
      LinearInputF16Holonomy.epsTable,
      Matrix.mul_apply, Matrix.transpose_apply]

/-- The retained F16 definitions reduce the checker’s A^TC to a signed
    index-xor-9 permutation. -/
theorem f16_relative_matrix_eq_shift :
    f16RelativeMatrix = f16ShiftMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [f16RelativeMatrix, f16ShiftMatrix, f16SignR, f16Sign,
      f16Partner, f16Base, f16Slope,
      LinearInputF16ConstructiveRecovery.baseMatrix,
      LinearInputF16ConstructiveRecovery.slopeMatrix,
      LinearInputF16Determinant.realPencilAll,
      LinearInputF16Determinant.entryThree,
      LinearInputF16Determinant.entryTen,
      LinearInputF16Holonomy.rightIndex,
      LinearInputF16Holonomy.eps,
      LinearInputF16Holonomy.epsTable,
      Matrix.mul_apply, Matrix.transpose_apply]

theorem f16_shift_mulVec (v : State) :
    f16ShiftMatrix.mulVec v = f16Step v := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, f16ShiftMatrix, f16Step, f16SignR,
      f16Sign, f16Partner,
      LinearInputF16Holonomy.rightIndex,
      LinearInputF16Holonomy.eps,
      LinearInputF16Holonomy.epsTable]

theorem f16_relative_action (v : State) :
    f16RelativeMatrix.mulVec v = f16Step v := by
  rw [f16_relative_matrix_eq_shift]
  exact f16_shift_mulVec v

def f16ChannelLow (i : Channel) : Fin 16 :=
  ⟨i.val, by omega⟩

def f16ChannelHigh (i : Channel) : Fin 16 :=
  ⟨i.val + 4, by omega⟩

def f16ChannelOf (i : Fin 16) : Channel :=
  ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

/-- The four scalar outputs are precisely the four rows of the checker’s
    4×16 observation matrix O. -/
def f16Observe (v : State) : Channel -> Real :=
  fun i =>
    (f16SignR (f16ChannelHigh i) *
        v (f16Partner (f16ChannelHigh i)) -
      f16SignR (f16ChannelLow i) *
        v (f16Partner (f16ChannelLow i))) / 2

def f16OrbitState (v : State) (phase : Fin 4) : State :=
  if phase.val = 0 then v
  else if phase.val = 1 then f16Step v
  else if phase.val = 2 then f16Step (f16Step v)
  else f16Step (f16Step (f16Step v))

/-- Rows O, OU, OU², OU³, represented as four time phases by four channels. -/
def f16Trace4 (v : State) : Fin 4 -> Channel -> Real :=
  fun phase => f16Observe (f16OrbitState v phase)

/-- Decoder matching the explicit rational certificate, applied to every
    coordinate (the index xor 9 pairs the low and high halves). -/
def f16Decode (y : Fin 4 -> Channel -> Real) (j : Fin 16) : Real :=
  if j.val < 4 then
    y 3 (f16ChannelOf j) - y 1 (f16ChannelOf j)
  else if j.val < 8 then
    y 3 (f16ChannelOf j) + y 1 (f16ChannelOf j)
  else if j.val < 12 then
    f16SignR (f16Partner j) *
      (y 2 (f16ChannelOf (f16Partner j)) -
        y 0 (f16ChannelOf (f16Partner j)))
  else
    f16SignR (f16Partner j) *
      (y 2 (f16ChannelOf (f16Partner j)) +
        y 0 (f16ChannelOf (f16Partner j)))

/-- The four-phase decoder recovers all sixteen real coordinates. -/
theorem f16_decode_four_trace (v : State) :
    f16Decode (f16Trace4 v) = v := by
  funext j
  fin_cases j <;>
    norm_num [f16Decode, f16Trace4, f16OrbitState, f16Observe, f16Step,
      f16SignR, f16Sign, f16Partner, f16ChannelLow, f16ChannelHigh,
      f16ChannelOf,
      LinearInputF16Holonomy.rightIndex,
      LinearInputF16Holonomy.eps,
      LinearInputF16Holonomy.epsTable] <;> ring

theorem f16_four_phase_injective : Function.Injective f16Trace4 := by
  intro v w h
  calc
    v = f16Decode (f16Trace4 v) := (f16_decode_four_trace v).symm
    _ = f16Decode (f16Trace4 w) := congrArg f16Decode h
    _ = w := f16_decode_four_trace w

def f16Zero : State := fun _ => 0

/-- A concrete nonzero state hidden by the first three phases. -/
def f16ThreePhaseWitness : State :=
  fun i => if i.val = 0 ∨ i.val = 4 then 1 else 0

def f16Trace3 (v : State) :
    ((Channel -> Real) × (Channel -> Real)) × (Channel -> Real) :=
  ((f16Observe v, f16Observe (f16Step v)),
    f16Observe (f16Step (f16Step v)))

def f16Trace2 (v : State) : (Channel -> Real) × (Channel -> Real) :=
  Prod.fst (f16Trace3 v)

def f16Trace1 (v : State) : Channel -> Real :=
  Prod.fst (f16Trace2 v)

theorem f16_three_phase_collision :
    f16Trace3 f16Zero = f16Trace3 f16ThreePhaseWitness := by
  apply Prod.ext
  · apply Prod.ext
    · funext ch
      fin_cases ch <;>
        norm_num [f16Trace3, f16Observe, f16Step, f16SignR, f16Sign,
          f16Partner, f16ChannelLow, f16ChannelHigh, f16Zero,
          f16ThreePhaseWitness,
          LinearInputF16Holonomy.rightIndex,
          LinearInputF16Holonomy.eps,
          LinearInputF16Holonomy.epsTable]
    · funext ch
      fin_cases ch <;>
        norm_num [f16Trace3, f16Observe, f16Step, f16SignR, f16Sign,
          f16Partner, f16ChannelLow, f16ChannelHigh, f16Zero,
          f16ThreePhaseWitness,
          LinearInputF16Holonomy.rightIndex,
          LinearInputF16Holonomy.eps,
          LinearInputF16Holonomy.epsTable]
  · funext ch
    fin_cases ch <;>
      norm_num [f16Trace3, f16Observe, f16Step, f16SignR, f16Sign,
        f16Partner, f16ChannelLow, f16ChannelHigh, f16Zero,
        f16ThreePhaseWitness,
        LinearInputF16Holonomy.rightIndex,
        LinearInputF16Holonomy.eps,
        LinearInputF16Holonomy.epsTable]

theorem f16_zero_ne_three_phase_witness :
    f16Zero ≠ f16ThreePhaseWitness := by
  intro h
  have h0 := congrFun h (0 : Fin 16)
  norm_num [f16Zero, f16ThreePhaseWitness] at h0

theorem f16_three_phase_not_injective :
    ¬ Function.Injective f16Trace3 := by
  intro h
  exact f16_zero_ne_three_phase_witness (h f16_three_phase_collision)

theorem f16_two_phase_collision :
    f16Trace2 f16Zero = f16Trace2 f16ThreePhaseWitness := by
  exact congrArg Prod.fst f16_three_phase_collision

theorem f16_two_phase_not_injective :
    ¬ Function.Injective f16Trace2 := by
  intro h
  exact f16_zero_ne_three_phase_witness (h f16_two_phase_collision)

theorem f16_one_phase_collision :
    f16Trace1 f16Zero = f16Trace1 f16ThreePhaseWitness := by
  exact congrArg (fun t => Prod.fst (Prod.fst t)) f16_three_phase_collision

theorem f16_one_phase_not_injective :
    ¬ Function.Injective f16Trace1 := by
  intro h
  exact f16_zero_ne_three_phase_witness (h f16_one_phase_collision)

end LinearInputF16RimRecovery
