/-!
# Exact four-channel observability for the original F16 relative action

This supplement identifies the checker matrix A^T C from the retained F16
left-multiplication matrices.  It proves the four-phase decoder for every
real 16-state and gives an explicit state hidden by the first three phases.
The proof uses the signed-permutation action of the original matrices; it
assumes no block decomposition into local models.
-/

noncomputable section
namespace LinearInputF16RimRecovery

abbrev State := Fin 16 -> Real
abbrev Channel := Fin 4

def f16Partner (i : Fin 16) : Fin 16 :=
  LinearInputF16Holonomy.rightIndex (9 : Fin 16) i

/-- A computational table for xor-9, used only to normalize finite indices. -/
def f16PartnerCode (i : Fin 16) : Fin 16 :=
  if i.val = 0 then 9 else if i.val = 1 then 8 else
  if i.val = 2 then 11 else if i.val = 3 then 10 else
  if i.val = 4 then 13 else if i.val = 5 then 12 else
  if i.val = 6 then 15 else if i.val = 7 then 14 else
  if i.val = 8 then 1 else if i.val = 9 then 0 else
  if i.val = 10 then 3 else if i.val = 11 then 2 else
  if i.val = 12 then 5 else if i.val = 13 then 4 else
  if i.val = 14 then 7 else 6

theorem f16Partner_eq_code (i : Fin 16) :
    f16Partner i = f16PartnerCode i := by
  fin_cases i <;> decide

def f16Sign (i : Fin 16) : Int :=
  LinearInputF16Holonomy.eps (3 : Fin 16) (f16Partner i) *
    LinearInputF16Holonomy.eps (10 : Fin 16) i

def f16SignR (i : Fin 16) : Real := (f16Sign i : Real)

def f16Base : Matrix (Fin 16) (Fin 16) Real :=
  LinearInputF16ConstructiveRecovery.baseMatrix

def f16Slope : Matrix (Fin 16) (Fin 16) Real :=
  LinearInputF16ConstructiveRecovery.slopeMatrix

/-- The actual relative matrix from the finite checker: U = Aᵀ C,
    where A is the retained L₃ matrix and C is the retained L₁₀ matrix. -/
def f16RelativeMatrix : Matrix (Fin 16) (Fin 16) Real :=
  f16Base.transpose * f16Slope

/-- A single signed left-basis multiplication matrix. -/
def f16BasisMatrix (a : Fin 16) : Matrix (Fin 16) (Fin 16) Real :=
  fun row col =>
    if LinearInputF16Holonomy.rightIndex a col = row then
      (LinearInputF16Holonomy.eps a col : Real)
    else 0

/-- Coordinate action induced by U = L₃ᵀ L₁₀. -/
def f16Step (v : State) : State :=
  fun i => f16SignR (f16Partner i) * v (f16Partner i)

theorem f16RightIndex_involutive (a i : Fin 16) :
    LinearInputF16Holonomy.rightIndex a
      (LinearInputF16Holonomy.rightIndex a i) = i := by
  fin_cases a <;> fin_cases i <;> decide

theorem f16Partner_involutive (i : Fin 16) :
    f16Partner (f16Partner i) = i := by
  simpa [f16Partner] using
    f16RightIndex_involutive (9 : Fin 16) i

theorem f16RightIndex_ten_three (i : Fin 16) :
    LinearInputF16Holonomy.rightIndex (10 : Fin 16)
      (LinearInputF16Holonomy.rightIndex (3 : Fin 16) i) =
        f16Partner i := by
  fin_cases i <;> decide

/-- A row of a signed permutation has exactly one nonzero entry. -/
theorem f16Basis_mulVec (a : Fin 16) (v : State) (i : Fin 16) :
    (f16BasisMatrix a).mulVec v i =
      (LinearInputF16Holonomy.eps a
        (LinearInputF16Holonomy.rightIndex a i) : Real) *
        v (LinearInputF16Holonomy.rightIndex a i) := by
  classical
  change (∑ j : Fin 16, f16BasisMatrix a i j * v j) = _
  rw [Finset.sum_eq_single (LinearInputF16Holonomy.rightIndex a i)]
  · simp [f16BasisMatrix, f16RightIndex_involutive]
  · intro j _ hne
    have hzero :
        LinearInputF16Holonomy.rightIndex a j ≠ i := by
      intro h
      apply hne
      calc
        j = LinearInputF16Holonomy.rightIndex a
              (LinearInputF16Holonomy.rightIndex a j) :=
                (f16RightIndex_involutive a j).symm
        _ = LinearInputF16Holonomy.rightIndex a i := by rw [h]
    simp [f16BasisMatrix, hzero]
  · simp

/-- The transpose sends a coordinate to its signed partner coordinate. -/
theorem f16Basis_transpose_mulVec (a : Fin 16) (v : State) (i : Fin 16) :
    (f16BasisMatrix a).transpose.mulVec v i =
      (LinearInputF16Holonomy.eps a i : Real) *
        v (LinearInputF16Holonomy.rightIndex a i) := by
  classical
  change (∑ j : Fin 16, f16BasisMatrix a j i * v j) = _
  rw [Finset.sum_eq_single (LinearInputF16Holonomy.rightIndex a i)]
  · simp [f16BasisMatrix]
  · intro j _ hne
    have hzero :
        LinearInputF16Holonomy.rightIndex a i ≠ j := by
      intro h
      exact hne h.symm
    simp [f16BasisMatrix, hzero]
  · simp

theorem f16Base_eq_three :
    f16Base = f16BasisMatrix (3 : Fin 16) := by
  ext i j
  simp [f16Base, f16BasisMatrix,
    LinearInputF16ConstructiveRecovery.baseMatrix,
    LinearInputF16Determinant.realPencilAll,
    LinearInputF16Determinant.entryThree]

theorem f16Slope_eq_ten :
    f16Slope = f16BasisMatrix (10 : Fin 16) := by
  ext i j
  simp [f16Slope, f16BasisMatrix,
    LinearInputF16ConstructiveRecovery.slopeMatrix,
    LinearInputF16Determinant.entryTen]

/-- The checker matrix AᵀC acts as the signed xor-9 permutation built
    from the original F16 sign table. -/
theorem f16_relative_action (v : State) :
    f16RelativeMatrix.mulVec v = f16Step v := by
  change (f16Base.transpose * f16Slope).mulVec v = f16Step v
  rw [← Matrix.mulVec_mulVec, f16Base_eq_three, f16Slope_eq_ten]
  funext i
  rw [f16Basis_transpose_mulVec, f16Basis_mulVec]
  simp only [f16RightIndex_ten_three, f16Step, f16SignR, f16Sign,
    f16Partner_involutive, Int.cast_mul]
  all_goals ring

def f16ChannelLow (i : Channel) : Fin 16 :=
  ⟨i.val, by omega⟩

def f16ChannelHigh (i : Channel) : Fin 16 :=
  ⟨i.val + 4, by omega⟩

def f16ChannelOf (i : Fin 16) : Channel :=
  ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

/-- The four scalar output rows, matching the checker’s observation matrix O. -/
def f16Observe (v : State) : Channel -> Real :=
  fun i =>
    (f16SignR (f16ChannelHigh i) *
        v (f16Partner (f16ChannelHigh i)) -
      f16SignR (f16ChannelLow i) *
        v (f16Partner (f16ChannelLow i))) / 2

/-- Row zero of the scalar matrix O in the rational checker. -/
theorem f16Observe_checker_row0 (v : State) :
    f16Observe v 0 = (v 9 - v 13) / 2 := by
  norm_num [f16Observe, f16ChannelLow, f16ChannelHigh,
    f16Partner_eq_code, f16PartnerCode, f16SignR, f16Sign,
    LinearInputF16Holonomy.eps, LinearInputF16Holonomy.epsTable]
  ring

/-- Row one of the scalar matrix O in the rational checker. -/
theorem f16Observe_checker_row1 (v : State) :
    f16Observe v 1 = (v 12 - v 8) / 2 := by
  norm_num [f16Observe, f16ChannelLow, f16ChannelHigh,
    f16Partner_eq_code, f16PartnerCode, f16SignR, f16Sign,
    LinearInputF16Holonomy.eps, LinearInputF16Holonomy.epsTable]

/-- Row two of the scalar matrix O in the rational checker. -/
theorem f16Observe_checker_row2 (v : State) :
    f16Observe v 2 = (v 11 + v 15) / 2 := by
  norm_num [f16Observe, f16ChannelLow, f16ChannelHigh,
    f16Partner_eq_code, f16PartnerCode, f16SignR, f16Sign,
    LinearInputF16Holonomy.eps, LinearInputF16Holonomy.epsTable]
  ring

/-- Row three of the scalar matrix O in the rational checker. -/
theorem f16Observe_checker_row3 (v : State) :
    f16Observe v 3 = (v 10 - v 14) / 2 := by
  norm_num [f16Observe, f16ChannelLow, f16ChannelHigh,
    f16Partner_eq_code, f16PartnerCode, f16SignR, f16Sign,
    LinearInputF16Holonomy.eps, LinearInputF16Holonomy.epsTable]
  ring

/-- The exact four-row output formula from the checker. -/
def f16ObserveChecker (v : State) (ch : Channel) : Real :=
  if ch.val = 0 then (v 9 - v 13) / 2
  else if ch.val = 1 then (v 12 - v 8) / 2
  else if ch.val = 2 then (v 11 + v 15) / 2
  else (v 10 - v 14) / 2

theorem f16Observe_eq_checker (v : State) (ch : Channel) :
    f16Observe v ch = f16ObserveChecker v ch := by
  fin_cases ch
  · simp [f16ObserveChecker, f16Observe_checker_row0]
  · simp [f16ObserveChecker, f16Observe_checker_row1]
  · simp [f16ObserveChecker, f16Observe_checker_row2]
  · simp [f16ObserveChecker, f16Observe_checker_row3]

theorem f16Sign_self_mul_int (i : Fin 16) :
    f16Sign i * f16Sign i = 1 := by
  fin_cases i <;>
    norm_num [f16Sign, f16Partner_eq_code, f16PartnerCode,
      LinearInputF16Holonomy.eps, LinearInputF16Holonomy.epsTable]

theorem f16Sign_partner_low_int (ch : Channel) :
    f16Sign (f16Partner (f16ChannelLow ch)) =
      -f16Sign (f16ChannelLow ch) := by
  fin_cases ch <;>
    norm_num [f16Sign, f16Partner_eq_code, f16PartnerCode,
      f16ChannelLow, LinearInputF16Holonomy.eps,
      LinearInputF16Holonomy.epsTable]

theorem f16Sign_partner_high_int (ch : Channel) :
    f16Sign (f16Partner (f16ChannelHigh ch)) =
      f16Sign (f16ChannelHigh ch) := by
  fin_cases ch <;>
    norm_num [f16Sign, f16Partner_eq_code, f16PartnerCode,
      f16ChannelHigh, LinearInputF16Holonomy.eps,
      LinearInputF16Holonomy.epsTable]

theorem f16SignR_self_mul (i : Fin 16) :
    f16SignR i * f16SignR i = 1 := by
  change (f16Sign i : Real) * (f16Sign i : Real) = 1
  exact_mod_cast f16Sign_self_mul_int i

theorem f16SignR_cancel_self (i : Fin 16) (x : Real) :
    f16SignR i * (f16SignR i * x) = x := by
  calc
    f16SignR i * (f16SignR i * x) =
        (f16SignR i * f16SignR i) * x := by ring
    _ = x := by rw [f16SignR_self_mul]; ring

theorem f16SignR_cancel_left (i j : Fin 16) (x : Real) :
    f16SignR i * (f16SignR i * f16SignR j * x) =
      f16SignR j * x := by
  calc
    f16SignR i * (f16SignR i * f16SignR j * x) =
        (f16SignR i * f16SignR i) * f16SignR j * x := by ring
    _ = f16SignR j * x := by rw [f16SignR_self_mul]; ring

theorem f16SignR_cancel_right (i j : Fin 16) (x : Real) :
    f16SignR i * (f16SignR j * f16SignR i * x) =
      f16SignR j * x := by
  calc
    f16SignR i * (f16SignR j * f16SignR i * x) =
        (f16SignR i * f16SignR i) * f16SignR j * x := by ring
    _ = f16SignR j * x := by rw [f16SignR_self_mul]; ring

theorem f16SignR_partner_low (i : Channel) :
    f16SignR (f16Partner (f16ChannelLow i)) =
      -f16SignR (f16ChannelLow i) := by
  change (f16Sign (f16Partner (f16ChannelLow i)) : Real) =
    -(f16Sign (f16ChannelLow i) : Real)
  exact_mod_cast f16Sign_partner_low_int i

theorem f16SignR_partner_high (i : Channel) :
    f16SignR (f16Partner (f16ChannelHigh i)) =
      f16SignR (f16ChannelHigh i) := by
  change (f16Sign (f16Partner (f16ChannelHigh i)) : Real) =
    (f16Sign (f16ChannelHigh i) : Real)
  exact_mod_cast f16Sign_partner_high_int i

/-- One observed phase after one application of U. -/
@[simp] theorem f16Observe_step (v : State) (ch : Channel) :
    f16Observe (f16Step v) ch =
      (v (f16ChannelHigh ch) - v (f16ChannelLow ch)) / 2 := by
  simp only [f16Observe, f16Step, f16Partner_involutive]
  rw [f16SignR_cancel_self, f16SignR_cancel_self]

theorem f16Step_twice (v : State) (i : Fin 16) :
    f16Step (f16Step v) i =
      f16SignR (f16Partner i) * f16SignR i * v i := by
  simp [f16Step, f16Partner_involutive]
  all_goals ring

theorem f16Step_twice_at_partner (v : State) (i : Fin 16) :
    f16Step (f16Step v) (f16Partner i) =
      f16SignR i * f16SignR (f16Partner i) *
        v (f16Partner i) := by
  simpa [f16Partner_involutive] using
    f16Step_twice v (f16Partner i)

@[simp] theorem f16Observe_step2 (v : State) (ch : Channel) :
    f16Observe (f16Step (f16Step v)) ch =
      (f16SignR (f16ChannelHigh ch) *
          v (f16Partner (f16ChannelHigh ch)) +
        f16SignR (f16ChannelLow ch) *
          v (f16Partner (f16ChannelLow ch))) / 2 := by
  unfold f16Observe
  rw [f16Step_twice_at_partner, f16Step_twice_at_partner]
  rw [f16SignR_cancel_left, f16SignR_cancel_left]
  rw [f16SignR_partner_high, f16SignR_partner_low]
  all_goals ring

theorem f16Step_thrice_at_partner (v : State) (i : Fin 16) :
    f16Step (f16Step (f16Step v)) (f16Partner i) =
      f16SignR (f16Partner i) * v i := by
  calc
    f16Step (f16Step (f16Step v)) (f16Partner i) =
        f16SignR i *
          (f16SignR (f16Partner i) * f16SignR i * v i) := by
      simp only [f16Step, f16Partner_involutive]
      ring
    _ = f16SignR (f16Partner i) * v i :=
      f16SignR_cancel_right i (f16Partner i) (v i)

theorem f16SignR_cancel_partner_low (ch : Channel) (x : Real) :
    f16SignR (f16ChannelLow ch) *
      (f16SignR (f16Partner (f16ChannelLow ch)) * x) = -x := by
  rw [f16SignR_partner_low]
  calc
    f16SignR (f16ChannelLow ch) *
        (-f16SignR (f16ChannelLow ch) * x) =
        -(f16SignR (f16ChannelLow ch) *
          (f16SignR (f16ChannelLow ch) * x)) := by ring
    _ = -x := by rw [f16SignR_cancel_self]

theorem f16SignR_cancel_partner_high (ch : Channel) (x : Real) :
    f16SignR (f16ChannelHigh ch) *
      (f16SignR (f16Partner (f16ChannelHigh ch)) * x) = x := by
  rw [f16SignR_partner_high]
  exact f16SignR_cancel_self (f16ChannelHigh ch) x

@[simp] theorem f16Observe_step3 (v : State) (ch : Channel) :
    f16Observe (f16Step (f16Step (f16Step v))) ch =
      (v (f16ChannelHigh ch) + v (f16ChannelLow ch)) / 2 := by
  unfold f16Observe
  rw [f16Step_thrice_at_partner, f16Step_thrice_at_partner]
  rw [f16SignR_cancel_partner_high, f16SignR_cancel_partner_low]
  all_goals ring

def f16OrbitState (v : State) (phase : Fin 4) : State :=
  if phase.val = 0 then v
  else if phase.val = 1 then f16Step v
  else if phase.val = 2 then f16Step (f16Step v)
  else f16Step (f16Step (f16Step v))

/-- The four outputs O, OU, OU², OU³ for each state. -/
def f16Trace4 (v : State) : Fin 4 -> Channel -> Real :=
  fun phase => f16Observe (f16OrbitState v phase)

@[simp] theorem f16Trace4_phase0 (v : State) (ch : Channel) :
    f16Trace4 v 0 ch = f16Observe v ch := by
  simp [f16Trace4, f16OrbitState]

@[simp] theorem f16Trace4_phase1 (v : State) (ch : Channel) :
    f16Trace4 v 1 ch = f16Observe (f16Step v) ch := by
  simp [f16Trace4, f16OrbitState]

@[simp] theorem f16Trace4_phase2 (v : State) (ch : Channel) :
    f16Trace4 v 2 ch =
      f16Observe (f16Step (f16Step v)) ch := by
  simp [f16Trace4, f16OrbitState]

@[simp] theorem f16Trace4_phase3 (v : State) (ch : Channel) :
    f16Trace4 v 3 ch =
      f16Observe (f16Step (f16Step (f16Step v))) ch := by
  simp [f16Trace4, f16OrbitState]

/-- Closed form for the first matrix-observation phase. -/
@[simp] theorem f16Trace4_value1 (v : State) (ch : Channel) :
    f16Trace4 v 1 ch =
      (v (f16ChannelHigh ch) - v (f16ChannelLow ch)) / 2 := by
  rw [f16Trace4_phase1, f16Observe_step]

/-- Closed form for the second matrix-observation phase. -/
@[simp] theorem f16Trace4_value2 (v : State) (ch : Channel) :
    f16Trace4 v 2 ch =
      (f16SignR (f16ChannelHigh ch) *
          v (f16Partner (f16ChannelHigh ch)) +
        f16SignR (f16ChannelLow ch) *
          v (f16Partner (f16ChannelLow ch))) / 2 := by
  rw [f16Trace4_phase2, f16Observe_step2]

/-- Closed form for the third matrix-observation phase. -/
@[simp] theorem f16Trace4_value3 (v : State) (ch : Channel) :
    f16Trace4 v 3 ch =
      (v (f16ChannelHigh ch) + v (f16ChannelLow ch)) / 2 := by
  rw [f16Trace4_phase3, f16Observe_step3]

/-- The same four phases, written with the actual matrix U = Aᵀ C. -/
def f16MatrixOrbitState (v : State) (phase : Fin 4) : State :=
  if phase.val = 0 then v
  else if phase.val = 1 then f16RelativeMatrix.mulVec v
  else if phase.val = 2 then
    f16RelativeMatrix.mulVec (f16RelativeMatrix.mulVec v)
  else
    f16RelativeMatrix.mulVec
      (f16RelativeMatrix.mulVec (f16RelativeMatrix.mulVec v))

def f16MatrixTrace4 (v : State) : Fin 4 -> Channel -> Real :=
  fun phase => f16Observe (f16MatrixOrbitState v phase)

/-- The signed-permutation reduction identifies every actual matrix phase. -/
theorem f16MatrixOrbitState_eq_f16OrbitState (v : State) (phase : Fin 4) :
    f16MatrixOrbitState v phase = f16OrbitState v phase := by
  fin_cases phase <;>
    simp [f16MatrixOrbitState, f16OrbitState, f16_relative_action]

theorem f16MatrixTrace4_eq_f16Trace4 (v : State) :
    f16MatrixTrace4 v = f16Trace4 v := by
  funext phase ch
  change f16Observe (f16MatrixOrbitState v phase) ch =
    f16Observe (f16OrbitState v phase) ch
  rw [f16MatrixOrbitState_eq_f16OrbitState]

/-- Explicit coordinate decoder matching the finite rational certificate. -/
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

/-- The four-phase decoder reconstructs all sixteen real coordinates. -/
theorem f16_decode_four_trace (v : State) :
    f16Decode (f16Trace4 v) = v := by
  funext j
  fin_cases j <;>
    simp only [f16Decode, f16ChannelOf, f16Partner_eq_code,
      f16PartnerCode, f16Trace4_phase0, f16Trace4_value1,
      f16Trace4_value2, f16Trace4_value3,
      f16Observe_eq_checker, f16ObserveChecker] <;>
    norm_num [f16ChannelLow, f16ChannelHigh, f16Partner_eq_code,
      f16PartnerCode, f16SignR, f16Sign,
      LinearInputF16Holonomy.eps, LinearInputF16Holonomy.epsTable] <;>
    field_simp <;>
    first
    | ring
    | (apply congrArg (fun x : Real => x * 2)
       apply congrArg v
       apply Fin.ext
       rfl)

/-- The same decoder identity for four successive applications of U itself. -/
theorem f16_decode_original_matrix_trace (v : State) :
    f16Decode (f16MatrixTrace4 v) = v := by
  rw [f16MatrixTrace4_eq_f16Trace4]
  exact f16_decode_four_trace v

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

/-- The witness is zero on all coordinates seen by the zeroth observation. -/
theorem f16ThreePhaseWitness_partner_low_zero (ch : Channel) :
    f16ThreePhaseWitness (f16Partner (f16ChannelLow ch)) = 0 := by
  fin_cases ch <;>
    norm_num [f16ThreePhaseWitness, f16Partner_eq_code, f16PartnerCode,
      f16ChannelLow]

/-- The witness is also zero on all partner coordinates from the high channel. -/
theorem f16ThreePhaseWitness_partner_high_zero (ch : Channel) :
    f16ThreePhaseWitness (f16Partner (f16ChannelHigh ch)) = 0 := by
  fin_cases ch <;>
    norm_num [f16ThreePhaseWitness, f16Partner_eq_code, f16PartnerCode,
      f16ChannelHigh]

/-- The witness has equal low/high coordinates in each direct channel pair. -/
theorem f16ThreePhaseWitness_channel_pair (ch : Channel) :
    f16ThreePhaseWitness (f16ChannelHigh ch) =
      f16ThreePhaseWitness (f16ChannelLow ch) := by
  fin_cases ch <;> rfl

def f16Trace3 (v : State) :
    ((Channel -> Real) × (Channel -> Real)) × (Channel -> Real) :=
  ((f16Observe v, f16Observe (f16Step v)),
    f16Observe (f16Step (f16Step v)))

@[simp] theorem f16Observe_zero (ch : Channel) :
    f16Observe f16Zero ch = 0 := by
  simp [f16Observe, f16Zero]

@[simp] theorem f16Observe_step_zero (ch : Channel) :
    f16Observe (f16Step f16Zero) ch = 0 := by
  rw [f16Observe_step]
  simp [f16Zero]

@[simp] theorem f16Observe_step2_zero (ch : Channel) :
    f16Observe (f16Step (f16Step f16Zero)) ch = 0 := by
  rw [f16Observe_step2]
  simp [f16Zero]

@[simp] theorem f16Observe_threeWitness_zero (ch : Channel) :
    f16Observe f16ThreePhaseWitness ch = 0 := by
  unfold f16Observe
  rw [f16ThreePhaseWitness_partner_high_zero,
      f16ThreePhaseWitness_partner_low_zero]
  ring

@[simp] theorem f16Observe_step_threeWitness_zero (ch : Channel) :
    f16Observe (f16Step f16ThreePhaseWitness) ch = 0 := by
  rw [f16Observe_step]
  have hpair := f16ThreePhaseWitness_channel_pair ch
  rw [hpair]
  ring

@[simp] theorem f16Observe_step2_threeWitness_zero (ch : Channel) :
    f16Observe (f16Step (f16Step f16ThreePhaseWitness)) ch = 0 := by
  rw [f16Observe_step2, f16ThreePhaseWitness_partner_high_zero,
      f16ThreePhaseWitness_partner_low_zero]
  ring

theorem f16_three_phase_collision :
    f16Trace3 f16Zero = f16Trace3 f16ThreePhaseWitness := by
  apply Prod.ext
  · apply Prod.ext
    · funext ch
      simp only [f16Trace3, f16Observe_zero,
        f16Observe_threeWitness_zero]
    · funext ch
      simp only [f16Trace3, f16Observe_step_zero,
        f16Observe_step_threeWitness_zero]
  · funext ch
    simp only [f16Trace3, f16Observe_step2_zero,
      f16Observe_step2_threeWitness_zero]

theorem f16_zero_ne_three_phase_witness :
    f16Zero ≠ f16ThreePhaseWitness := by
  intro h
  have h0 := congrFun h (0 : Fin 16)
  norm_num [f16Zero, f16ThreePhaseWitness] at h0

theorem f16_three_phase_not_injective :
    ¬ Function.Injective f16Trace3 := by
  intro h
  exact f16_zero_ne_three_phase_witness (h f16_three_phase_collision)

def f16Trace2 (v : State) : (Channel -> Real) × (Channel -> Real) :=
  Prod.fst (f16Trace3 v)

def f16Trace1 (v : State) : Channel -> Real :=
  Prod.fst (f16Trace2 v)

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
