/-!
Decode/re-observe connects complementary observations to F0 and Stops.

The retraction acts on observation pairs, not on the original state space.
Its fixed points are exactly compatible pairs. The singleton-closure statement
requires an incompatible pair: an onto encoder gives the identity retraction
and belongs to the separate universal-closure case.
-/

noncomputable section

namespace LinearInputObservationRetractionPolarity

open LinearInputStrangeGalois LinearInputStrangeFixedSets

universe u v

/-- Reconstruct a state and encode it again in the data space. -/
def retract {α : Type u} {β : Type v} (encode : α → β) (decode : β → α) : β → β :=
  fun y => encode (decode y)

/-- Exact state reconstruction induces an F0 idempotent on the data space. -/
theorem retract_idempotent {α : Type u} {β : Type v}
    (encode : α → β) (decode : β → α) (h : Function.LeftInverse decode encode) :
    LinearInputF0.Idempotent (retract encode decode) := by
  intro y
  exact congrArg encode (h (decode y))

/-- Re-encoding does not change the decoded state. -/
theorem decode_retract {α : Type u} {β : Type v}
    (encode : α → β) (decode : β → α) (h : Function.LeftInverse decode encode)
    (y : β) : decode (retract encode decode y) = decode y :=
  h (decode y)

/-- All realizable data and only those data are fixed by the retraction. -/
theorem retract_fixed_iff {α : Type u} {β : Type v}
    (encode : α → β) (decode : β → α) (h : Function.LeftInverse decode encode)
    (y : β) : retract encode decode y = y ↔ y ∈ Set.range encode := by
  constructor
  · intro hy
    exact ⟨decode y, hy⟩
  · rintro ⟨x, rfl⟩
    exact congrArg encode (h x)

theorem fixedStates_retract {α : Type u} {β : Type v}
    (encode : α → β) (decode : β → α) (h : Function.LeftInverse decode encode) :
    FixedStates (retract encode decode) = Set.range encode := by
  apply Set.ext
  intro y
  exact retract_fixed_iff encode decode h y

/-- The retraction identifies exactly the pairs with the same decoded state. -/
theorem retract_fiber_iff {α : Type u} {β : Type v}
    (encode : α → β) (decode : β → α) (h : Function.LeftInverse decode encode)
    (y z : β) : retract encode decode y = retract encode decode z ↔ decode y = decode z := by
  constructor
  · intro hyz
    have hd := congrArg decode hyz
    simpa only [decode_retract encode decode h] using hd
  · exact congrArg encode

/-- Stops detects the passage from unrealizable to realizable data. -/
theorem stops_retract_iff {α : Type u} {β : Type v}
    (encode : α → β) (decode : β → α) (h : Function.LeftInverse decode encode)
    (T : β → β) :
    Stops T (retract encode decode) ↔
      ∃ y : β, y ∉ Set.range encode ∧ T y ∈ Set.range encode := by
  constructor
  · rintro ⟨y, hy, hTy⟩
    exact ⟨y, fun hr => hy ((retract_fixed_iff encode decode h y).mpr hr),
      (retract_fixed_iff encode decode h (T y)).mp hTy⟩
  · rintro ⟨y, hy, hTy⟩
    exact ⟨y, fun hf => hy ((retract_fixed_iff encode decode h y).mp hf),
      (retract_fixed_iff encode decode h (T y)).mpr hTy⟩

/-- A single inconsistent datum makes the retraction nontrivial and self-stopping. -/
theorem retract_self_stops {α : Type u} {β : Type v}
    (encode : α → β) (decode : β → α) (h : Function.LeftInverse decode encode)
    (y : β) (hy : y ∉ Set.range encode) :
    Stops (retract encode decode) (retract encode decode) := by
  apply idempotent_self_stops _ (retract_idempotent encode decode h)
  exact ⟨y, fun hf => hy ((retract_fixed_iff encode decode h y).mp hf)⟩

/-- PR #26's fixed-set classification applies to any exact decoder, with
explicit witnesses that the compatible-data subset is nonempty and proper. -/
theorem close_retract_exact {α : Type u} {β : Type v}
    (encode : α → β) (decode : β → α) (h : Function.LeftInverse decode encode)
    (x : α) (y : β) (hy : y ∉ Set.range encode) :
    Close (Stops (α := β)) ({retract encode decode} : Set (β → β)) =
      {U | FixedStates U = Set.range encode} := by
  have hFixed : ∃ z : β, retract encode decode z = z :=
    ⟨encode x, congrArg encode (h x)⟩
  have hActive : ∃ z : β, retract encode decode z ≠ z :=
    ⟨y, fun hf => hy ((retract_fixed_iff encode decode h y).mp hf)⟩
  rw [close_singleton_exact_fixed_set _ hFixed hActive, fixedStates_retract encode decode h]

/-- An onto encoder gives the identity retraction, whose closure is universal. -/
theorem close_retract_of_surjective {α : Type u} {β : Type v}
    (encode : α → β) (decode : β → α) (h : Function.LeftInverse decode encode)
    (hOnto : Function.Surjective encode) :
    Close (Stops (α := β)) ({retract encode decode} : Set (β → β)) = Set.univ := by
  apply close_singleton_top_of_all_fixed
  intro y
  exact (retract_fixed_iff encode decode h y).mpr (hOnto y)

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [Field K]

/-- The concrete PR #25 decoder, now regarded as an observation-space F0 map. -/
def pairRetract (B C D : Matrix n n K) : ((n → K) × (n → K)) → (n → K) × (n → K) :=
  retract (LinearInputComplementaryPencilRecovery.observe B C)
    (LinearInputComplementaryPencilRecovery.decode D)

theorem pairRetract_idempotent (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1) :
    LinearInputF0.Idempotent (pairRetract B C D) :=
  retract_idempotent _ _
    (LinearInputComplementaryPencilRecovery.decode_leftInverse B C D h2 hDB)

theorem pairRetract_fixed_iff (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1) (y : (n → K) × (n → K)) :
    pairRetract B C D y = y ↔ LinearInputComplementaryPencilRecovery.Compatible B C y :=
  (LinearInputComplementaryPencilRecovery.compatible_iff_reconstruction B C D h2 hDB y).symm

omit [DecidableEq n] in
/-- Opposite data have zero average and hence retract to the zero pair. -/
theorem pairRetract_opposite (B C D : Matrix n n K) (w : n → K) :
    pairRetract B C D (w, -w) = (0, 0) := by
  simp [pairRetract, retract, LinearInputComplementaryPencilRecovery.decode,
    LinearInputComplementaryPencilRecovery.observe]

/-- A nonzero opposite pair witnesses that the compatible-data set is proper. -/
theorem opposite_compatible_iff (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1) (w : n → K) :
    LinearInputComplementaryPencilRecovery.Compatible B C (w, -w) ↔ w = 0 := by
  rw [← pairRetract_fixed_iff B C D h2 hDB (w, -w), pairRetract_opposite]
  constructor
  · intro he
    exact (congrArg Prod.fst he).symm
  · intro hw
    simp [hw]

theorem pairRetract_stops_iff (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1)
    (T : ((n → K) × (n → K)) → (n → K) × (n → K)) :
    Stops T (pairRetract B C D) ↔
      ∃ y, ¬ LinearInputComplementaryPencilRecovery.Compatible B C y ∧
        LinearInputComplementaryPencilRecovery.Compatible B C (T y) :=
  stops_retract_iff _ _
    (LinearInputComplementaryPencilRecovery.decode_leftInverse B C D h2 hDB) T

/-- The singleton polarity closure is determined precisely by compatible
observation pairs, not by any particular choice of decoder off that set. -/
theorem close_pairRetract_exact (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1)
    (y : (n → K) × (n → K))
    (hy : ¬ LinearInputComplementaryPencilRecovery.Compatible B C y) :
    Close (Stops (α := (n → K) × (n → K)))
        ({pairRetract B C D} : Set (((n → K) × (n → K)) → (n → K) × (n → K))) =
      {U | FixedStates U = {z | LinearInputComplementaryPencilRecovery.Compatible B C z}} :=
  close_retract_exact _ _
    (LinearInputComplementaryPencilRecovery.decode_leftInverse B C D h2 hDB) 0 y hy

/-- A nonzero state vector supplies the required incompatible-data witness. -/
theorem close_pairRetract_exact_of_nonzero (B C D : Matrix n n K)
    (h2 : (2 : K) ≠ 0) (hDB : D * B = 1) (w : n → K) (hw : w ≠ 0) :
    Close (Stops (α := (n → K) × (n → K)))
        ({pairRetract B C D} : Set (((n → K) × (n → K)) → (n → K) × (n → K))) =
      {U | FixedStates U = {z | LinearInputComplementaryPencilRecovery.Compatible B C z}} :=
  close_pairRetract_exact B C D h2 hDB (w, -w)
    (fun hy => hw ((opposite_compatible_iff B C D h2 hDB w).mp hy))

end LinearInputObservationRetractionPolarity
