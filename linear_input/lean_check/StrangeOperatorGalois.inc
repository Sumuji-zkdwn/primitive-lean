/-!
Strange-operator polarity derived from the existing F0 forgetting model.

"Stops T S" means that S changes some state x, but becomes inactive
after the chosen operation T. This is an explicit proposed definition,
not an existing physical characterization of strange matter.

The Galois connection and closure are relational facts. The genuine
connection with primitive-lean consists of the F0 idempotent witness
and the separate fiber-obstruction witness below.
-/

namespace LinearInputStrangeGalois

universe u v

/-- T suppresses a previously active S at some state. -/
def Stops {α : Type u} (T S : α → α) : Prop :=
  ∃ x : α, S x ≠ x ∧ S (T x) = T x

/-- An idempotent F0 map stops itself whenever it is not the identity. -/
theorem idempotent_self_stops {α : Type u} (K : α → α)
    (hK : LinearInputF0.Idempotent K)
    (hNontrivial : ∃ x, K x ≠ x) : Stops K K := by
  obtain ⟨x, hx⟩ := hNontrivial
  exact ⟨x, hx, hK x⟩

/-- The identity update cannot suppress an active operation. -/
theorem identity_does_not_stop {α : Type u} (S : α → α) :
    ¬ Stops (fun x : α => x) S := by
  rintro ⟨x, hx, he⟩
  exact hx he

/-- This is a distinct sort of strangeness: a forgotten difference reappears. -/
def BreaksFiber {α : Type u} (K T : α → α) : Prop :=
  ∃ x y : α, K x = K y ∧ K (T x) ≠ K (T y)

/-- Previously proved F0 commuting maps preserve observational fibers. -/
theorem commuting_does_not_break {α : Type u} {K : α → α}
    (T : LinearInputF0.CommutingMap K) : ¬ BreaksFiber K T.val := by
  rintro ⟨x, y, hxy, hne⟩
  apply hne
  calc
    K (T.val x) = T.val (K x) := (T.property x).symm
    _ = T.val (K y) := congrArg T.val hxy
    _ = K (T.val y) := T.property y

/-- The concrete Fin 3 retraction from F0Retractions.inc is nontrivial. -/
theorem exampleK_nontrivial :
    ∃ x : Fin 3, LinearInputF0.exampleK x ≠ x := by
  refine ⟨1, ?_⟩
  decide

theorem exampleK_self_stops :
    Stops LinearInputF0.exampleK LinearInputF0.exampleK := by
  exact idempotent_self_stops LinearInputF0.exampleK
    LinearInputF0.exampleK_idempotent exampleK_nontrivial

/-- Reuses the actual F0 Fin 3 example of a non-compatible update. -/
theorem exampleBadS_breaks :
    BreaksFiber LinearInputF0.exampleK
      (fun x : Fin 3 => LinearInputF0.exampleBadS x 0) := by
  refine ⟨0, 1, ?_, ?_⟩ <;> decide

/-- Self-stopping does not imply reappearance of a forgotten distinction. -/
theorem exampleK_does_not_break :
    ¬ BreaksFiber LinearInputF0.exampleK LinearInputF0.exampleK := by
  apply commuting_does_not_break
  exact (⟨LinearInputF0.exampleK, by intro x; rfl⟩ :
    LinearInputF0.CommutingMap LinearInputF0.exampleK)

/-- Operators on the left that act strangely on *every* element on the right. -/
def LeftPolar {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (A : Set κ) : Set ι :=
  {t | ∀ s ∈ A, R t s}

/-- Operators on the right affected by *every* element on the left. -/
def RightPolar {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (B : Set ι) : Set κ :=
  {s | ∀ t ∈ B, R t s}

/-- The two antitone maps form a (polarity) Galois connection. -/
theorem polar_galois {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (A : Set κ) (B : Set ι) :
    B ⊆ LeftPolar R A ↔ A ⊆ RightPolar R B := by
  constructor
  · intro h s hs t ht
    exact h ht s hs
  · intro h t ht s hs
    exact h hs t ht

theorem left_antitone {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) {A B : Set κ} (hAB : A ⊆ B) :
    LeftPolar R B ⊆ LeftPolar R A := by
  intro t ht s hs
  exact ht s (hAB hs)

theorem right_antitone {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) {B C : Set ι} (hBC : B ⊆ C) :
    RightPolar R C ⊆ RightPolar R B := by
  intro s hs t ht
  exact hs t (hBC ht)

/-- Unlike squaring one polar of a directed relation, this is always a closure. -/
def Close {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (A : Set κ) : Set κ :=
  RightPolar R (LeftPolar R A)

theorem close_extensive {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (A : Set κ) :
    A ⊆ Close R A := by
  intro s hs t ht
  exact ht s hs

theorem close_monotone {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) {A B : Set κ} (hAB : A ⊆ B) :
    Close R A ⊆ Close R B := by
  intro s hs t ht
  apply hs t
  intro a ha
  exact ht a (hAB ha)

theorem left_polar_close {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (A : Set κ) :
    LeftPolar R (Close R A) = LeftPolar R A := by
  apply Set.ext
  intro t
  constructor
  · intro ht s hs
    exact ht s (close_extensive R A hs)
  · intro ht s hs
    exact hs t ht

theorem close_idempotent {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (A : Set κ) :
    Close R (Close R A) = Close R A := by
  change RightPolar R (LeftPolar R (Close R A)) =
    RightPolar R (LeftPolar R A)
  rw [left_polar_close R A]

/-- This explicitly constructs fixed points, without invoking an extra axiom. -/
theorem close_fixed_exists {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) :
    ∃ A : Set κ, Close R A = A := by
  exact ⟨Close R ∅, close_idempotent R ∅⟩

/-- Every closed right-polar/left-polar pair is mutually stable. -/
theorem stable_pair {ι : Type u} {κ : Type v}
    (R : ι → κ → Prop) (A : Set κ) :
    RightPolar R (LeftPolar R (Close R A)) = Close R A ∧
      LeftPolar R (Close R A) = LeftPolar R A := by
  exact ⟨close_idempotent R A, left_polar_close R A⟩

/-- Applying a single (possibly directed) polar twice is merely monotone. -/
theorem left_polar_twice_monotone {ι : Type u}
    (R : ι → ι → Prop) {A B : Set ι} (hAB : A ⊆ B) :
    LeftPolar R (LeftPolar R A) ⊆ LeftPolar R (LeftPolar R B) := by
  intro t ht s hs
  exact ht s (left_antitone R hAB hs)

/-- Instantiate the general fixed-point construction with the F0-derived Stops relation. -/
theorem strange_family_fixed_exists {α : Type u} :
    ∃ A : Set (α → α), Close (Stops (α := α)) A = A := by
  exact close_fixed_exists (Stops (α := α))

end LinearInputStrangeGalois
