import Research.SiphonPolynomialE
import OrbitTrace

/-!
# Position observations of two existing polynomial maps

The observer always reads the first coordinate. Changing the available operations
changes the predictive equivalence. The half turn can undo a time step even
though no word built from it and the time step can reveal the sign of I.
-/

namespace OperationalWorldGeneration

open Elastica.SiphonPolynomialE

abbrev State := ℝ × ℝ

def signature (z : State) : ℝ × ℝ := (z.1, I z ^ 2)

/-- Flip the signed invariant without changing the position. -/
def mirror (z : State) : State := (z.1, -I z - z.1 ^ 3)

theorem mirror_invariant (z : State) : I (mirror z) = -I z := by
  dsimp [I, mirror]
  ring

theorem mirror_involutive (z : State) : mirror (mirror z) = z := by
  apply Prod.ext
  · rfl
  · change -I (mirror z) - z.1 ^ 3 = z.2
    rw [mirror_invariant]
    dsimp [I]
    ring

theorem mirror_commutes (z : State) : E (mirror z) = mirror (E z) := by
  apply Prod.ext
  · change z.1 + I (mirror z) ^ 2 = z.1 + I z ^ 2
    rw [mirror_invariant, neg_sq]
  · change I (mirror z) - (z.1 + I (mirror z) ^ 2) ^ 3 =
        -I (E z) - (z.1 + I z ^ 2) ^ 3
    rw [mirror_invariant, I_E, neg_sq]

theorem position_iterate (n : ℕ) (z : State) :
    (iterate n z).1 = z.1 + (n : ℝ) * I z ^ 2 := by
  rw [iterate_eq_closedOrbit]
  rfl

private theorem signature_of_two_reads {z t : State}
    (h₀ : z.1 = t.1) (h₁ : (E z).1 = (E t).1) : signature z = signature t := by
  change z.1 + I z ^ 2 = t.1 + I t ^ 2 at h₁
  exact Prod.ext h₀ (add_left_cancel (h₀ ▸ h₁))

theorem passive_iff_signature (z t : State) :
    (∀ n, (iterate n z).1 = (iterate n t).1) ↔ signature z = signature t := by
  constructor
  · intro h
    exact signature_of_two_reads (h 0) (h 1)
  · intro h n
    have hx : z.1 = t.1 := congrArg Prod.fst h
    have hr : I z ^ 2 = I t ^ 2 := congrArg Prod.snd h
    rw [position_iterate, position_iterate, hx, hr]

theorem signature_eq_iff_mirror (z t : State) :
    signature z = signature t ↔ t = z ∨ t = mirror z := by
  constructor
  · intro h
    have hx : t.1 = z.1 := (congrArg Prod.fst h).symm
    have hs : I t ^ 2 = I z ^ 2 := (congrArg Prod.snd h).symm
    have hfac : (I t - I z) * (I t + I z) = 0 := by nlinarith only [hs]
    rcases mul_eq_zero.mp hfac with hp | hn
    · left
      apply Prod.ext hx
      dsimp [I] at hp
      rw [hx] at hp
      linarith
    · right
      apply Prod.ext hx
      dsimp [mirror, I] at hn ⊢
      rw [hx] at hn
      linarith
  · rintro (rfl | rfl)
    · rfl
    · apply Prod.ext
      · rfl
      · change I z ^ 2 = I (mirror z) ^ 2
        rw [mirror_invariant, neg_sq]

theorem signature_range (u s : ℝ) :
    (∃ z, signature z = (u, s)) ↔ 0 ≤ s := by
  constructor
  · rintro ⟨z, hz⟩
    have hs : I z ^ 2 = s := congrArg Prod.snd hz
    rw [← hs]
    exact sq_nonneg _
  · intro hs
    refine ⟨(u, Real.sqrt s - u ^ 3), Prod.ext rfl ?_⟩
    change (Real.sqrt s - u ^ 3 + u ^ 3) ^ 2 = s
    rw [sub_add_cancel, Real.sq_sqrt hs]

theorem recover_elapsed (n : ℕ) (z : State) (hr : I z ≠ 0) :
    ((iterate n z).1 - z.1) / I z ^ 2 = (n : ℝ) := by
  rw [position_iterate]
  apply (div_eq_iff (pow_ne_zero 2 hr)).2
  ring

/-- Elapsed time computed solely from the initial, one-step and final positions. -/
theorem recover_elapsed_from_reads (n : ℕ) (z : State) (hmoved : (E z).1 ≠ z.1) :
    ((iterate n z).1 - z.1) / ((E z).1 - z.1) = (n : ℝ) := by
  have hr : I z ≠ 0 := by
    intro h
    apply hmoved
    change z.1 + I z ^ 2 = z.1
    simp [h]
  change ((iterate n z).1 - z.1) / ((z.1 + I z ^ 2) - z.1) = (n : ℝ)
  simpa using recover_elapsed n z hr

theorem zero_fibre_fixed (n : ℕ) (z : State) (hr : I z = 0) :
    iterate n z = z := by
  rw [iterate_eq_closedOrbit]
  apply Prod.ext
  · change z.1 + (n : ℝ) * I z ^ 2 = z.1
    simp [hr]
  · change I z - (z.1 + (n : ℝ) * I z ^ 2) ^ 3 = z.2
    simp only [hr, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_sub]
    dsimp [I] at hr
    linarith

/-- The cube of the existing order-six linear map. -/
def halfTurn (z : State) : State := OrbitTrace.linearE (OrbitTrace.linearE (OrbitTrace.linearE z))

theorem halfTurn_reverses_step (z : State) : halfTurn (E (halfTurn z)) = invE z := by
  simp only [halfTurn, OrbitTrace.linearE_cube]
  apply Prod.ext <;> dsimp [E, I, invE] <;> ring

inductive Move where
  | advance | turn

def run (turn : State → State) (z : State) : List Move → State
  | [] => z
  | .advance :: w => run turn (E z) w
  | .turn :: w => run turn (turn z) w

theorem run_append (turn : State → State) (z : State) (v w : List Move) :
    run turn z (v ++ w) = run turn (run turn z v) w := by
  induction v generalizing z with
  | nil => rfl
  | cons a v ih => cases a <;> apply ih

theorem run_advances (turn : State → State) (z : State) (n : ℕ) :
    run turn z (List.replicate n .advance) = iterate n z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ', run_append, ih]; rfl

/-- Equality of position after every finite continuation, including the empty word. -/
def WordEq (turn : State → State) (z t : State) : Prop :=
  ∀ w, (run turn z w).1 = (run turn t w).1

private theorem signature_advance (z : State) :
    signature (E z) = ((signature z).1 + (signature z).2, (signature z).2) := by
  apply Prod.ext
  · rfl
  · change I (E z) ^ 2 = I z ^ 2
    rw [I_E]

private theorem signature_halfTurn (z : State) :
    signature (halfTurn z) = (-(signature z).1, (signature z).2) := by
  rw [halfTurn, OrbitTrace.linearE_cube]
  apply Prod.ext
  · rfl
  · dsimp [signature, I]
    ring

theorem halfTurn_wordEq_iff (z t : State) :
    WordEq halfTurn z t ↔ signature z = signature t := by
  constructor
  · intro h
    exact signature_of_two_reads (h []) (h [.advance])
  · intro h w
    induction w generalizing z t with
    | nil => exact congrArg Prod.fst h
    | cons a w ih =>
      cases a with
      | advance =>
        apply ih (z := E z) (t := E t)
        rw [signature_advance, signature_advance, h]
      | turn =>
        apply ih (z := halfTurn z) (t := halfTurn t)
        rw [signature_halfTurn, signature_halfTurn, h]

/-- Two position readings on the same run give the original pair of coordinates. -/
theorem two_reads_recover (z : State) : (z.1, (OrbitTrace.linearE z).1) = z := rfl

theorem linear_wordEq_iff (z t : State) :
    WordEq OrbitTrace.linearE z t ↔ z = t := by
  constructor
  · intro h
    exact Prod.ext (h []) (h [.turn])
  · rintro rfl w
    rfl

theorem mirror_separated_after_one_turn (z : State) (hr : I z ≠ 0) :
    WordEq halfTurn z (mirror z) ∧
      z.1 = (mirror z).1 ∧ (OrbitTrace.linearE z).1 ≠ (OrbitTrace.linearE (mirror z)).1 := by
  refine ⟨(halfTurn_wordEq_iff _ _).2 ((signature_eq_iff_mirror _ _).2 (Or.inr rfl)), rfl, ?_⟩
  intro heq
  have hstate : z = mirror z := Prod.ext rfl heq
  have hneg : I z = -I z := (congrArg I hstate).trans (mirror_invariant z)
  exact hr (by linarith)

/-- Every forward word preserves the integer lattice inside the real plane. -/
theorem integer_word (w : List Move) (a b : ℤ) :
    ∃ c d : ℤ, run OrbitTrace.linearE ((a : ℝ), (b : ℝ)) w = ((c : ℝ), (d : ℝ)) := by
  induction w generalizing a b with
  | nil => exact ⟨a, b, rfl⟩
  | cons move w ih =>
    cases move with
    | advance =>
      let r := b + a ^ 3
      let x := a + r ^ 2
      simpa [run, E, I, x, r] using ih x (r - x ^ 3)
    | turn =>
      simpa [run, OrbitTrace.linearE] using ih b (b - a)

/-- Every integer-starting orbit misses the same nonempty Euclidean-open strip. -/
theorem integer_word_open_strip (a b : ℤ) :
    ∃ U : Set State, IsOpen U ∧ U.Nonempty ∧
      ∀ w : List Move, run OrbitTrace.linearE ((a : ℝ), (b : ℝ)) w ∉ U := by
  refine ⟨Prod.fst ⁻¹' Set.Ioo (0 : ℝ) 1, isOpen_Ioo.preimage continuous_fst,
    ⟨((1 / 2 : ℝ), (0 : ℝ)), ?_⟩, ?_⟩
  · change 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1
    norm_num
  · intro w
    obtain ⟨c, d, h⟩ := integer_word w a b
    rw [h]
    change ¬ (0 < (c : ℝ) ∧ (c : ℝ) < 1)
    rintro ⟨h₀, h₁⟩
    have h₀' : (0 : ℤ) < c := by exact_mod_cast h₀
    have h₁' : c < (1 : ℤ) := by exact_mod_cast h₁
    omega

end OperationalWorldGeneration
