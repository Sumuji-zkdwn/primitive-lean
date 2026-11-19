/-!
Scalar sampling of the integer circular-arc model. Reading times are known:
one absolute reading after every complete block of three letters. The initial
state, including its position and direction, is known.
-/

namespace LinearInputCurveWordSampling

open LinearInputCurveWordFinite

abbrev Block := Bool × Bool × Bool

def letters (b : Block) : List Bool := [b.1, b.2.1, b.2.2]

def shadow (s : State) : ℤ := s.1.1 + 3 * s.1.2

def advance (s : State) (b : Block) : State := (letters b).foldl step s

/-- The absolute observations obtained along a word divided into triples. -/
def readings (s : State) : List Block → List ℤ
  | [] => []
  | b :: bs => let t := advance s b; shadow t :: readings t bs

/-- Each new sample is taken at the endpoint of the actual concatenated word. -/
theorem readings_append_block (s : State) (bs : List Block) (b : Block) :
    readings s (bs ++ [b]) = readings s bs ++
      [shadow (((bs ++ [b]).flatMap letters).foldl step s)] := by
  induction bs generalizing s with
  | nil => simp [readings, advance]
  | cons c cs ih =>
    simp only [List.cons_append, readings, List.flatMap_cons, List.foldl_append]
    exact congrArg (List.cons (shadow (advance s c))) (ih (advance s c))

private def heading (s : State) : Fin 4 :=
  ⟨s.2.1 % 4, Nat.mod_lt _ (by decide)⟩

private def reference (k : Fin 4) : State := ((0, 0), k.val, 0, 0)

/-- Parallel initial headings give identical displacements for the same word. -/
private theorem parallel_run (w : List Bool) (s t : State)
    (h : s.2.1 % 4 = t.2.1 % 4) :
    (w.foldl step s).1.1 - s.1.1 = (w.foldl step t).1.1 - t.1.1 ∧
    (w.foldl step s).1.2 - s.1.2 = (w.foldl step t).1.2 - t.1.2 := by
  induction w generalizing s t with
  | nil => simp
  | cons a w ih =>
    let p : Point := if a then (3, 3) else (-1, 1)
    have hr : rotate p s.2.1 = rotate p t.2.1 := by unfold rotate; rw [h]
    have ht : (step s a).2.1 % 4 = (step t a).2.1 % 4 := by
      change (s.2.1 + _) % 4 = (t.2.1 + _) % 4
      rw [Nat.add_mod s.2.1, Nat.add_mod t.2.1, h]
    obtain ⟨hx, hy⟩ := ih (step s a) (step t a) ht
    change _ - (s.1.1 + (rotate p s.2.1).1) = _ - (t.1.1 + (rotate p t.2.1).1) at hx
    change _ - (s.1.2 + (rotate p s.2.1).2) = _ - (t.1.2 + (rotate p t.2.1).2) at hy
    rw [hr] at hx hy
    simp only [List.foldl_cons]
    constructor <;> omega

private def delta (k : Fin 4) (b : Block) : ℤ :=
  shadow (advance (reference k) b)

private theorem shadow_delta (s : State) (b : Block) :
    shadow (advance s b) - shadow s = delta (heading s) b := by
  have h : s.2.1 % 4 = (reference (heading s)).2.1 % 4 := by
    simp [reference, heading]
  obtain ⟨hx, hy⟩ := parallel_run (letters b) s (reference (heading s)) h
  change (advance s b).1.1 - s.1.1 = (advance (reference (heading s)) b).1.1 - 0 at hx
  change (advance s b).1.2 - s.1.2 = (advance (reference (heading s)) b).1.2 - 0 at hy
  unfold delta shadow
  omega

private def blocks : List Block :=
  [false, true].flatMap fun a =>
    [false, true].flatMap fun b =>
      [false, true].map fun c => (a, b, c)

private def lookup (k : Fin 4) (d : ℤ) : Option Block :=
  blocks.find? fun b => delta k b == d

/-- All four headings and all eight blocks, checked by kernel reduction. -/
private theorem lookup_delta :
    ∀ (k : Fin 4) (a b c : Bool),
      lookup k (delta k (a, b, c)) = some (a, b, c) := by decide

/-- Reconstruct the blocks from absolute readings. Impossible readings fail. -/
def decode (s : State) : List ℤ → Option (List Block)
  | [] => some []
  | z :: zs => do
    let b ← lookup (heading s) (z - shadow s)
    let bs ← decode (advance s b) zs
    pure (b :: bs)

/-- Round trip for every number of blocks and every known initial state. -/
theorem decode_readings (s : State) (bs : List Block) :
    decode s (readings s bs) = some bs := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨a, b, c⟩ := b
    simp [readings, decode, shadow_delta, lookup_delta, ih]

theorem readings_injective (s : State) {u v : List Block}
    (h : readings s u = readings s v) : u = v := by
  have he := congrArg (decode s) h
  simpa only [decode_readings, Option.some.injEq] using he

/-- Four letters can hide a balanced exchange even when the lifted turn and
bending cost are recorded. The chord cross terms retain its order. -/
theorem four_letter_exchange :
    [true, false, false, true] ≠ [false, true, true, false] ∧
    state [true, false, false, true] = ((4, 0), 8, 20, -8) ∧
    state [false, true, true, false] = ((4, 0), 8, 20, 8) := by decide

private theorem fold_same_pose (w : List Bool) (s t : State)
    (hp : s.1 = t.1) (hq : s.2.1 = t.2.1) :
    (w.foldl step s).1 = (w.foldl step t).1 ∧
    (w.foldl step s).2.1 = (w.foldl step t).2.1 := by
  induction w generalizing s t with
  | nil => exact ⟨hp, hq⟩
  | cons a w ih =>
    change (w.foldl step (step s a)).1 = (w.foldl step (step t a)).1 ∧
      (w.foldl step (step s a)).2.1 = (w.foldl step (step t a)).2.1
    exact ih (step s a) (step t a) (by simp only [step, hp, hq])
      (by simp only [step, hq])

/-- The hidden exchange cannot be recovered from any later position or turn,
even if every subsequent letter boundary is observed. -/
theorem four_letter_exchange_continuation (w : List Bool) :
    (state ([true, false, false, true] ++ w)).1 =
      (state ([false, true, true, false] ++ w)).1 ∧
    (state ([true, false, false, true] ++ w)).2.1 =
      (state ([false, true, true, false] ++ w)).2.1 := by
  change (w.foldl step (state [true, false, false, true])).1 =
    (w.foldl step (state [false, true, true, false])).1 ∧
    (w.foldl step (state [true, false, false, true])).2.1 =
    (w.foldl step (state [false, true, true, false])).2.1
  exact fold_same_pose w _ _ (by decide) (by decide)

end LinearInputCurveWordSampling
