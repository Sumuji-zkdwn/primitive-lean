/-!
Exact finite word witnesses for the two circular-arc auxiliary model.

Coordinates are in units xi = 2 h / (3 pi), bending costs in units
c0 = pi^2 / (8 h), and turns in units pi / 2.  True denotes A and false B.
The turn coordinate is a natural number, not its residue modulo four.
The last coordinate is the integer cross term D in twice the signed area;
for words with the same letter counts the intrinsic arc-area sum is equal.
This is the discrete word model.  The arc-integral identification, smooth
gluing, and the third iterated integral are not assumed as Lean theorems here.
-/

namespace LinearInputCurveWordFinite

abbrev Point := ℤ × ℤ

abbrev State := Point × ℕ × ℕ × ℤ

/-- Rotate a lattice point using the residue of a lifted quarter-turn count. -/
def rotate (p : Point) (turn : ℕ) : Point :=
  match turn % 4 with
  | 0 => p
  | 1 => (-p.2, p.1)
  | 2 => (-p.1, -p.2)
  | _ => (p.2, -p.1)

def step (s : State) (a : Bool) : State :=
  let d := rotate (if a then (3, 3) else (-1, 1)) s.2.1
  ((s.1.1 + d.1, s.1.2 + d.2),
   s.2.1 + (if a then 1 else 3),
   s.2.2.1 + (if a then 1 else 9),
   s.2.2.2 + s.1.1 * d.2 - s.1.2 * d.1)

def state (w : List Bool) : State := w.foldl step ((0, 0), 0, 0, 0)

def firstState (w : List Bool) : Point × ℕ × ℕ :=
  let s := state w
  (s.1, s.2.1, s.2.2.1)

def crossArea (w : List Bool) : ℤ := (state w).2.2.2

theorem ab_state : state [true, false] = ((2, 2), 4, 10, 0) := by decide

theorem ba_state : state [false, true] = ((2, -2), 4, 10, 0) := by decide

theorem ab_ba_same_cost_turn :
    (state [true, false]).2.1 = (state [false, true]).2.1 ∧
    (state [true, false]).2.2.1 = (state [false, true]).2.2.1 := by decide

theorem ab_ba_distinct_endpoint :
    (state [true, false]).1 ≠ (state [false, true]).1 := by decide

theorem ab_ba_same_x :
    (state [true, false]).1.1 = (state [false, true]).1.1 := by decide

theorem prefix_A_separates_x :
    (state [true, true, false]).1.1 ≠ (state [true, false, true]).1.1 := by decide

theorem six_letter_first_collision :
    firstState [true, true, false, false, false, true] =
    firstState [false, true, true, true, false, false] := by decide

theorem six_letter_area_values :
    crossArea [true, true, false, false, false, true] = 8 ∧
    crossArea [false, true, true, true, false, false] = 24 := by decide

theorem six_letter_area_separates :
    crossArea [true, true, false, false, false, true] ≠
    crossArea [false, true, true, true, false, false] := by decide

theorem eight_letter_area_collision :
    state [true, true, true, true, false, false, false, false] =
    state [true, true, true, false, false, false, false, true] := by decide

theorem eight_letter_state_value :
    state [true, true, true, true, false, false, false, false] =
      ((0, 0), 16, 40, 32) := by decide

/-- Every Boolean word of a prescribed length, with no restriction on counts. -/
def allWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allWords n).flatMap (fun w => [true :: w, false :: w])

theorem mem_allWords (w : List Bool) (n : ℕ) :
    w ∈ allWords n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [allWords]
  | succ n ih =>
    cases w with
    | nil => simp [allWords]
    | cons a w =>
      cases a <;> simp [allWords, List.mem_flatMap, ih]

/-- Words with n copies of each letter. -/
def balancedWords (n : ℕ) : List (List Bool) :=
  (allWords (2 * n)).filter (fun w => w.count true == n)

theorem mem_balancedWords (w : List Bool) (n : ℕ) :
    w ∈ balancedWords n ↔ w.length = 2 * n ∧ w.count true = n := by
  simp [balancedWords, mem_allWords]

def endpointCount (n : ℕ) : ℕ :=
  ((balancedWords n).map (fun w => (state w).1)).eraseDups.length

def areaStateCount (n : ℕ) : ℕ :=
  ((balancedWords n).map state).eraseDups.length

set_option maxRecDepth 200000 in
theorem three_three_word_count : (balancedWords 3).length = 20 := by decide

set_option maxRecDepth 200000 in
theorem three_three_distinct_word_count : (balancedWords 3).toFinset.card = 20 := by decide

set_option maxRecDepth 200000 in
theorem three_three_endpoint_count : endpointCount 3 = 12 := by decide

set_option maxRecDepth 200000 in
theorem three_three_area_state_count : areaStateCount 3 = 20 := by decide

set_option maxRecDepth 200000 in
theorem three_three_endpoint_set :
    ((balancedWords 3).map (fun w => (state w).1)).toFinset =
      {(-2, -6), (-2, -2), (-2, 2), (-2, 6),
       (2, -6), (2, -2), (2, 2), (2, 6),
       (6, -6), (6, -2), (6, 2), (6, 6)} := by decide

set_option maxRecDepth 200000 in
theorem three_three_lifted_data :
    ∀ w ∈ balancedWords 3, (state w).2.1 = 12 ∧ (state w).2.2.1 = 30 := by decide

set_option maxRecDepth 200000 in
theorem four_four_word_count : (balancedWords 4).length = 70 := by decide

set_option maxRecDepth 200000 in
theorem four_four_distinct_word_count : (balancedWords 4).toFinset.card = 70 := by decide

set_option maxRecDepth 200000 in
theorem four_four_endpoint_count : endpointCount 4 = 20 := by decide

set_option maxRecDepth 200000 in
theorem four_four_area_state_count : areaStateCount 4 = 50 := by decide

end LinearInputCurveWordFinite
