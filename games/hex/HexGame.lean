import Std

/-!
# Hex Circuit

A dependency-free, playable Hex game written in Lean 4 itself.
Route a deterministic token through all six neighboring cells of the origin,
then return to the origin. The player edits each cell's outgoing direction.

Run: lean --run games/hex/HexGame.lean
Test: lean --trust=0 games/hex/HexGame.lean
      lean --run games/hex/HexGame.lean --self-test

This is a finite programmable-router puzzle, not an assertion that its
dynamics are an Abelian sandpile or a Laakso space.
-/

namespace HexCircuit

structure Hex where
  q : Int
  r : Int
  deriving Repr, BEq, DecidableEq

def origin : Hex := ⟨0, 0⟩

/-- The closed axial-coordinate hexagon of radius two, with 19 cells. -/
def inside (p : Hex) : Bool :=
  decide (p.q.natAbs ≤ 2 ∧ p.r.natAbs ≤ 2 ∧ (p.q + p.r).natAbs ≤ 2)

/-- 0: E, 1: NE, 2: NW, 3: W, 4: SW, 5: SE. -/
def direction : Nat → Hex
  | 0 => ⟨ 1,  0⟩
  | 1 => ⟨ 1, -1⟩
  | 2 => ⟨ 0, -1⟩
  | 3 => ⟨-1,  0⟩
  | 4 => ⟨-1,  1⟩
  | _ => ⟨ 0,  1⟩

def plus (a b : Hex) : Hex := ⟨a.q + b.q, a.r + b.r⟩

def candidate (p : Hex) (d : Nat) : Hex :=
  plus p (direction (d % 6))

/-- An invalid move becomes `none`; the token never moves off the board. -/
def checkedMove (p : Hex) (d : Nat) : Option Hex :=
  if inside (candidate p d) then some (candidate p d) else none

/-- A general safety guarantee, rather than only a finite example. -/
theorem checkedMove_inside (p target : Hex) (d : Nat)
    (h : checkedMove p d = some target) : inside target = true := by
  cases hin : inside (candidate p d) with
  | false =>
      simp [checkedMove, hin] at h
  | true =>
      have eq : candidate p d = target := by
        simpa [checkedMove, hin] using h
      subst target
      exact hin

/-- All board cells, ordered by rows. -/
def cells : List Hex :=
  (List.range 5).flatMap fun j =>
    (List.range 5).filterMap fun i =>
      let p : Hex := ⟨Int.ofNat i - 2, Int.ofNat j - 2⟩
      if inside p then some p else none

/-- The six target cells are the ring immediately around the origin. -/
def goals : List Hex :=
  [⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩,
   ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩]

def member (xs : List Hex) (p : Hex) : Bool :=
  xs.any (fun x => x == p)

def router (routes : List (Hex × Nat)) (p : Hex) : Nat :=
  match routes.find? (fun entry => entry.1 == p) with
  | some entry => entry.2
  | none => 0

def assign (routes : List (Hex × Nat)) (p : Hex) (d : Nat) : List (Hex × Nat) :=
  routes.map fun entry =>
    if entry.1 == p then (p, d % 6) else entry

structure Game where
  routes : List (Hex × Nat)
  position : Hex
  seen : List Hex
  moves : Nat
  lost : Bool
  won : Bool
  deriving Repr, DecidableEq

def initial : Game :=
  { routes := cells.map (fun p => (p, 0))
    position := origin
    seen := []
    moves := 0
    lost := false
    won := false }

/-- Editing outside the finite board is a no-op. -/
def edit (s : Game) (p : Hex) (d : Nat) : Game :=
  if inside p then { s with routes := assign s.routes p d } else s

theorem edit_outside (s : Game) (p : Hex) (d : Nat)
    (h : inside p = false) : edit s p d = s := by
  simp [edit, h]

def goalsDone (seen : List Hex) : Bool :=
  goals.all (member seen)

/-- One fully deterministic game tick, implemented in Lean. -/
def step (s : Game) : Game :=
  if s.lost || s.won then s
  else
    match checkedMove s.position (router s.routes s.position) with
    | none => { s with lost := true, moves := s.moves + 1 }
    | some next =>
        let seen := if member goals next && !(member s.seen next)
          then next :: s.seen else s.seen
        { s with
          position := next
          seen := seen
          moves := s.moves + 1
          won := (next == origin) && goalsDone seen }

/-- Run up to n ticks (finished games remain unchanged). -/
def simulate : Nat → Game → Game
  | 0, s => s
  | n + 1, s => simulate n (step s)

/-- A concrete seven-step winning circuit; no random input is needed. -/
def solution : Game :=
  let s0 := edit initial ⟨ 1,  0⟩ 2
  let s1 := edit s0      ⟨ 1, -1⟩ 3
  let s2 := edit s1      ⟨ 0, -1⟩ 4
  let s3 := edit s2      ⟨-1,  0⟩ 5
  let s4 := edit s3      ⟨-1,  1⟩ 0
  edit s4 ⟨0, 1⟩ 2

/- Kernel-checked concrete regression properties. -/
example : cells.length = 19 := by decide
example : goals.length = 6 := by decide
example : (simulate 6 solution).won = false := by decide
example : (simulate 7 solution).won = true := by decide
example : (simulate 7 solution).lost = false := by decide
example : (simulate 3 initial).lost = true := by decide
example : edit initial ⟨3, 0⟩ 5 = initial := by decide

#print axioms checkedMove_inside
#print axioms edit_outside

/-- The center is @, visited goal cells are *, and other digits are router directions. -/
def glyph (s : Game) (p : Hex) : String :=
  if s.position == p then "@"
  else if member s.seen p then "*"
  else toString (router s.routes p)

def render (s : Game) : String :=
  String.intercalate "\n" ((List.range 5).map fun j =>
    let r : Int := Int.ofNat j - 2
    let row := cells.filter (fun p => p.r == r)
    let indent := String.ofList (List.replicate r.natAbs ' ')
    indent ++ String.intercalate " " (row.map (glyph s)))

def summary (s : Game) : String :=
  let result := if s.won then "YOU WIN" else if s.lost then "CRASH" else "PLAYING"
  s!"moves={s.moves} goals={s.seen.length}/6 pos=({s.position.q},{s.position.r}) {result}"

def display (s : Game) : IO Unit := do
  IO.println (render s)
  IO.println (summary s)

def helpText : String := String.intercalate "\n"
  [ "HEX CIRCUIT — route a token through all 6 goals, then back to (0,0)."
  , "Directions: 0 E, 1 NE, 2 NW, 3 W, 4 SW, 5 SE"
  , "Board: axial coordinates (q,r), |q|, |r|, |q+r| <= 2."
  , "@ = token; * = visited goal; 0-5 = outgoing router."
  , "Commands:"
  , "  set q r d  : write direction 0..5 on a cell"
  , "  turn q r   : rotate a cell's direction by one"
  , "  step       : move token once"
  , "  run n      : move at most n times (n <= 100)"
  , "  show       : print current board"
  , "  reset      : restart with all routers pointing east"
  , "  demo       : load a known solution and play it"
  , "  help       : print this text"
  , "  quit       : exit"
  ]

def command (s : Game) : List String → IO (Option Game)
  | ["quit"] => pure none
  | ["help"] => do
      IO.println helpText
      pure (some s)
  | ["show"] => do
      display s
      pure (some s)
  | ["reset"] => do
      display initial
      pure (some initial)
  | ["demo"] => do
      let next := simulate 7 solution
      display next
      pure (some next)
  | ["step"] => do
      let next := step s
      display next
      pure (some next)
  | ["run", n] => do
      match n.toNat? with
      | some k =>
          if k <= 100 then
            let next := simulate k s
            display next
            pure (some next)
          else
            IO.println "Run limit is 100."
            pure (some s)
      | none =>
          IO.println "Usage: run n"
          pure (some s)
  | ["set", q, r, d] => do
      match q.toInt?, r.toInt?, d.toNat? with
      | some qi, some ri, some di =>
          let p : Hex := ⟨qi, ri⟩
          if !(inside p) then
            IO.println "That cell is outside the radius-two board."
            pure (some s)
          else if di >= 6 then
            IO.println "Direction must be 0..5."
            pure (some s)
          else
            let next := edit s p di
            display next
            pure (some next)
      | _, _, _ =>
          IO.println "Usage: set q r direction"
          pure (some s)
  | ["turn", q, r] => do
      match q.toInt?, r.toInt? with
      | some qi, some ri =>
          let p : Hex := ⟨qi, ri⟩
          if inside p then
            let next := edit s p (router s.routes p + 1)
            display next
            pure (some next)
          else
            IO.println "That cell is outside the radius-two board."
            pure (some s)
      | _, _ =>
          IO.println "Usage: turn q r"
          pure (some s)
  | _ => do
      IO.println "Unknown command. Type help."
      pure (some s)

partial def repl (s : Game) : IO Unit := do
  IO.print "> "
  let line ← (← IO.getStdin).getLine
  if line.isEmpty then return
  let words := (line.trimAscii.toString.splitOn " ").filter (fun w => !w.isEmpty)
  let next ← command s words
  match next with
  | none => pure ()
  | some s' => repl s'

def selfTest : IO Unit := do
  if cells.length != 19 then throw (IO.userError "wrong board size")
  if (simulate 6 solution).won then throw (IO.userError "premature victory")
  if !(simulate 7 solution).won then throw (IO.userError "solution did not win")
  if (simulate 7 solution).lost then throw (IO.userError "solution crashed")
  if !(simulate 3 initial).lost then throw (IO.userError "unrouted token did not crash")
  IO.println "HEX_GAME_SELF_TEST_OK"

end HexCircuit

def main (args : List String) : IO Unit := do
  match args with
  | ["--self-test"] => HexCircuit.selfTest
  | _ =>
      IO.println HexCircuit.helpText
      HexCircuit.display HexCircuit.initial
      HexCircuit.repl HexCircuit.initial
